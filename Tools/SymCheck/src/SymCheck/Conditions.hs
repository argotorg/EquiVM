{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}

module SymCheck.Conditions
  ( CompareOp(..)
  , StopPredicate(..)
  , SmtMode(..)
  , OverapproxMode(..)
  , BufferRef(..)
  , CallField(..)
  , WordTerm(..)
  , Condition(..)
  , PostconditionStatus(..)
  , PostconditionReport(..)
  , conditionToPreProp
  , checkPostconditionsWithSolvers
  ) where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT)
import Control.Monad.ST (stToIO)
import Data.Map qualified as Map
import Data.Text qualified as T
import EVM.Expr qualified as Expr
import EVM.Effects qualified as Effects
import EVM.Format qualified as Format
import EVM.Solvers qualified as Solvers
import EVM.SymExec qualified as SymExec
import EVM.Types
import SymCheck.Midpoint
import SymCheck.Smt

data CompareOp
  = CmpEq
  | CmpNe
  | CmpLt
  | CmpLe
  | CmpGt
  | CmpGe
  deriving (Eq, Show)

data StopPredicate
  = StopSuccess
  | StopFailure
  | StopPartial
  | StopTarget
  | StopFuel
  deriving (Eq, Show)

data SmtMode
  = SmtExact
  | SmtWeakened
  deriving (Eq, Show)

data OverapproxMode
  = OverapproxNone
  | OverapproxSome
  deriving (Eq, Show)

data BufferRef
  = MemoryBuf
  | CalldataBuf
  | ReturndataBuf
  deriving (Eq, Show)

data CallField
  = CallGasField
  | CallToField
  | CallValueField
  | CallInputOffsetField
  | CallInputSizeField
  | CallOutputOffsetField
  | CallOutputSizeField
  | CallReturndataLengthField
  | CallPostStorageBaseField
  | CallConstraintCountField
  deriving (Eq, Show)

data WordTerm
  = StackTerm Int
  | VarTerm T.Text
  | LitTerm W256
  | AddressValueTerm (Expr EAddr)
  | AddressTerm
  | CodeAddressTerm
  | CallerTerm
  | OriginTerm
  | CoinbaseTerm
  | CallvalueTerm
  | BlockNumberTerm
  | TimestampTerm
  | CallCountTerm
  | CallFieldTerm Int CallField
  | CallReturndataWordTerm Int WordTerm
  | BufferWordTerm BufferRef WordTerm
  | BufferLengthTerm BufferRef
  | StorageTerm WordTerm
  deriving (Eq, Show)

data Condition
  = WordCondition CompareOp WordTerm WordTerm
  | PcCondition CompareOp Int
  | StopCondition StopPredicate
  | SmtCondition CompareOp SmtMode
  | OverapproxCondition CompareOp OverapproxMode
  | CallOutcomeCondition CompareOp Int CallBoundaryOutcome
  | CallFailureModeCondition CompareOp Int CallFailureMode
  | CallOpcodeCondition CompareOp Int CallOpcode
  deriving (Eq, Show)

data PostconditionStatus
  = PostconditionQed
  | PostconditionQedWithAbstraction
  | PostconditionCex (Maybe String)
  | PostconditionUnknown String
  | PostconditionError String
  deriving (Eq, Show)

data PostconditionReport = PostconditionReport
  { condition :: Condition
  , status :: PostconditionStatus
  } deriving (Eq, Show)

conditionToPreProp :: MidpointSpec -> Condition -> Either String Prop
conditionToPreProp spec = \case
  WordCondition op lhs rhs -> do
    lhsExpr <- resolveInitialWordTerm spec lhs
    rhsExpr <- resolveInitialWordTerm spec rhs
    pure $ compareExprs op lhsExpr rhsExpr
  PcCondition {} ->
    Left "pc preconditions are not supported; set --pc directly"
  StopCondition {} ->
    Left "halt-mode preconditions are not supported"
  SmtCondition {} ->
    Left "smt-mode preconditions are not supported"
  OverapproxCondition {} ->
    Left "overapproximation preconditions are not supported"
  CallOutcomeCondition {} ->
    Left "call outcome preconditions are not supported"
  CallFailureModeCondition {} ->
    Left "call failure-mode preconditions are not supported"
  CallOpcodeCondition {} ->
    Left "call opcode preconditions are not supported"

checkPostconditionsWithSolvers
  :: SegmentRunSpec
  -> [Condition]
  -> [SegmentResult]
  -> IO [[PostconditionReport]]
checkPostconditionsWithSolvers runSpec conditions results =
  Effects.runEnv Effects.defaultEnv $
    Solvers.withSolvers Solvers.Z3 1 Nothing Solvers.defMemLimit $ \solverGroup ->
      traverse
        (\result -> traverse (\cond -> checkOne solverGroup cond result) conditions)
        results
  where
    checkOne
      :: Solvers.SolverGroup
      -> Condition
      -> SegmentResult
      -> ReaderT Effects.Env IO PostconditionReport
    checkOne solverGroup cond result =
      PostconditionReport cond <$> checkPostcondition solverGroup result cond

    checkPostcondition
      :: Solvers.SolverGroup
      -> SegmentResult
      -> Condition
      -> ReaderT Effects.Env IO PostconditionStatus
    checkPostcondition solverGroup result = \case
      WordCondition op lhs rhs ->
        liftIO (stToIO $ SymExec.freezeVM result.finalVm) >>= \frozenVm ->
          case buildFinalWordProp result frozenVm (WordCondition op lhs rhs) of
            Left err -> pure $ PostconditionError err
            Right prop -> do
              outcome <-
                checkSatWithPolicy
                  runSpec.smtPolicy
                  solverGroup
                  "postcondition"
                  (result.finalVm.constraints <> [negateProp prop])
              pure $ fromSmtResult outcome result (Just frozenVm) (Just (lhs, rhs))
      PcCondition op rhs ->
        pure $
          if compareInt op result.finalVm.state.pc rhs
            then PostconditionQed
            else PostconditionCex (Just $ "actual pc = " <> show result.finalVm.state.pc)
      StopCondition want ->
        pure $
          if matchesStopPredicate want result.stopReason
            then PostconditionQed
            else PostconditionCex (Just $ "actual stop = " <> show result.stopReason)
      SmtCondition op want ->
        pure $
          case op of
            CmpEq -> checkSmtMode want (==)
            CmpNe -> checkSmtMode want (/=)
            _ -> PostconditionError "smt only supports == and !="
      OverapproxCondition op want ->
        pure $
          case op of
            CmpEq -> checkOverapproxMode want (==)
            CmpNe -> checkOverapproxMode want (/=)
            _ -> PostconditionError "overapprox only supports == and !="
      CallOutcomeCondition op idx want ->
        pure $
          case op of
            CmpEq -> checkCallOutcome idx want (==)
            CmpNe -> checkCallOutcome idx want (/=)
            _ -> PostconditionError "call[N].outcome only supports == and !="
      CallFailureModeCondition op idx want ->
        pure $
          case op of
            CmpEq -> checkCallFailureMode idx want (==)
            CmpNe -> checkCallFailureMode idx want (/=)
            _ -> PostconditionError "call[N].failure-mode only supports == and !="
      CallOpcodeCondition op idx want ->
        pure $
          case op of
            CmpEq -> checkCallOpcode idx want (==)
            CmpNe -> checkCallOpcode idx want (/=)
            _ -> PostconditionError "call[N].opcode only supports == and !="
      where
        checkCallOutcome idx want cmp =
          case resolveCallOutcome result idx of
            Left err -> PostconditionError err
            Right got ->
              if cmp got want
                then PostconditionQed
                else PostconditionCex (Just $ "actual call[" <> show idx <> "].outcome = " <> showCallBoundaryOutcome got)

        checkCallFailureMode idx want cmp =
          case resolveCallFailureMode result idx of
            Left err -> PostconditionError err
            Right got ->
              if cmp got want
                then PostconditionQed
                else PostconditionCex (Just $ "actual call[" <> show idx <> "].failure-mode = " <> showCallFailureMode got)

        checkCallOpcode idx want cmp =
          case resolveCallOpcode result idx of
            Left err -> PostconditionError err
            Right got ->
              if cmp got want
                then PostconditionQed
                else PostconditionCex (Just $ "actual call[" <> show idx <> "].opcode = " <> showCallOpcode got)

        checkSmtMode want cmp =
          let got = if result.usedWeakenedSmt then SmtWeakened else SmtExact
          in if cmp got want
              then PostconditionQed
              else PostconditionCex (Just $ "actual smt = " <> showSmtMode got)

        checkOverapproxMode want cmp =
          let got = if null result.overapproximations then OverapproxNone else OverapproxSome
          in if cmp got want
              then PostconditionQed
              else PostconditionCex (Just $ "actual overapprox = " <> showOverapproxMode got)

    fromSmtResult :: SmtQueryOutcome -> SegmentResult -> Maybe (VM Symbolic) -> Maybe (WordTerm, WordTerm) -> PostconditionStatus
    fromSmtResult outcome result frozenVm wordTerms =
      case (outcome.weakened, outcome.smtResult) of
        (False, Qed) -> PostconditionQed
        (True, Qed) -> PostconditionQedWithAbstraction
        (False, Cex cex) ->
          PostconditionCex $
            case (frozenVm, wordTerms) of
              (Just vm, Just terms) -> renderWordCounterexample result vm terms cex
              _ -> Nothing
        (True, Cex _) ->
          PostconditionUnknown "weakened query is satisfiable; exact counterexamples are not trustworthy"
        (_, Unknown msg) ->
          PostconditionUnknown msg
        (_, Error msg) ->
          PostconditionError msg

renderWordCounterexample
  :: SegmentResult
  -> VM Symbolic
  -> (WordTerm, WordTerm)
  -> SMTCex
  -> Maybe String
renderWordCounterexample result vm (lhsTerm, rhsTerm) cex = do
  lhsExpr <- either (const Nothing) Just (resolveFinalWordTerm result vm lhsTerm)
  rhsExpr <- either (const Nothing) Just (resolveFinalWordTerm result vm rhsTerm)
  pure $
    showWordTerm lhsTerm
      <> " = "
      <> prettyWordExprFromCex cex lhsExpr
      <> ", "
      <> showWordTerm rhsTerm
      <> " = "
      <> prettyWordExprFromCex cex rhsExpr

resolveInitialWordTerm :: MidpointSpec -> WordTerm -> Either String (Expr EWord)
resolveInitialWordTerm spec = \case
  StackTerm idx ->
    maybe
      (Left $ "initial stack index out of bounds: " <> show idx)
      Right
      (indexList idx spec.stack)
  VarTerm name -> Right $ Var name
  LitTerm val -> Right $ Lit val
  AddressValueTerm addrExpr -> Right $ forceEAddrToEWord addrExpr
  AddressTerm -> Right $ forceEAddrToEWord spec.address
  CodeAddressTerm -> Right $ forceEAddrToEWord spec.codeAddress
  CallerTerm -> Right $ forceEAddrToEWord spec.caller
  OriginTerm -> Right $ forceEAddrToEWord spec.origin
  CoinbaseTerm -> Right $ forceEAddrToEWord spec.coinbase
  CallvalueTerm -> Right spec.callvalue
  BlockNumberTerm -> Right spec.blockNumber
  TimestampTerm -> Right spec.timestamp
  CallCountTerm -> Left "call-count is only available in postconditions"
  CallFieldTerm {} -> Left "call[N].FIELD terms are only available in postconditions"
  CallReturndataWordTerm {} -> Left "call[N].returndata[...] terms are only available in postconditions"
  BufferWordTerm bufRef offsetTerm -> do
    offsetExpr <- resolveInitialWordTerm spec offsetTerm
    pure $ Expr.readWord offsetExpr (bufferExprFromSpec spec bufRef)
  BufferLengthTerm bufRef ->
    pure $ Expr.bufLength (bufferExprFromSpec spec bufRef)
  StorageTerm slotTerm -> do
    slotExpr <- resolveInitialWordTerm spec slotTerm
    pure $ Expr.readStorage' slotExpr spec.storage

buildFinalWordProp :: SegmentResult -> VM Symbolic -> Condition -> Either String Prop
buildFinalWordProp result vm = \case
  WordCondition op lhs rhs -> do
    lhsExpr <- resolveFinalWordTerm result vm lhs
    rhsExpr <- resolveFinalWordTerm result vm rhs
    pure $ compareExprs op lhsExpr rhsExpr
  _ ->
    Left "internal error: expected word postcondition"

resolveFinalWordTerm :: SegmentResult -> VM Symbolic -> WordTerm -> Either String (Expr EWord)
resolveFinalWordTerm result vm = \case
  StackTerm idx ->
    maybe
      (Left $ "final stack index out of bounds: " <> show idx)
      Right
      (indexList idx vm.state.stack)
  VarTerm name -> Right $ Var name
  LitTerm val -> Right $ Lit val
  AddressValueTerm addrExpr -> Right $ forceEAddrToEWord addrExpr
  AddressTerm -> Right $ forceEAddrToEWord vm.state.contract
  CodeAddressTerm -> Right $ forceEAddrToEWord vm.state.codeContract
  CallerTerm -> Right $ forceEAddrToEWord vm.state.caller
  OriginTerm -> Right $ forceEAddrToEWord vm.tx.origin
  CoinbaseTerm -> Right $ forceEAddrToEWord vm.block.coinbase
  CallvalueTerm -> Right vm.state.callvalue
  BlockNumberTerm -> Right vm.block.number
  TimestampTerm -> Right vm.block.timestamp
  CallCountTerm -> Right $ Lit (fromIntegral (length result.callBoundaries))
  CallFieldTerm idx field -> resolveCallFieldTerm result idx field
  CallReturndataWordTerm idx offsetTerm -> do
    boundary <- resolveCallBoundary result idx
    offsetExpr <- resolveFinalWordTerm result vm offsetTerm
    pure $ Expr.readWord offsetExpr boundary.postReturndata
  BufferWordTerm bufRef offsetTerm -> do
    offsetExpr <- resolveFinalWordTerm result vm offsetTerm
    pure $ Expr.readWord offsetExpr (bufferExprFromVm vm bufRef)
  BufferLengthTerm bufRef ->
    pure $ Expr.bufLength (bufferExprFromVm vm bufRef)
  StorageTerm slotTerm -> do
    slotExpr <- resolveFinalWordTerm result vm slotTerm
    pure $ Expr.readStorage' slotExpr (storageExprFromVm vm)

resolveCallFieldTerm :: SegmentResult -> Int -> CallField -> Either String (Expr EWord)
resolveCallFieldTerm result idx field = do
  boundary <- resolveCallBoundary result idx
  case field of
    CallGasField -> Right boundary.gas
    CallToField -> Right boundary.callee
    CallValueField ->
      maybe
        (Left $ "call[" <> show idx <> "].value is undefined for " <> show boundary.opcode)
        Right
        boundary.value
    CallInputOffsetField -> Right boundary.inputOffset
    CallInputSizeField -> Right boundary.inputSize
    CallOutputOffsetField -> Right boundary.outputOffset
    CallOutputSizeField -> Right boundary.outputSize
    CallReturndataLengthField -> Right (Expr.bufLength boundary.postReturndata)
    CallPostStorageBaseField ->
      maybe
        (Left $ "call[" <> show idx <> "].post-storage-base is undefined")
        (Right . forceEAddrToEWord)
        boundary.postStorageBase
    CallConstraintCountField -> Right (Lit (fromIntegral (length boundary.pathConstraints)))

resolveCallBoundary :: SegmentResult -> Int -> Either String CallBoundary
resolveCallBoundary result idx =
  maybe
    (Left $ "call boundary index out of bounds: " <> show idx)
    Right
    (indexList idx result.callBoundaries)

indexList :: Int -> [a] -> Maybe a
indexList idx xs
  | idx < 0 = Nothing
  | otherwise = go idx xs
  where
    go 0 (y : _) = Just y
    go n (_ : ys) = go (n - 1) ys
    go _ [] = Nothing

compareExprs :: CompareOp -> Expr EWord -> Expr EWord -> Prop
compareExprs op lhs rhs =
  case op of
    CmpEq -> lhs .== rhs
    CmpNe -> lhs ./= rhs
    CmpLt -> lhs .< rhs
    CmpLe -> PLEq lhs rhs
    CmpGt -> lhs .> rhs
    CmpGe -> PGEq lhs rhs

negateProp :: Prop -> Prop
negateProp = PNeg

concretizeWordExpr :: SMTCex -> Expr EWord -> Either String (Expr EWord)
concretizeWordExpr cex expr =
  Expr.simplify <$> SymExec.defaultSymbolicValues (SymExec.subModel cex expr)

prettyWordExprFromCex :: SMTCex -> Expr EWord -> String
prettyWordExprFromCex cex expr =
  case concretizeWordExpr cex expr of
    Right (Lit val) -> show val
    Right concreteExpr -> T.unpack (Format.formatExpr concreteExpr)
    Left _ -> T.unpack (Format.formatExpr expr)

compareInt :: CompareOp -> Int -> Int -> Bool
compareInt op lhs rhs =
  case op of
    CmpEq -> lhs == rhs
    CmpNe -> lhs /= rhs
    CmpLt -> lhs < rhs
    CmpLe -> lhs <= rhs
    CmpGt -> lhs > rhs
    CmpGe -> lhs >= rhs

matchesStopPredicate :: StopPredicate -> SegmentStop -> Bool
matchesStopPredicate want stopReason =
  case (want, stopReason) of
    (StopTarget, StoppedAtTargetPc _) -> True
    (StopFuel, StoppedAtFuelExhaustion) -> True
    (StopSuccess, StoppedAtResult (VMSuccess _)) -> True
    (StopFailure, StoppedAtResult (VMFailure _)) -> True
    (StopPartial, StoppedAtResult (Unfinished _)) -> True
    _ -> False

bufferExprFromSpec :: MidpointSpec -> BufferRef -> Expr Buf
bufferExprFromSpec spec = \case
  MemoryBuf -> spec.memory
  CalldataBuf -> spec.calldata
  ReturndataBuf -> spec.returndata

bufferExprFromVm :: VM Symbolic -> BufferRef -> Expr Buf
bufferExprFromVm vm = \case
  MemoryBuf ->
    case vm.state.memory of
      SymbolicMemory mem -> mem
      ConcreteMemory _ -> error "expected frozen symbolic memory"
  CalldataBuf -> vm.state.calldata
  ReturndataBuf -> vm.state.returndata

storageExprFromVm :: VM Symbolic -> Expr Storage
storageExprFromVm vm =
  case Map.lookup vm.state.contract vm.env.contracts of
    Just contract -> contract.storage
    Nothing -> AbstractStore vm.state.contract Nothing

showWordTerm :: WordTerm -> String
showWordTerm = \case
  StackTerm idx -> "stack[" <> show idx <> "]"
  VarTerm name -> "var:" <> T.unpack name
  LitTerm val -> show val
  AddressValueTerm addrExpr -> T.unpack (Format.formatExpr (Expr.simplify addrExpr))
  AddressTerm -> "address"
  CodeAddressTerm -> "code-address"
  CallerTerm -> "caller"
  OriginTerm -> "origin"
  CoinbaseTerm -> "coinbase"
  CallvalueTerm -> "callvalue"
  BlockNumberTerm -> "block-number"
  TimestampTerm -> "timestamp"
  CallCountTerm -> "call-count"
  CallFieldTerm idx field ->
    "call[" <> show idx <> "]." <> showCallField field
  CallReturndataWordTerm idx offset ->
    "call[" <> show idx <> "].returndata[" <> showWordTerm offset <> "]"
  BufferWordTerm bufRef offset ->
    showBufferRef bufRef <> "[" <> showWordTerm offset <> "]"
  BufferLengthTerm bufRef ->
    "len(" <> showBufferRef bufRef <> ")"
  StorageTerm slot ->
    "storage[" <> showWordTerm slot <> "]"

showBufferRef :: BufferRef -> String
showBufferRef = \case
  MemoryBuf -> "memory"
  CalldataBuf -> "calldata"
  ReturndataBuf -> "returndata"

resolveCallOutcome :: SegmentResult -> Int -> Either String CallBoundaryOutcome
resolveCallOutcome result idx =
  maybe
    (Left $ "call boundary index out of bounds: " <> show idx)
    (Right . (.outcome))
    (indexList idx result.callBoundaries)

resolveCallFailureMode :: SegmentResult -> Int -> Either String CallFailureMode
resolveCallFailureMode result idx = do
  boundary <-
    maybe
      (Left $ "call boundary index out of bounds: " <> show idx)
      Right
      (indexList idx result.callBoundaries)
  maybe
    (Left $ "call[" <> show idx <> "].failure-mode is undefined for continued calls")
    Right
    boundary.failureMode

resolveCallOpcode :: SegmentResult -> Int -> Either String CallOpcode
resolveCallOpcode result idx =
  maybe
    (Left $ "call boundary index out of bounds: " <> show idx)
    (Right . (.opcode))
    (indexList idx result.callBoundaries)

showCallBoundaryOutcome :: CallBoundaryOutcome -> String
showCallBoundaryOutcome = \case
  CallContinued -> "continued"
  CallFailedDeterministic -> "failed-deterministic"
  CallFailedSymbolic -> "failed-symbolic"

showCallFailureMode :: CallFailureMode -> String
showCallFailureMode = \case
  CallFailureReturnsZero -> "returns-zero"
  CallFailureStopsFrame -> "stops-frame"

showCallOpcode :: CallOpcode -> String
showCallOpcode = \case
  CallOpCall -> "call"
  CallOpCallcode -> "callcode"
  CallOpDelegatecall -> "delegatecall"
  CallOpStaticcall -> "staticcall"

showSmtMode :: SmtMode -> String
showSmtMode = \case
  SmtExact -> "exact"
  SmtWeakened -> "weakened"

showOverapproxMode :: OverapproxMode -> String
showOverapproxMode = \case
  OverapproxNone -> "none"
  OverapproxSome -> "some"

showCallField :: CallField -> String
showCallField = \case
  CallGasField -> "gas"
  CallToField -> "to"
  CallValueField -> "value"
  CallInputOffsetField -> "input-offset"
  CallInputSizeField -> "input-size"
  CallOutputOffsetField -> "output-offset"
  CallOutputSizeField -> "output-size"
  CallReturndataLengthField -> "returndata-len"
  CallPostStorageBaseField -> "post-storage-base"
  CallConstraintCountField -> "constraint-count"
