{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}

module SymCheck.Midpoint
  ( MidpointSpec(..)
  , defaultMidpointSpec
  , SegmentRunSpec(..)
  , SegmentStop(..)
  , CallBoundary(..)
  , CallOpcode(..)
  , CallBoundaryOutcome(..)
  , CallFailureMode(..)
  , Overapproximation(..)
  , SegmentResult(..)
  , requiredInitialStackDepth
  , ensureInitialStackDepth
  , autoFillInitialStackDepth
  , runtimeCodeFromBytes
  , makeMidpointVM
  , runSegment
  , runSegmentWithSolvers
  ) where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT)
import Control.Monad.ST (RealWorld, ST, stToIO)
import Control.Monad.Trans.State.Strict (runStateT)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import EVM
import EVM.Expr qualified as Expr
import EVM.Effects qualified as Effects
import EVM.Fetch qualified as Fetch
import EVM.Op (getOp)
import EVM.Solvers qualified as Solvers
import EVM.SymExec qualified as SymExec
import EVM.Types
import SymCheck.Smt

import GHC.Word (Word8, Word64)

data MidpointSpec = MidpointSpec
  { code :: ContractCode
  , pc :: Int
  , stack :: [Expr EWord]
  , memory :: Expr Buf
  , memorySize :: Word64
  , storage :: Expr Storage
  , transientStorage :: Expr Storage
  , originalStorage :: Expr Storage
  , calldata :: Expr Buf
  , returndata :: Expr Buf
  , constraints :: [Prop]
  , address :: Expr EAddr
  , codeAddress :: Expr EAddr
  , caller :: Expr EAddr
  , overrideCaller :: Maybe (Expr EAddr)
  , origin :: Expr EAddr
  , coinbase :: Expr EAddr
  , callvalue :: Expr EWord
  , blockNumber :: Expr EWord
  , timestamp :: Expr EWord
  , static :: Bool
  , baseState :: BaseState
  }

data SegmentRunSpec = SegmentRunSpec
  { fuel :: Int
  , targetPc :: Maybe Int
  , config :: Effects.Config
  , smtPolicy :: SmtQueryPolicy
  }

data SegmentStop
  = StoppedAtTargetPc Int
  | StoppedAtFuelExhaustion
  | StoppedAtCallBoundary CallBoundary
  | StoppedAtResult (VMResult Symbolic)
  deriving (Show)

data CallOpcode
  = CallOpCall
  | CallOpCallcode
  | CallOpDelegatecall
  | CallOpStaticcall
  deriving (Eq, Show)

data CallBoundaryOutcome
  = CallContinued
  | CallFailedDeterministic
  | CallFailedSymbolic
  deriving (Eq, Show)

data CallFailureMode
  = CallFailureReturnsZero
  | CallFailureStopsFrame
  deriving (Eq, Show)

data CallBoundary = CallBoundary
  { opcode :: CallOpcode
  , outcome :: CallBoundaryOutcome
  , failureMode :: Maybe CallFailureMode
  , gas :: Expr EWord
  , callee :: Expr EWord
  , value :: Maybe (Expr EWord)
  , inputOffset :: Expr EWord
  , inputSize :: Expr EWord
  , outputOffset :: Expr EWord
  , outputSize :: Expr EWord
  , postReturndata :: Expr Buf
  , postStorageBase :: Maybe (Expr EAddr)
  , pathConstraints :: [Prop]
  } deriving (Show)

data Overapproximation
  = OverapproxCallSuccess CallOpcode
  | OverapproxCallReturndata CallOpcode
  | OverapproxCallStorage CallOpcode
  | OverapproxGasOpcode
  | OverapproxPostCallExtcodesize
  | OverapproxPostCallExtcodehash
  | OverapproxCoarseExtcodecopyMemory
  deriving (Eq, Show)

data SegmentResult = SegmentResult
  { steps :: Int
  , pcTrace :: [Int]
  , stopReason :: SegmentStop
  , callBoundaries :: [CallBoundary]
  , overapproximations :: [Overapproximation]
  , usedWeakenedSmt :: Bool
  , finalVm :: VM Symbolic
  }

data StackCheckOutcome
  = ContinueAt !Int !Int
  | StopCheck

requiredInitialStackDepth :: SegmentRunSpec -> MidpointSpec -> Either String Int
requiredInitialStackDepth runSpec spec =
  case spec.code of
    RuntimeCode (ConcreteRuntimeCode codeBytes) -> go 0 spec.pc 0 0 codeBytes
    RuntimeCode (SymbolicRuntimeCode _) ->
      Left "stack-depth check requires concrete runtime bytecode"
    InitCode _ _ ->
      Left "stack-depth check expects runtime bytecode, not initcode"
    UnknownCode _ ->
      Left "stack-depth check requires known bytecode"
  where
    go :: Int -> Int -> Int -> Int -> ByteString -> Either String Int
    go stepsChecked pc0 depthDelta depthRequired codeBytes
      | stepsChecked >= runSpec.fuel = Right depthRequired
      | Just stopPc <- runSpec.targetPc
      , pc0 == stopPc = Right depthRequired
      | pc0 < 0 = Left $ "negative pc in stack-depth check: " <> show pc0
      | pc0 >= BS.length codeBytes = Right depthRequired
      | otherwise = do
          let opcodeByte = BS.index codeBytes pc0
              op = getOp opcodeByte
              needed = opRequiredDepth op
              produced = opProducedDepth op
              depthRequired' = max depthRequired (needed - depthDelta)
              depthDelta' = depthDelta - needed + produced
          case nextStackCheckState pc0 op of
            StopCheck -> Right depthRequired'
            ContinueAt pc1 stepCost ->
              go (stepsChecked + stepCost) pc1 depthDelta' depthRequired' codeBytes

    opRequiredDepth :: GenericOp Word8 -> Int
    opRequiredDepth = \case
      OpStop -> 0
      OpAdd -> 2
      OpMul -> 2
      OpSub -> 2
      OpDiv -> 2
      OpSdiv -> 2
      OpMod -> 2
      OpSmod -> 2
      OpAddmod -> 3
      OpMulmod -> 3
      OpExp -> 2
      OpSignextend -> 2
      OpLt -> 2
      OpGt -> 2
      OpSlt -> 2
      OpSgt -> 2
      OpEq -> 2
      OpIszero -> 1
      OpAnd -> 2
      OpOr -> 2
      OpXor -> 2
      OpNot -> 1
      OpByte -> 2
      OpShl -> 2
      OpShr -> 2
      OpSar -> 2
      OpClz -> 1
      OpSha3 -> 2
      OpAddress -> 0
      OpBalance -> 1
      OpOrigin -> 0
      OpCaller -> 0
      OpCallvalue -> 0
      OpCalldataload -> 1
      OpCalldatasize -> 0
      OpCalldatacopy -> 3
      OpCodesize -> 0
      OpCodecopy -> 3
      OpGasprice -> 0
      OpExtcodesize -> 1
      OpExtcodecopy -> 4
      OpReturndatasize -> 0
      OpReturndatacopy -> 3
      OpExtcodehash -> 1
      OpBlockhash -> 1
      OpCoinbase -> 0
      OpTimestamp -> 0
      OpNumber -> 0
      OpPrevRandao -> 0
      OpGaslimit -> 0
      OpChainid -> 0
      OpSelfbalance -> 0
      OpBaseFee -> 0
      OpBlobhash -> 1
      OpBlobBaseFee -> 0
      OpPop -> 1
      OpMcopy -> 3
      OpMload -> 1
      OpMstore -> 2
      OpMstore8 -> 2
      OpSload -> 1
      OpSstore -> 2
      OpTload -> 1
      OpTstore -> 2
      OpJump -> 1
      OpJumpi -> 2
      OpPc -> 0
      OpMsize -> 0
      OpGas -> 0
      OpJumpdest -> 0
      OpCreate -> 3
      OpCall -> 7
      OpStaticcall -> 6
      OpCallcode -> 7
      OpReturn -> 2
      OpDelegatecall -> 6
      OpCreate2 -> 4
      OpRevert -> 2
      OpSelfdestruct -> 1
      OpDup n -> fromIntegral n
      OpSwap n -> fromIntegral n + 1
      OpLog n -> fromIntegral n + 2
      OpPush0 -> 0
      OpPush _ -> 0
      OpUnknown _ -> 0

    opProducedDepth :: GenericOp Word8 -> Int
    opProducedDepth = \case
      OpStop -> 0
      OpAdd -> 1
      OpMul -> 1
      OpSub -> 1
      OpDiv -> 1
      OpSdiv -> 1
      OpMod -> 1
      OpSmod -> 1
      OpAddmod -> 1
      OpMulmod -> 1
      OpExp -> 1
      OpSignextend -> 1
      OpLt -> 1
      OpGt -> 1
      OpSlt -> 1
      OpSgt -> 1
      OpEq -> 1
      OpIszero -> 1
      OpAnd -> 1
      OpOr -> 1
      OpXor -> 1
      OpNot -> 1
      OpByte -> 1
      OpShl -> 1
      OpShr -> 1
      OpSar -> 1
      OpClz -> 1
      OpSha3 -> 1
      OpAddress -> 1
      OpBalance -> 1
      OpOrigin -> 1
      OpCaller -> 1
      OpCallvalue -> 1
      OpCalldataload -> 1
      OpCalldatasize -> 1
      OpCalldatacopy -> 0
      OpCodesize -> 1
      OpCodecopy -> 0
      OpGasprice -> 1
      OpExtcodesize -> 1
      OpExtcodecopy -> 0
      OpReturndatasize -> 1
      OpReturndatacopy -> 0
      OpExtcodehash -> 1
      OpBlockhash -> 1
      OpCoinbase -> 1
      OpTimestamp -> 1
      OpNumber -> 1
      OpPrevRandao -> 1
      OpGaslimit -> 1
      OpChainid -> 1
      OpSelfbalance -> 1
      OpBaseFee -> 1
      OpBlobhash -> 1
      OpBlobBaseFee -> 1
      OpPop -> 0
      OpMcopy -> 0
      OpMload -> 1
      OpMstore -> 0
      OpMstore8 -> 0
      OpSload -> 1
      OpSstore -> 0
      OpTload -> 1
      OpTstore -> 0
      OpJump -> 0
      OpJumpi -> 0
      OpPc -> 1
      OpMsize -> 1
      OpGas -> 1
      OpJumpdest -> 0
      OpCreate -> 1
      OpCall -> 1
      OpStaticcall -> 1
      OpCallcode -> 1
      OpReturn -> 0
      OpDelegatecall -> 1
      OpCreate2 -> 1
      OpRevert -> 0
      OpSelfdestruct -> 0
      OpDup n -> fromIntegral n + 1
      OpSwap n -> fromIntegral n + 1
      OpLog _ -> 0
      OpPush0 -> 1
      OpPush _ -> 1
      OpUnknown _ -> 0

    nextStackCheckState :: Int -> GenericOp Word8 -> StackCheckOutcome
    nextStackCheckState pc0 = \case
      OpStop -> StopCheck
      OpReturn -> StopCheck
      OpRevert -> StopCheck
      OpSelfdestruct -> StopCheck
      OpCall -> StopCheck
      OpCallcode -> StopCheck
      OpDelegatecall -> StopCheck
      OpStaticcall -> StopCheck
      OpJump -> StopCheck
      OpJumpi -> StopCheck
      OpUnknown _ -> StopCheck
      OpPush width -> ContinueAt (pc0 + 1 + fromIntegral width) 1
      _ -> ContinueAt (pc0 + 1) 1

ensureInitialStackDepth :: SegmentRunSpec -> MidpointSpec -> Either String ()
ensureInitialStackDepth runSpec spec = do
  requiredDepth <- requiredInitialStackDepth runSpec spec
  let actualDepth = length spec.stack
  if actualDepth >= requiredDepth
    then Right ()
    else Left $
      "segment requires initial stack depth >= " <> show requiredDepth
        <> ", but only " <> show actualDepth <> " item(s) were provided"

autoFillInitialStackDepth :: SegmentRunSpec -> MidpointSpec -> Either String MidpointSpec
autoFillInitialStackDepth runSpec spec = do
  requiredDepth <- requiredInitialStackDepth runSpec spec
  let actualDepth = length spec.stack
      missingDepth = requiredDepth - actualDepth
      filler =
        [ Var (T.pack ("stack_" <> show idx))
        | idx <- [0 .. missingDepth - 1]
        ]
  pure $
    if missingDepth <= 0
      then spec
      else MidpointSpec
        { code = spec.code
        , pc = spec.pc
        , stack = spec.stack <> filler
        , memory = spec.memory
        , memorySize = spec.memorySize
        , storage = spec.storage
        , transientStorage = spec.transientStorage
        , originalStorage = spec.originalStorage
        , calldata = spec.calldata
        , returndata = spec.returndata
        , constraints = spec.constraints
        , address = spec.address
        , codeAddress = spec.codeAddress
        , caller = spec.caller
        , overrideCaller = spec.overrideCaller
        , origin = spec.origin
        , coinbase = spec.coinbase
        , callvalue = spec.callvalue
        , blockNumber = spec.blockNumber
        , timestamp = spec.timestamp
        , static = spec.static
        , baseState = spec.baseState
        }

runtimeCodeFromBytes :: ByteString -> ContractCode
runtimeCodeFromBytes = RuntimeCode . ConcreteRuntimeCode

defaultMidpointSpec :: ByteString -> MidpointSpec
defaultMidpointSpec codeBytes =
  let addr = SymAddr "entrypoint"
      storageExpr = AbstractStore addr Nothing
  in MidpointSpec
      { code = runtimeCodeFromBytes codeBytes
      , pc = 0
      , stack = []
      , memory = AbstractBuf "memory"
      , memorySize = 0
      , storage = storageExpr
      , transientStorage = storageExpr
      , originalStorage = storageExpr
      , calldata = AbstractBuf "calldata"
      , returndata = ConcreteBuf mempty
      , constraints = []
      , address = addr
      , codeAddress = addr
      , caller = SymAddr "caller"
      , overrideCaller = Nothing
      , origin = SymAddr "origin"
      , coinbase = SymAddr "coinbase"
      , callvalue = Lit 0
      , blockNumber = Lit 0
      , timestamp = Lit 0
      , static = False
      , baseState = AbstractBase
      }

makeMidpointVM :: MidpointSpec -> ST RealWorld (VM Symbolic)
makeMidpointVM spec = do
  let seeded = (abstractContract spec.code spec.codeAddress)
        { storage = spec.storage
        , tStorage = spec.transientStorage
        , origStorage = spec.originalStorage
        }
  vm0 <- makeVm $ defaultVMOpts
    { contract = seeded
    , calldata = (spec.calldata, spec.constraints)
    , value = spec.callvalue
    , baseState = spec.baseState
    , address = spec.address
    , caller = spec.caller
    , origin = spec.origin
    , coinbase = spec.coinbase
    , number = spec.blockNumber
    , timestamp = spec.timestamp
    , blockGaslimit = 0
    , prevRandao = 42069
    }
  let env' :: Env
      env' =
        Env
          { contracts =
              Map.insert spec.codeAddress seeded $
              Map.insert spec.address seeded vm0.env.contracts
          , chainId = vm0.env.chainId
          , freshAddresses = vm0.env.freshAddresses
          , freshGasVals = vm0.env.freshGasVals
          }
      state' :: FrameState Symbolic
      state' =
        vm0.state
          { pc = spec.pc
          , stack = spec.stack
          , memory = SymbolicMemory spec.memory
          , memorySize = spec.memorySize
          , calldata = spec.calldata
          , callvalue = spec.callvalue
        , caller = spec.caller
        , overrideCaller = spec.overrideCaller
        , returndata = spec.returndata
        , contract = spec.address
        , codeContract = spec.codeAddress
        , static = spec.static
        }
  pure vm0
    { env = env'
    , state = state'
    , constraints = spec.constraints
    }

runSegment :: SegmentRunSpec -> VM Symbolic -> ST RealWorld SegmentResult
runSegment spec = go [] [] [] 0 spec.fuel
  where
    go traceRev seenCalls overapprox stepsLeft fuelLeft vm
      | Just stopPc <- spec.targetPc
      , vm.state.pc == stopPc =
          pure SegmentResult
            { steps = stepsLeft
            , pcTrace = finishPcTrace traceRev vm.state.pc
            , stopReason = StoppedAtTargetPc stopPc
            , callBoundaries = reverse seenCalls
            , overapproximations = reverse overapprox
            , usedWeakenedSmt = False
            , finalVm = vm
            }
      | Just result <- vm.result =
          pure SegmentResult
            { steps = stepsLeft
            , pcTrace = finishPcTrace traceRev vm.state.pc
            , stopReason = StoppedAtResult result
            , callBoundaries = reverse seenCalls
            , overapproximations = reverse overapprox
            , usedWeakenedSmt = False
            , finalVm = vm
            }
      | fuelLeft <= 0 =
          pure SegmentResult
            { steps = stepsLeft
            , pcTrace = finishPcTrace traceRev vm.state.pc
            , stopReason = StoppedAtFuelExhaustion
            , callBoundaries = reverse seenCalls
            , overapproximations = reverse overapprox
            , usedWeakenedSmt = False
            , finalVm = vm
            }
      | Just (boundary, vm', newOverapprox) <- cutAtCallBoundary vm =
          go (extendPcTrace traceRev vm.state.pc) (boundary : seenCalls) (reverse newOverapprox <> overapprox) (stepsLeft + 1) (fuelLeft - 1) vm'
      | Just (vm', newOverapprox) <- abstractGasStep vm =
          go (extendPcTrace traceRev vm.state.pc) seenCalls (reverse newOverapprox <> overapprox) (stepsLeft + 1) (fuelLeft - 1) vm'
      | Just (vm', newOverapprox) <- abstractPostCallWorldStep vm =
          go (extendPcTrace traceRev vm.state.pc) seenCalls (reverse newOverapprox <> overapprox) (stepsLeft + 1) (fuelLeft - 1) vm'
      | otherwise = do
          (_, vm') <- runStateT (exec1 spec.config) vm
          go (extendPcTrace traceRev vm.state.pc) seenCalls overapprox (stepsLeft + 1) (fuelLeft - 1) vm'

runSegmentWithSolvers :: SegmentRunSpec -> VM Symbolic -> IO [SegmentResult]
runSegmentWithSolvers spec vm0 =
  Effects.runEnv Effects.defaultEnv $
    Solvers.withSolvers Solvers.Z3 1 Nothing Solvers.defMemLimit $ \solverGroup ->
      go solverGroup [] [] [] False 0 spec.fuel vm0
  where
    go
      :: Solvers.SolverGroup
      -> [Int]
      -> [CallBoundary]
      -> [Overapproximation]
      -> Bool
      -> Int
      -> Int
      -> VM Symbolic
      -> ReaderT Effects.Env IO [SegmentResult]
    go solverGroup traceRev seenCalls overapprox weakenedSmt stepsLeft fuelLeft vm
      | Just stopPc <- spec.targetPc
      , vm.state.pc == stopPc =
          pure [SegmentResult
            { steps = stepsLeft
            , pcTrace = finishPcTrace traceRev vm.state.pc
            , stopReason = StoppedAtTargetPc stopPc
            , callBoundaries = reverse seenCalls
            , overapproximations = reverse overapprox
            , usedWeakenedSmt = weakenedSmt
            , finalVm = vm
            }]
      | Just result <- vm.result =
          case result of
            HandleEffect (Query query0) ->
              resolveQuery solverGroup query0 vm >>= \case
                Nothing ->
                  pure [SegmentResult
                    { steps = stepsLeft
                    , pcTrace = finishPcTrace traceRev vm.state.pc
                    , stopReason = StoppedAtResult result
                    , callBoundaries = reverse seenCalls
                    , overapproximations = reverse overapprox
                    , usedWeakenedSmt = weakenedSmt
                    , finalVm = vm
                    }]
                Just (queryUsedWeakening, vm') ->
                  go solverGroup traceRev seenCalls overapprox (weakenedSmt || queryUsedWeakening) stepsLeft fuelLeft vm'
            HandleEffect (Branch context) ->
              branchVMs context vm >>= \case
                [] ->
                  pure [SegmentResult
                    { steps = stepsLeft
                    , pcTrace = finishPcTrace traceRev vm.state.pc
                    , stopReason = StoppedAtResult result
                    , callBoundaries = reverse seenCalls
                    , overapproximations = reverse overapprox
                    , usedWeakenedSmt = weakenedSmt
                    , finalVm = vm
                    }]
                vms ->
                  concat <$> traverse (go solverGroup traceRev seenCalls overapprox weakenedSmt stepsLeft fuelLeft) vms
            _ ->
              pure [SegmentResult
                { steps = stepsLeft
                , pcTrace = finishPcTrace traceRev vm.state.pc
                , stopReason = StoppedAtResult result
                , callBoundaries = reverse seenCalls
                , overapproximations = reverse overapprox
                , usedWeakenedSmt = weakenedSmt
                , finalVm = vm
                }]
      | fuelLeft <= 0 =
          pure [SegmentResult
            { steps = stepsLeft
            , pcTrace = finishPcTrace traceRev vm.state.pc
            , stopReason = StoppedAtFuelExhaustion
            , callBoundaries = reverse seenCalls
            , overapproximations = reverse overapprox
            , usedWeakenedSmt = weakenedSmt
            , finalVm = vm
            }]
      | Just boundary <- callBoundaryForCurrentOp vm =
          continueAfterCallWithSolvers solverGroup vm boundary >>= \branches ->
            concat <$>
              traverse
                (\(boundary', vm', newOverapprox, branchUsedWeakening) ->
                  go
                    solverGroup
                    (extendPcTrace traceRev vm.state.pc)
                    (boundary' : seenCalls)
                    (reverse newOverapprox <> overapprox)
                    (weakenedSmt || branchUsedWeakening)
                    (stepsLeft + 1)
                    (fuelLeft - 1)
                    vm')
                branches
      | Just (vm', newOverapprox) <- abstractGasStep vm =
          go solverGroup (extendPcTrace traceRev vm.state.pc) seenCalls (reverse newOverapprox <> overapprox) weakenedSmt (stepsLeft + 1) (fuelLeft - 1) vm'
      | Just (vm', newOverapprox) <- abstractPostCallWorldStep vm =
          go solverGroup (extendPcTrace traceRev vm.state.pc) seenCalls (reverse newOverapprox <> overapprox) weakenedSmt (stepsLeft + 1) (fuelLeft - 1) vm'
      | otherwise = do
          (_, vm') <- liftIO $ stToIO $ runStateT (exec1 spec.config) vm
          go solverGroup (extendPcTrace traceRev vm.state.pc) seenCalls overapprox weakenedSmt (stepsLeft + 1) (fuelLeft - 1) vm'

    resolveQuery
      :: Solvers.SolverGroup
      -> Query Symbolic
      -> VM Symbolic
      -> ReaderT Effects.Env IO (Maybe (Bool, VM Symbolic))
    resolveQuery solverGroup query0 vm =
      case query0 of
        PleaseAskSMT branchcondition pathconditions continue -> do
          let pathconds = foldl' PAnd (PBool True) pathconditions
          branchOutcome <-
            case branchcondition of
              Lit 0 -> pure (BranchQueryOutcome (Case False) False)
              Lit _ -> pure (BranchQueryOutcome (Case True) False)
              _ -> checkBranchWithPolicy spec.smtPolicy solverGroup (branchcondition ./= Lit 0) pathconds
          let action = continue branchOutcome.branchCondition
          fmap (\(_, vm') -> Just (branchOutcome.usedWeakening, vm')) (liftIO $ stToIO $ runStateT action vm)
        PleaseGetSols {} -> runFetcher
        _ -> pure Nothing
      where
        runFetcher = do
          let fetcher = Fetch.noRpcFetcher solverGroup
          action <- fetcher query0
          fmap (\(_, vm') -> Just (False, vm')) (liftIO $ stToIO $ runStateT action vm)

    branchVMs
      :: BranchContext
      -> VM Symbolic
      -> ReaderT Effects.Env IO [VM Symbolic]
    branchVMs context vm = do
      frozen <- liftIO $ stToIO $ SymExec.freezeVM vm
      case context of
        PleaseRunBoth continue -> do
          let branchDepth = vm.exploreDepth + 1
          trueVm <- snd <$> (liftIO $ stToIO $ runStateT (continue True) frozen { result = Nothing, exploreDepth = branchDepth })
          falseVm <- snd <$> (liftIO $ stToIO $ runStateT (continue False) frozen { result = Nothing, exploreDepth = branchDepth })
          pure [trueVm, falseVm]
        PleaseRunAll vals continue -> do
          let branchDepth = vm.exploreDepth + 1
          traverse
            (\val -> snd <$> (liftIO $ stToIO $ runStateT (continue val) frozen { result = Nothing, exploreDepth = branchDepth }))
            vals

    continueAfterCallWithSolvers
      :: Solvers.SolverGroup
      -> VM Symbolic
      -> CallBoundary
      -> ReaderT Effects.Env IO [(CallBoundary, VM Symbolic, [Overapproximation], Bool)]
    continueAfterCallWithSolvers solverGroup vm boundary =
      let plan = callContinuationPlan vm boundary
      in case symbolicPreCallOutcome vm boundary of
          Left err ->
            pure [(boundary, vm {result = Just (VMFailure err)}, [], False)]
          Right (CallPrecheckDeterministicFailure memorySize') ->
            pure [(boundary, deterministicCallFailureVm vm plan memorySize', [], False)]
          Right (CallPrecheckDeterministicContinuation memorySize') ->
            let (boundary', vm', newOverapprox) = abstractCallContinuationVm vm boundary plan memorySize'
            in pure [(boundary', vm', newOverapprox, False)]
          Right (CallPrecheckBranch failureKind failureProp memorySize') -> do
            failOutcome <- checkSatWithPolicy spec.smtPolicy solverGroup "call precheck failure" (vm.constraints <> [failureProp])
            contOutcome <- checkSatWithPolicy spec.smtPolicy solverGroup "call precheck continuation" (vm.constraints <> [PNeg failureProp])
            let usedWeakening = failOutcome.weakened || contOutcome.weakened
                failureBranch = buildFailureBranch vm boundary plan failureKind failureProp memorySize'
                continueBranch = buildContinueBranch vm boundary plan failureProp memorySize'
            pure $
              case (isSatLike failOutcome.smtResult, isSatLike contOutcome.smtResult) of
                (False, False) -> []
                (True, False) -> [failureBranch usedWeakening]
                (False, True) -> [continueBranch usedWeakening]
                (True, True) -> [failureBranch usedWeakening, continueBranch usedWeakening]

extendPcTrace :: [Int] -> Int -> [Int]
extendPcTrace traceRev pc0 =
  case traceRev of
    pc1 : _ | pc1 == pc0 -> traceRev
    _ -> pc0 : traceRev

finishPcTrace :: [Int] -> Int -> [Int]
finishPcTrace traceRev pc0 =
  reverse (extendPcTrace traceRev pc0)

cutAtCallBoundary :: VM Symbolic -> Maybe (CallBoundary, VM Symbolic, [Overapproximation])
cutAtCallBoundary vm = do
  boundary <- callBoundaryForCurrentOp vm
  (boundary', vm', overapprox) <- continueAfterCall vm boundary
  pure (boundary', vm', overapprox)

callBoundaryForCurrentOp :: VM Symbolic -> Maybe CallBoundary
callBoundaryForCurrentOp vm = do
  op <- currentOpcode vm
  callBoundaryForOp vm op

buildFailureBranch
  :: VM Symbolic
  -> CallBoundary
  -> CallContinuationPlan
  -> SymbolicCallFailureKind
  -> Prop
  -> Word64
  -> Bool
  -> (CallBoundary, VM Symbolic, [Overapproximation], Bool)
buildFailureBranch vm boundary plan failureKind failureProp memorySize' usedWeakening =
  case failureKind of
    SymbolicStaticViolation ->
      let vm' =
            appendVmConstraints [failureProp] $
              vm { result = Just (VMFailure StateChangeWhileStatic) }
      in (boundary { outcome = CallFailedSymbolic, failureMode = Just CallFailureStopsFrame }, vm', [], usedWeakening)
    SymbolicInsufficientBalance ->
      let vm0 :: VM Symbolic
          vm0 = deterministicCallFailureVm vm plan memorySize'
          vm' = appendVmConstraints [failureProp] vm0
      in (boundary { outcome = CallFailedSymbolic, failureMode = Just CallFailureReturnsZero }, vm', [], usedWeakening)

buildContinueBranch
  :: VM Symbolic
  -> CallBoundary
  -> CallContinuationPlan
  -> Prop
  -> Word64
  -> Bool
  -> (CallBoundary, VM Symbolic, [Overapproximation], Bool)
buildContinueBranch vm boundary plan failureProp memorySize' usedWeakening =
  let (boundary', vm0, newOverapprox) = abstractCallContinuationVm vm boundary plan memorySize'
      vm' = appendVmConstraints [PNeg failureProp] vm0
  in (boundary', vm', newOverapprox, usedWeakening)

isSatLike :: SMTResult -> Bool
isSatLike = \case
  Cex {} -> True
  Unknown {} -> True
  Error {} -> True
  Qed -> False

appendVmConstraints :: [Prop] -> VM Symbolic -> VM Symbolic
appendVmConstraints extra vm =
  VM
    { result = vm.result
    , state = vm.state
    , frames = vm.frames
    , env = vm.env
    , block = vm.block
    , tx = vm.tx
    , logs = vm.logs
    , traces = vm.traces
    , pathsVisited = vm.pathsVisited
    , burned = vm.burned
    , iterations = vm.iterations
    , constraints = vm.constraints <> extra
    , config = vm.config
    , forks = vm.forks
    , currentFork = vm.currentFork
    , srcLookup = vm.srcLookup
    , labels = vm.labels
    , osEnv = vm.osEnv
    , freshVar = vm.freshVar
    , exploreDepth = vm.exploreDepth
    , keccakPreImgs = vm.keccakPreImgs
    , mergeState = vm.mergeState
    , expectedRevert = vm.expectedRevert
    }

currentOpcode :: VM Symbolic -> Maybe (GenericOp Word8)
currentOpcode vm = do
  codeBytes <- case vm.state.code of
    RuntimeCode (ConcreteRuntimeCode bs) -> Just bs
    _ -> Nothing
  let pc0 = vm.state.pc
  if pc0 < 0 || pc0 >= BS.length codeBytes
    then Nothing
    else Just (getOp (BS.index codeBytes pc0))

abstractGasStep :: VM Symbolic -> Maybe (VM Symbolic, [Overapproximation])
abstractGasStep vm = do
  op <- currentOpcode vm
  case op of
    OpGas ->
      let resultExpr = Var (T.pack ("gas_opcode_" <> show vm.freshVar))
          state' = advanceState vm.state (resultExpr : vm.state.stack)
      in Just (vm { state = state', freshVar = vm.freshVar + 1 }, [OverapproxGasOpcode])
    _ ->
      Nothing

callBoundaryForOp :: VM Symbolic -> GenericOp Word8 -> Maybe CallBoundary
callBoundaryForOp vm = \case
  OpCall ->
    case vm.state.stack of
      gasArg : toArg : valueArg : inOffsetArg : inSizeArg : outOffsetArg : outSizeArg : _ ->
        Just CallBoundary
          { opcode = CallOpCall
          , outcome = CallContinued
          , failureMode = Nothing
          , gas = gasArg
          , callee = toArg
          , value = Just valueArg
          , inputOffset = inOffsetArg
          , inputSize = inSizeArg
          , outputOffset = outOffsetArg
          , outputSize = outSizeArg
          , postReturndata = ConcreteBuf mempty
          , postStorageBase = Nothing
          , pathConstraints = vm.constraints
          }
      _ -> Nothing
  OpCallcode ->
    case vm.state.stack of
      gasArg : toArg : valueArg : inOffsetArg : inSizeArg : outOffsetArg : outSizeArg : _ ->
        Just CallBoundary
          { opcode = CallOpCallcode
          , outcome = CallContinued
          , failureMode = Nothing
          , gas = gasArg
          , callee = toArg
          , value = Just valueArg
          , inputOffset = inOffsetArg
          , inputSize = inSizeArg
          , outputOffset = outOffsetArg
          , outputSize = outSizeArg
          , postReturndata = ConcreteBuf mempty
          , postStorageBase = Nothing
          , pathConstraints = vm.constraints
          }
      _ -> Nothing
  OpDelegatecall ->
    case vm.state.stack of
      gasArg : toArg : inOffsetArg : inSizeArg : outOffsetArg : outSizeArg : _ ->
        Just CallBoundary
          { opcode = CallOpDelegatecall
          , outcome = CallContinued
          , failureMode = Nothing
          , gas = gasArg
          , callee = toArg
          , value = Nothing
          , inputOffset = inOffsetArg
          , inputSize = inSizeArg
          , outputOffset = outOffsetArg
          , outputSize = outSizeArg
          , postReturndata = ConcreteBuf mempty
          , postStorageBase = Nothing
          , pathConstraints = vm.constraints
          }
      _ -> Nothing
  OpStaticcall ->
    case vm.state.stack of
      gasArg : toArg : inOffsetArg : inSizeArg : outOffsetArg : outSizeArg : _ ->
        Just CallBoundary
          { opcode = CallOpStaticcall
          , outcome = CallContinued
          , failureMode = Nothing
          , gas = gasArg
          , callee = toArg
          , value = Nothing
          , inputOffset = inOffsetArg
          , inputSize = inSizeArg
          , outputOffset = outOffsetArg
          , outputSize = outSizeArg
          , postReturndata = ConcreteBuf mempty
          , postStorageBase = Nothing
          , pathConstraints = vm.constraints
          }
      _ -> Nothing
  _ -> Nothing

continueAfterCall :: VM Symbolic -> CallBoundary -> Maybe (CallBoundary, VM Symbolic, [Overapproximation])
continueAfterCall vm boundary = do
  let plan = callContinuationPlan vm boundary
  case deterministicPreCallOutcome vm boundary of
    Left err ->
      pure (boundary { outcome = CallFailedDeterministic, failureMode = Just CallFailureStopsFrame }, vm {result = Just (VMFailure err)}, [])
    Right (DeterministicCallFailure memorySize') ->
      pure (boundary { outcome = CallFailedDeterministic, failureMode = Just CallFailureReturnsZero }, deterministicCallFailureVm vm plan memorySize', [])
    Right (DeterministicCallContinuation memorySize') ->
      let (boundary', vm', overapprox) = abstractCallContinuationVm vm boundary plan memorySize'
      in pure (boundary', vm', overapprox)

data CallContinuationPlan = CallContinuationPlan
  { argCount :: Int
  , abstractStorage :: Bool
  , remainingStack :: [Expr EWord]
  , successVar :: Expr EWord
  , returndataBuf :: Expr Buf
  , storageBase :: Maybe (Expr EAddr)
  , extraConstraints :: [Prop]
  }

callContinuationPlan :: VM Symbolic -> CallBoundary -> CallContinuationPlan
callContinuationPlan vm boundary =
  let (argCount, abstractStorage) =
        case boundary.opcode of
          CallOpCall -> (7, True)
          CallOpCallcode -> (7, True)
          CallOpDelegatecall -> (6, True)
          CallOpStaticcall -> (6, False)
      remainingStack = drop argCount vm.state.stack
      successVar = Var (T.pack ("call_success_" <> show vm.freshVar))
      returndataBuf = AbstractBuf (T.pack ("returndata_call_" <> show (vm.freshVar + 1)))
      storageBase =
        if abstractStorage
          then Just (SymAddr (storageAbstractionName vm.state.contract (vm.freshVar + 2)))
          else Nothing
      extraConstraints = [PLEq successVar (Lit 1)]
  in
    CallContinuationPlan
      { argCount = argCount
      , abstractStorage = abstractStorage
      , remainingStack = remainingStack
      , successVar = successVar
      , returndataBuf = returndataBuf
      , storageBase = storageBase
      , extraConstraints = extraConstraints
      }

deterministicCallFailureVm :: VM Symbolic -> CallContinuationPlan -> Word64 -> VM Symbolic
deterministicCallFailureVm vm plan memorySize' =
  let state0 = vm.state
      state' =
        advanceStateWithMemory
          state0
          (Lit 0 : plan.remainingStack)
          state0.memory
          memorySize'
          (ConcreteBuf mempty)
  in vm
      { state = state'
      , result = Nothing
      }

abstractCallContinuationVm :: VM Symbolic -> CallBoundary -> CallContinuationPlan -> Word64 -> (CallBoundary, VM Symbolic, [Overapproximation])
abstractCallContinuationVm vm boundary plan memorySize' =
  let state0 = vm.state
      memory' =
        applyPostCallOutputMemory vm.freshVar state0.memory boundary.outputOffset boundary.outputSize plan.returndataBuf
      state' =
        advanceStateWithMemory state0 (plan.successVar : plan.remainingStack) memory' memorySize' plan.returndataBuf
      env' =
        if plan.abstractStorage
          then abstractPostCallWorld vm (vm.freshVar + 2)
          else vm.env
      boundary' =
        boundary
          { outcome = CallContinued
          , failureMode = Nothing
          , postReturndata = plan.returndataBuf
          , postStorageBase = plan.storageBase
          }
      vm' =
        vm
          { state = state'
          , env = env'
          , constraints = vm.constraints <> plan.extraConstraints
          , freshVar = vm.freshVar + 3
          , result = Nothing
          }
      overapprox =
        [ OverapproxCallSuccess boundary.opcode
        , OverapproxCallReturndata boundary.opcode
        ]
          <> [OverapproxCallStorage boundary.opcode | plan.abstractStorage]
  in (boundary', vm', overapprox)

data DeterministicCallOutcome
  = DeterministicCallFailure Word64
  | DeterministicCallContinuation Word64

data SymbolicCallFailureKind
  = SymbolicStaticViolation
  | SymbolicInsufficientBalance

data CallPrecheck
  = CallPrecheckDeterministicFailure Word64
  | CallPrecheckDeterministicContinuation Word64
  | CallPrecheckBranch SymbolicCallFailureKind Prop Word64

deterministicPreCallOutcome :: VM Symbolic -> CallBoundary -> Either EvmError DeterministicCallOutcome
deterministicPreCallOutcome vm boundary
  | callViolatesStaticContext vm boundary = Left StateChangeWhileStatic
  | otherwise = do
      -- This only handles pre-call outcomes we can decide locally without SMT.
      memorySize' <- applyCallMemoryAccesses vm.state.memorySize boundary.inputOffset boundary.inputSize boundary.outputOffset boundary.outputSize
      case deterministicCallFailure vm boundary of
        Just () -> Right (DeterministicCallFailure memorySize')
        Nothing -> Right (DeterministicCallContinuation memorySize')

symbolicPreCallOutcome :: VM Symbolic -> CallBoundary -> Either EvmError CallPrecheck
symbolicPreCallOutcome vm boundary = do
  memorySize' <- applyCallMemoryAccesses vm.state.memorySize boundary.inputOffset boundary.inputSize boundary.outputOffset boundary.outputSize
  case symbolicStaticViolationProp vm boundary of
    Just prop -> Right (CallPrecheckBranch SymbolicStaticViolation prop memorySize')
    Nothing ->
      case deterministicCallFailure vm boundary of
        Just () -> Right (CallPrecheckDeterministicFailure memorySize')
        Nothing ->
          case symbolicBalanceFailureProp vm boundary of
            Just prop -> Right (CallPrecheckBranch SymbolicInsufficientBalance prop memorySize')
            Nothing -> Right (CallPrecheckDeterministicContinuation memorySize')

callViolatesStaticContext :: VM Symbolic -> CallBoundary -> Bool
callViolatesStaticContext vm boundary =
  case (boundary.opcode, boundary.value) of
    (CallOpCall, Just valueExpr) -> vm.state.static && maybe False (> 0) (literalWord valueExpr)
    (CallOpCallcode, Just valueExpr) -> vm.state.static && maybe False (> 0) (literalWord valueExpr)
    _ -> False

symbolicStaticViolationProp :: VM Symbolic -> CallBoundary -> Maybe Prop
symbolicStaticViolationProp vm boundary =
  case (boundary.opcode, boundary.value) of
    (CallOpCall, Just valueExpr)
      | vm.state.static ->
          case literalWord valueExpr of
            Just 0 -> Nothing
            Just _ -> Nothing
            Nothing -> Just (valueExpr .> Lit 0)
    (CallOpCallcode, Just valueExpr)
      | vm.state.static ->
          case literalWord valueExpr of
            Just 0 -> Nothing
            Just _ -> Nothing
            Nothing -> Just (valueExpr .> Lit 0)
    _ -> Nothing

deterministicCallFailure :: VM Symbolic -> CallBoundary -> Maybe ()
deterministicCallFailure vm boundary
  | length vm.frames >= 1024 = Just ()
  | otherwise =
      case boundary.value of
        Just valueExpr
          | Just value0 <- literalWord valueExpr
          , value0 > 0
          , Just balance0 <- senderBalance vm
          , value0 > balance0 ->
              Just ()
        _ -> Nothing

senderBalance :: VM Symbolic -> Maybe W256
senderBalance vm =
  literalWord =<< senderBalanceExpr vm

senderBalanceExpr :: VM Symbolic -> Maybe (Expr EWord)
senderBalanceExpr vm =
  let sender = fromMaybe vm.state.contract vm.state.overrideCaller
  in case Map.lookup sender vm.env.contracts of
      Just contract -> Just contract.balance
      Nothing ->
        case (sender, vm.config.baseState) of
          (LitAddr _, EmptyBase) -> Just (Lit 0)
          (LitAddr _, AbstractBase) -> Just (Balance sender)
          _ -> Nothing

symbolicBalanceFailureProp :: VM Symbolic -> CallBoundary -> Maybe Prop
symbolicBalanceFailureProp vm boundary
  | length vm.frames >= 1024 = Nothing
  | otherwise =
      case (boundary.value, senderBalanceExpr vm) of
        (Just valueExpr, Just balanceExpr) ->
          case (literalWord valueExpr, literalWord balanceExpr) of
            (Just 0, _) -> Nothing
            (Just value0, Just balance0)
              | value0 > balance0 -> Nothing
              | otherwise -> Nothing
            _ -> Just (valueExpr .> balanceExpr)
        _ -> Nothing

literalWord :: Expr EWord -> Maybe W256
literalWord = \case
  Lit value0 -> Just value0
  _ -> Nothing

applyCallMemoryAccesses :: Word64 -> Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord -> Either EvmError Word64
applyCallMemoryAccesses memorySize0 inOffset inSize outOffset outSize = do
  memorySize1 <- applyMemoryAccessRange memorySize0 inOffset inSize
  applyMemoryAccessRange memorySize1 outOffset outSize

applyMemoryAccessRange :: Word64 -> Expr EWord -> Expr EWord -> Either EvmError Word64
applyMemoryAccessRange currentSize _ (Lit 0) = Right currentSize
applyMemoryAccessRange currentSize (Lit offs) (Lit sz) =
  let word64Limit = fromIntegral (maxBound :: Word64) :: W256
  in if offs > word64Limit || sz > word64Limit
      then Left IllegalOverflow
      else
        let offs64 = fromIntegral offs :: Word64
            sz64 = fromIntegral sz :: Word64
        in if offs64 + sz64 < sz64 || offs64 >= 0x0fffffff || sz64 >= 0x0fffffff
            then Left IllegalOverflow
            else Right (roundUpToWordBoundary (max currentSize (offs64 + sz64)))
applyMemoryAccessRange currentSize _ _ = Right currentSize

roundUpToWordBoundary :: Word64 -> Word64
roundUpToWordBoundary size =
  32 * ((size + 31) `div` 32)

advanceStateWithMemory :: FrameState Symbolic -> [Expr EWord] -> Memory -> Word64 -> Expr Buf -> FrameState Symbolic
advanceStateWithMemory state0 stack' memory' memorySize' returndata' =
  FrameState
    { contract = state0.contract
    , codeContract = state0.codeContract
    , code = state0.code
    , pc = state0.pc + 1
    , stack = stack'
    , memory = memory'
    , memorySize = memorySize'
    , returndata = returndata'
    , calldata = state0.calldata
    , callvalue = state0.callvalue
    , caller = state0.caller
    , gas = state0.gas
    , static = state0.static
    , overrideCaller = state0.overrideCaller
    , resetCaller = state0.resetCaller
    }

applyPostCallOutputMemory :: Int -> Memory -> Expr EWord -> Expr EWord -> Expr Buf -> Memory
applyPostCallOutputMemory freshVar memory outOffset outSize returndataBuf =
  case outSize of
    Lit 0 -> memory
    _ ->
      case memory of
        SymbolicMemory mem ->
          SymbolicMemory (CopySlice (Lit 0) outOffset outSize returndataBuf mem)
        ConcreteMemory _ ->
          SymbolicMemory (AbstractBuf (T.pack ("memory_after_call_" <> show freshVar)))

abstractPostCallWorld :: VM Symbolic -> Int -> Env
abstractPostCallWorld vm abstractionId =
  Env
    { contracts = Map.mapWithKey abstractOne vm.env.contracts
    , chainId = vm.env.chainId
    , freshAddresses = vm.env.freshAddresses
    , freshGasVals = vm.env.freshGasVals
    }
  where
    selfAddr = vm.state.contract
    abstractOne addr contract =
      let freshBalance = Var (balanceAbstractionName abstractionId addr)
          abstractCode = UnknownCode addr
          contract0 =
            contract
              { balance = freshBalance
              , nonce =
                  if addr == selfAddr
                    then Nothing
                    else contract.nonce
              , code =
                  if addr == selfAddr
                    then abstractCode
                    else abstractCode
              , codehash = hashcode abstractCode
              }
      in if addr == selfAddr
          then
            let freshStoreAddr = SymAddr (storageAbstractionName addr abstractionId)
                baseStorage = AbstractStore freshStoreAddr Nothing
            in contract0
                { storage = baseStorage
                , tStorage = baseStorage
                , origStorage = contract.origStorage
                }
          else contract0

storageAbstractionName :: Expr EAddr -> Int -> T.Text
storageAbstractionName contractAddr abstractionId =
  "storage_after_call_"
    <> T.pack (show abstractionId)
    <> "_"
    <> addrStem contractAddr
  where
    addrStem :: Expr EAddr -> T.Text
    addrStem = \case
      SymAddr name -> name
      LitAddr addr -> "lit_" <> T.pack (show addr)
      GVar _ -> "gvar"

balanceAbstractionName :: Int -> Expr EAddr -> T.Text
balanceAbstractionName abstractionId addr =
  "balance_after_call_"
    <> T.pack (show abstractionId)
    <> "_"
    <> addrStem addr
  where
    addrStem :: Expr EAddr -> T.Text
    addrStem = \case
      SymAddr name -> name
      LitAddr addr0 -> "lit_" <> T.pack (show addr0)
      GVar _ -> "gvar"

abstractPostCallWorldStep :: VM Symbolic -> Maybe (VM Symbolic, [Overapproximation])
abstractPostCallWorldStep vm = do
  epoch <- postCallWorldEpoch vm
  op <- currentOpcode vm
  case op of
    OpExtcodesize ->
      case vm.state.stack of
        _addr : xs ->
          let resultExpr = Var (extcodeMetricName "size" epoch vm.freshVar)
              state' = advanceState vm.state (resultExpr : xs)
          in Just (vm {state = state', freshVar = vm.freshVar + 1}, [OverapproxPostCallExtcodesize])
        _ -> Nothing
    OpExtcodehash ->
      case vm.state.stack of
        _addr : xs ->
          let resultExpr = Var (extcodeMetricName "hash" epoch vm.freshVar)
              state' = advanceState vm.state (resultExpr : xs)
          in Just (vm {state = state', freshVar = vm.freshVar + 1}, [OverapproxPostCallExtcodehash])
        _ -> Nothing
    OpExtcodecopy ->
      case vm.state.stack of
        _addr : memOffset : codeOffset : copySize : xs ->
          let state0 = vm.state
          in case extcodecopyMemoryUpdate epoch vm.freshVar state0.memory state0.memorySize memOffset codeOffset copySize of
              Left err ->
                Just (vm {result = Just (VMFailure err)}, [])
              Right ExtcodecopyMemoryUpdate {newMemory, newMemorySize, usedCoarseAbstraction} ->
                let state' =
                      FrameState
                        { contract = state0.contract
                        , codeContract = state0.codeContract
                        , code = state0.code
                        , pc = state0.pc + 1
                        , stack = xs
                        , memory = newMemory
                        , memorySize = newMemorySize
                        , returndata = state0.returndata
                        , calldata = state0.calldata
                        , callvalue = state0.callvalue
                        , caller = state0.caller
                        , gas = state0.gas
                        , static = state0.static
                        , overrideCaller = state0.overrideCaller
                        , resetCaller = state0.resetCaller
                        }
                    overapprox = [OverapproxCoarseExtcodecopyMemory | usedCoarseAbstraction]
                in Just (vm {state = state', freshVar = vm.freshVar + 1}, overapprox)
        _ -> Nothing
    OpMsize
      | isAbstractPostCallMemory vm.state.memory ->
          let resultExpr = Var (T.pack ("msize_after_extcodecopy_" <> show vm.freshVar))
              state' = advanceState vm.state (resultExpr : vm.state.stack)
          in Just (vm {state = state', freshVar = vm.freshVar + 1}, [])
    _ -> Nothing

advanceState :: FrameState Symbolic -> [Expr EWord] -> FrameState Symbolic
advanceState state0 stack' =
  FrameState
    { contract = state0.contract
    , codeContract = state0.codeContract
    , code = state0.code
    , pc = state0.pc + 1
    , stack = stack'
    , memory = state0.memory
    , memorySize = state0.memorySize
    , returndata = state0.returndata
    , calldata = state0.calldata
    , callvalue = state0.callvalue
    , caller = state0.caller
    , gas = state0.gas
    , static = state0.static
    , overrideCaller = state0.overrideCaller
    , resetCaller = state0.resetCaller
    }

isAbstractPostCallMemory :: Memory -> Bool
isAbstractPostCallMemory = \case
  SymbolicMemory (AbstractBuf name) -> "memory_after_extcodecopy_" `T.isPrefixOf` name
  _ -> False

data ExtcodecopyMemoryUpdate = ExtcodecopyMemoryUpdate
  { newMemory :: Memory
  , newMemorySize :: Word64
  , usedCoarseAbstraction :: Bool
  }

extcodecopyMemoryUpdate
  :: Int
  -> Int
  -> Memory
  -> Word64
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> Either EvmError ExtcodecopyMemoryUpdate
extcodecopyMemoryUpdate epoch freshVar memory0 memorySize0 memOffset codeOffset copySize =
  case copySize of
    Lit 0 ->
      Right
        ExtcodecopyMemoryUpdate
          { newMemory = memory0
          , newMemorySize = memorySize0
          , usedCoarseAbstraction = False
          }
    Lit size ->
      case memOffset of
        Lit dstOffset ->
          case concreteMemorySizeAfterWrite memorySize0 dstOffset size of
            Left err -> Left err
            Right memorySize1 ->
              Right
                ExtcodecopyMemoryUpdate
                  { newMemory = applyPreciseExtcodecopyMemory epoch freshVar memory0 memOffset codeOffset copySize
                  , newMemorySize = memorySize1
                  , usedCoarseAbstraction = False
                  }
        _ ->
          Right
            ExtcodecopyMemoryUpdate
              { newMemory = coarseExtcodecopyMemory freshVar
              , newMemorySize = maxBound
              , usedCoarseAbstraction = True
              }
    _ ->
      Right
        ExtcodecopyMemoryUpdate
          { newMemory = coarseExtcodecopyMemory freshVar
          , newMemorySize = maxBound
          , usedCoarseAbstraction = True
          }

applyPreciseExtcodecopyMemory
  :: Int
  -> Int
  -> Memory
  -> Expr EWord
  -> Expr EWord
  -> Expr EWord
  -> Memory
applyPreciseExtcodecopyMemory epoch freshVar memory0 memOffset codeOffset copySize =
      let srcBuf = AbstractBuf (extcodecopyBufferName epoch freshVar)
  in case memory0 of
      SymbolicMemory mem ->
        SymbolicMemory (Expr.copySlice codeOffset memOffset copySize srcBuf mem)
      ConcreteMemory _ ->
        coarseExtcodecopyMemory freshVar

coarseExtcodecopyMemory :: Int -> Memory
coarseExtcodecopyMemory freshVar =
  SymbolicMemory (AbstractBuf (T.pack ("memory_after_extcodecopy_" <> show freshVar)))

extcodecopyBufferName :: Int -> Int -> T.Text
extcodecopyBufferName epoch freshVar =
  "extcodecopy_data_"
    <> T.pack (show epoch)
    <> "_"
    <> T.pack (show freshVar)

concreteMemorySizeAfterWrite :: Word64 -> W256 -> W256 -> Either EvmError Word64
concreteMemorySizeAfterWrite oldSize dstOffset size =
  case (toWord64 dstOffset, toWord64 size) of
    (Just dstOffset64, Just size64) ->
      if dstOffset64 + size64 < size64
        then Left IllegalOverflow
        else if dstOffset64 >= 0x0fffffff || size64 >= 0x0fffffff
          then Left IllegalOverflow
          else Right (roundUpMemorySize (max oldSize (dstOffset64 + size64)))
    _ ->
      Left IllegalOverflow

roundUpMemorySize :: Word64 -> Word64
roundUpMemorySize n = 32 * ceilDiv n 32

postCallWorldEpoch :: VM Symbolic -> Maybe Int
postCallWorldEpoch vm = do
  contract <- Map.lookup vm.state.contract vm.env.contracts
  case contract.storage of
    AbstractStore (SymAddr name) Nothing ->
      parseStorageEpoch name
    _ -> Nothing

parseStorageEpoch :: T.Text -> Maybe Int
parseStorageEpoch name = do
  rest <- T.stripPrefix "storage_after_call_" name
  let epochText = T.takeWhile (/= '_') rest
  case reads (T.unpack epochText) of
    [(n, "")] -> Just n
    _ -> Nothing

extcodeMetricName :: String -> Int -> Int -> T.Text
extcodeMetricName metric epoch fresh =
  T.pack (metric <> "_after_call_" <> show epoch <> "_" <> show fresh)
