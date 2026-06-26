{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Control.Monad (unless, when)
import Control.Monad.ST (stToIO)
import Data.Aeson (Value(..), object, (.=), encode, toJSON)
import Data.Bits ((.&.), shiftL, (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.Char (digitToInt, isHexDigit)
import Data.List (find, stripPrefix)
import Data.Map qualified as Map
import Data.Text qualified as T
import EVM.Expr qualified as Expr
import EVM.Effects qualified as Effects
import EVM.Format qualified as Format
import EVM.Op (intToOpName)
import EVM.SymExec qualified as SymExec
import EVM.Types
import SymCheck
import System.Environment (getArgs)
import System.Exit (die)

data CliOptions = CliOptions
  { cliCode :: ByteString
  , cliPc :: Int
  , cliFuel :: Int
  , cliTargetPc :: Maybe Int
  , cliStack :: [Expr EWord]
  , cliMemory :: Expr Buf
  , cliCalldata :: Expr Buf
  , cliReturndata :: Expr Buf
  , cliAddress :: Expr EAddr
  , cliCodeAddress :: Expr EAddr
  , cliCaller :: Expr EAddr
  , cliOverrideCaller :: Maybe (Expr EAddr)
  , cliOrigin :: Expr EAddr
  , cliCoinbase :: Expr EAddr
  , cliCallvalue :: Expr EWord
  , cliBlockNumber :: Expr EWord
  , cliTimestamp :: Expr EWord
  , cliStatic :: Bool
  , cliBaseState :: BaseState
  , cliStores :: Map.Map W256 W256
  , cliPreconditions :: [Condition]
  , cliPostconditions :: [Condition]
  , cliAllowSmtWeakening :: Bool
  , cliNotifySmtWeakening :: Bool
  , cliFailOnOverapproximation :: Bool
  , cliJsonOutput :: Bool
  , cliTraceOpcodes :: Bool
  }

defaultCliOptions :: Either String CliOptions
defaultCliOptions = do
  codeBytes <- parseHexBytes "00"
  pure CliOptions
    { cliCode = codeBytes
    , cliPc = 0
    , cliFuel = 32
    , cliTargetPc = Nothing
    , cliStack = []
    , cliMemory = AbstractBuf "memory"
    , cliCalldata = AbstractBuf "calldata"
    , cliReturndata = ConcreteBuf mempty
    , cliAddress = SymAddr "entrypoint"
    , cliCodeAddress = SymAddr "entrypoint"
    , cliCaller = SymAddr "caller"
    , cliOverrideCaller = Nothing
    , cliOrigin = SymAddr "origin"
    , cliCoinbase = SymAddr "coinbase"
    , cliCallvalue = Lit 0
    , cliBlockNumber = Lit 0
    , cliTimestamp = Lit 0
    , cliStatic = False
    , cliBaseState = AbstractBase
    , cliStores = Map.empty
    , cliPreconditions = []
    , cliPostconditions = []
    , cliAllowSmtWeakening = True
    , cliNotifySmtWeakening = True
    , cliFailOnOverapproximation = False
    , cliJsonOutput = False
    , cliTraceOpcodes = False
    }

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["smoke-all"] -> runSmokeAll
    [cmd]
      | Just action <- lookup cmd smokeCommands -> action
    "run" : rest -> either die runCli =<< pure (parseCli rest)
    _ -> putStrLn usage

runSmokeAdd :: IO ()
runSmokeAdd = smoke "smoke-add" $ do
  codeBytes <- smokeEither "smoke-add" $ parseHexBytes "600160020100"
  let baseSpec = defaultMidpointSpec codeBytes
      spec =
        MidpointSpec
          { code = baseSpec.code
          , pc = 2
          , stack = [Lit 0x1]
          , memory = baseSpec.memory
          , memorySize = baseSpec.memorySize
          , storage = baseSpec.storage
          , transientStorage = baseSpec.transientStorage
          , originalStorage = baseSpec.originalStorage
          , calldata = baseSpec.calldata
          , returndata = baseSpec.returndata
          , constraints = baseSpec.constraints
          , address = baseSpec.address
          , codeAddress = baseSpec.codeAddress
          , caller = baseSpec.caller
          , overrideCaller = baseSpec.overrideCaller
          , origin = baseSpec.origin
          , coinbase = baseSpec.coinbase
          , callvalue = baseSpec.callvalue
          , blockNumber = baseSpec.blockNumber
          , timestamp = baseSpec.timestamp
          , static = baseSpec.static
          , baseState = baseSpec.baseState
          }
      runSpec =
        SegmentRunSpec
          { fuel = 3
          , targetPc = Nothing
          , config = Effects.defaultConfig
          , smtPolicy = defaultSmtQueryPolicy
          }
  results <- runSmokeSegment "smoke-add" runSpec spec
  case results of
    [result]
      | Lit 0x3 : _ <- result.finalVm.state.stack ->
          pure ()
      | otherwise ->
          smokeFail "smoke-add" $ "unexpected final stack " <> show result.finalVm.state.stack
    _ -> smokeFail "smoke-add" $ "expected exactly one result, got " <> show (length results)

runSmokeTargetPc :: IO ()
runSmokeTargetPc = smoke "smoke-target-pc" $ do
  codeBytes <- smokeEither "smoke-target-pc" $ parseHexBytes "600160020100"
  let baseSpec :: MidpointSpec
      baseSpec = defaultMidpointSpec codeBytes
      runSpec = smokeRunSpec 5 (Just 4)
  results <- runSmokeSegment "smoke-target-pc" runSpec baseSpec
  result <- expectSingleResult "smoke-target-pc" results
  case result.stopReason of
    StoppedAtTargetPc 4 -> pure ()
    other -> smokeFail "smoke-target-pc" $ "expected target-pc stop, got " <> show other
  smokeAssert "smoke-target-pc" (result.finalVm.state.pc == 4) $
    "expected final pc 4, got " <> show result.finalVm.state.pc
  smokeAssert "smoke-target-pc" (take 2 result.finalVm.state.stack == [Lit 0x2, Lit 0x1]) $
    "unexpected stack at target pc: " <> show result.finalVm.state.stack

runSmokePostconditions :: IO ()
runSmokePostconditions = smoke "smoke-postconditions" $ do
  codeBytes <- smokeEither "smoke-postconditions" $ parseHexBytes "600160020100"
  let baseSpec :: MidpointSpec
      baseSpec = defaultMidpointSpec codeBytes
      spec :: MidpointSpec
      spec =
        setMidpointStack [Lit 0x1] $
          setMidpointPc 2 baseSpec
      runSpec = smokeRunSpec 3 Nothing
      conditions =
        [ WordCondition CmpEq (StackTerm 0) (LitTerm 0x3)
        , StopCondition StopSuccess
        , SmtCondition CmpEq SmtExact
        , OverapproxCondition CmpEq OverapproxNone
        ]
  results <- runSmokeSegment "smoke-postconditions" runSpec spec
  reports <- checkPostconditionsWithSolvers runSpec conditions results
  expectSingleBranchStatuses "smoke-postconditions" reports (replicate (length conditions) PostconditionQed)

runSmokeCallMetadata :: IO ()
runSmokeCallMetadata = smoke "smoke-call-metadata" $ do
  codeBytes <- smokeEither "smoke-call-metadata" $ parseHexBytes "f100"
  let baseSpec :: MidpointSpec
      baseSpec = defaultMidpointSpec codeBytes
      spec :: MidpointSpec
      spec =
        setMidpointStack
          [ Lit 0x5
          , Lit 0x1234
          , Lit 0
          , Lit 0
          , Lit 0
          , Lit 0
          , Lit 0
          ]
          baseSpec
      runSpec = smokeRunSpec 2 Nothing
      conditions =
        [ WordCondition CmpEq CallCountTerm (LitTerm 0x1)
        , CallOpcodeCondition CmpEq 0 CallOpCall
        , CallOutcomeCondition CmpEq 0 CallContinued
        , WordCondition CmpEq (CallFieldTerm 0 CallToField) (LitTerm 0x1234)
        , OverapproxCondition CmpEq OverapproxSome
        ]
  results <- runSmokeSegment "smoke-call-metadata" runSpec spec
  result <- expectSingleResult "smoke-call-metadata" results
  smokeAssert "smoke-call-metadata" (length result.callBoundaries == 1) $
    "expected one call boundary, got " <> show (length result.callBoundaries)
  reports <- checkPostconditionsWithSolvers runSpec conditions results
  expectSingleBranchStatuses "smoke-call-metadata" reports (replicate (length conditions) PostconditionQed)

runSmokeStaticCallSplit :: IO ()
runSmokeStaticCallSplit = smoke "smoke-static-call-split" $ do
  codeBytes <- smokeEither "smoke-static-call-split" $ parseHexBytes "f100"
  let baseSpec :: MidpointSpec
      baseSpec = defaultMidpointSpec codeBytes
      spec :: MidpointSpec
      spec =
        setMidpointStatic True $
          setMidpointStack
            [ Lit 0x5
            , Lit 0x1234
            , Var "call_value"
            , Lit 0
            , Lit 0
            , Lit 0
            , Lit 0
            ]
            baseSpec
      runSpec = smokeRunSpec 2 Nothing
  results <- runSmokeSegment "smoke-static-call-split" runSpec spec
  smokeAssert "smoke-static-call-split" (length results == 2) $
    "expected two branches, got " <> show (length results)
  let outcomes = fmap callBranchSummary results
  smokeAssert "smoke-static-call-split" ((CallFailedSymbolic, Just CallFailureStopsFrame) `elem` outcomes) $
    "missing symbolic static-failure branch: " <> show outcomes
  smokeAssert "smoke-static-call-split" ((CallContinued, Nothing) `elem` outcomes) $
    "missing continued branch: " <> show outcomes

runSmokeBalanceSplit :: IO ()
runSmokeBalanceSplit = smoke "smoke-balance-split" $ do
  codeBytes <- smokeEither "smoke-balance-split" $ parseHexBytes "f100"
  let baseSpec :: MidpointSpec
      baseSpec = defaultMidpointSpec codeBytes
      spec :: MidpointSpec
      spec =
        setMidpointBaseState AbstractBase $
          setMidpointOverrideCaller (Just (LitAddr 0xdead)) $
            setMidpointStack
              [ Lit 0x5
              , Lit 0x1234
              , Var "call_value"
              , Lit 0
              , Lit 0
              , Lit 0
              , Lit 0
              ]
              baseSpec
      runSpec = smokeRunSpec 2 Nothing
  results <- runSmokeSegment "smoke-balance-split" runSpec spec
  smokeAssert "smoke-balance-split" (length results == 2) $
    "expected two branches, got " <> show (length results)
  let outcomes = fmap callBranchSummary results
  smokeAssert "smoke-balance-split" ((CallFailedSymbolic, Just CallFailureReturnsZero) `elem` outcomes) $
    "missing symbolic insufficient-balance branch: " <> show outcomes
  smokeAssert "smoke-balance-split" ((CallContinued, Nothing) `elem` outcomes) $
    "missing continued branch: " <> show outcomes

runSmokeSmtWeakening :: IO ()
runSmokeSmtWeakening = smoke "smoke-smt-weakening" $ do
  codeBytes <- smokeEither "smoke-smt-weakening" $ parseHexBytes "f100"
  let baseSpec :: MidpointSpec
      baseSpec = defaultMidpointSpec codeBytes
      spec :: MidpointSpec
      spec =
        setMidpointStack
          [ Lit 0x5
          , Lit 0x1234
          , Lit 0
          , Lit 0
          , Lit 0
          , Lit 0
          , Var "out_size"
          ]
          baseSpec
      runSpec = smokeRunSpec 2 Nothing
      conditions =
        [WordCondition CmpEq (BufferWordTerm MemoryBuf (LitTerm 0)) (LitTerm 0)]
  results <- runSmokeSegment "smoke-smt-weakening" runSpec spec
  reports <- checkPostconditionsWithSolvers runSpec conditions results
  expectSingleBranchStatus "smoke-smt-weakening" reports $ \case
    [PostconditionUnknown _] -> True
    _ -> False

runSmokeAll :: IO ()
runSmokeAll =
  mapM_ snd smokeCommands

smokeCommands :: [(String, IO ())]
smokeCommands =
  [ ("smoke-add", runSmokeAdd)
  , ("smoke-target-pc", runSmokeTargetPc)
  , ("smoke-postconditions", runSmokePostconditions)
  , ("smoke-call-metadata", runSmokeCallMetadata)
  , ("smoke-static-call-split", runSmokeStaticCallSplit)
  , ("smoke-balance-split", runSmokeBalanceSplit)
  , ("smoke-smt-weakening", runSmokeSmtWeakening)
  ]

smoke :: String -> IO () -> IO ()
smoke name action = do
  action
  putStrLn $ name <> ": ok"

smokeFail :: String -> String -> IO a
smokeFail name msg =
  die $ name <> ": " <> msg

smokeEither :: String -> Either String a -> IO a
smokeEither name =
  either (smokeFail name) pure

smokeAssert :: String -> Bool -> String -> IO ()
smokeAssert name ok msg =
  unless ok (smokeFail name msg)

smokeRunSpec :: Int -> Maybe Int -> SegmentRunSpec
smokeRunSpec fuel0 targetPc0 =
  SegmentRunSpec
    { fuel = fuel0
    , targetPc = targetPc0
    , config = Effects.defaultConfig
    , smtPolicy = defaultSmtQueryPolicy
    }

setMidpointPc :: Int -> MidpointSpec -> MidpointSpec
setMidpointPc pc0 spec =
  MidpointSpec
    { code = spec.code
    , pc = pc0
    , stack = spec.stack
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

setMidpointStack :: [Expr EWord] -> MidpointSpec -> MidpointSpec
setMidpointStack stack0 spec =
  MidpointSpec
    { code = spec.code
    , pc = spec.pc
    , stack = stack0
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

setMidpointStatic :: Bool -> MidpointSpec -> MidpointSpec
setMidpointStatic static0 spec =
  MidpointSpec
    { code = spec.code
    , pc = spec.pc
    , stack = spec.stack
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
    , static = static0
    , baseState = spec.baseState
    }

setMidpointOverrideCaller :: Maybe (Expr EAddr) -> MidpointSpec -> MidpointSpec
setMidpointOverrideCaller overrideCaller0 spec =
  MidpointSpec
    { code = spec.code
    , pc = spec.pc
    , stack = spec.stack
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
    , overrideCaller = overrideCaller0
    , origin = spec.origin
    , coinbase = spec.coinbase
    , callvalue = spec.callvalue
    , blockNumber = spec.blockNumber
    , timestamp = spec.timestamp
    , static = spec.static
    , baseState = spec.baseState
    }

setMidpointBaseState :: BaseState -> MidpointSpec -> MidpointSpec
setMidpointBaseState baseState0 spec =
  MidpointSpec
    { code = spec.code
    , pc = spec.pc
    , stack = spec.stack
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
    , baseState = baseState0
    }

runSmokeSegment :: String -> SegmentRunSpec -> MidpointSpec -> IO [SegmentResult]
runSmokeSegment name runSpec spec = do
  paddedSpec <- smokeEither name $ autoFillInitialStackDepth runSpec spec
  vm <- stToIO $ makeMidpointVM paddedSpec
  runSegmentWithSolvers runSpec vm

expectSingleResult :: String -> [SegmentResult] -> IO SegmentResult
expectSingleResult name = \case
  [result] -> pure result
  results -> smokeFail name $ "expected exactly one result, got " <> show (length results)

expectSingleBranchStatuses :: String -> [[PostconditionReport]] -> [PostconditionStatus] -> IO ()
expectSingleBranchStatuses name reports expected =
  expectSingleBranchStatus name reports (== expected)

expectSingleBranchStatus :: String -> [[PostconditionReport]] -> ([PostconditionStatus] -> Bool) -> IO ()
expectSingleBranchStatus name reports predicate =
  case fmap (fmap (.status)) reports of
    [statuses] ->
      smokeAssert name (predicate statuses) $
        "unexpected postcondition statuses: " <> show (fmap renderPostconditionStatus statuses)
    _ ->
      smokeFail name $ "expected exactly one report branch, got " <> show (length reports)

callBranchSummary :: SegmentResult -> (CallBoundaryOutcome, Maybe CallFailureMode)
callBranchSummary result =
  case result.callBoundaries of
    [boundary] -> (boundary.outcome, boundary.failureMode)
    boundaries ->
      error $ "expected one call boundary per branch, got " <> show (length boundaries)

runCli :: CliOptions -> IO ()
runCli opts = do
  let storageExpr =
        if Map.null opts.cliStores
          then AbstractStore opts.cliAddress Nothing
          else ConcreteStore opts.cliStores
      spec0 =
        (defaultMidpointSpec opts.cliCode)
          { pc = opts.cliPc
          , stack = opts.cliStack
          , memory = opts.cliMemory
          , storage = storageExpr
          , transientStorage = storageExpr
          , originalStorage = storageExpr
          , calldata = opts.cliCalldata
          , returndata = opts.cliReturndata
          , address = opts.cliAddress
          , codeAddress = opts.cliCodeAddress
          , caller = opts.cliCaller
          , overrideCaller = opts.cliOverrideCaller
          , origin = opts.cliOrigin
          , coinbase = opts.cliCoinbase
          , callvalue = opts.cliCallvalue
          , blockNumber = opts.cliBlockNumber
          , timestamp = opts.cliTimestamp
          , static = opts.cliStatic
          , baseState = opts.cliBaseState
          }
      runSpec =
        SegmentRunSpec
          { fuel = opts.cliFuel
          , targetPc = opts.cliTargetPc
          , config = Effects.defaultConfig
          , smtPolicy =
              SmtQueryPolicy
                { allowWeakening = opts.cliAllowSmtWeakening
                , notifyWeakening = opts.cliNotifySmtWeakening
                }
          }
  initialConstraints <- either die pure $ traverse (conditionToPreProp spec0) opts.cliPreconditions
  let spec =
        MidpointSpec
          { code = spec0.code
          , pc = spec0.pc
          , stack = spec0.stack
          , memory = spec0.memory
          , memorySize = spec0.memorySize
          , storage = spec0.storage
          , transientStorage = spec0.transientStorage
          , originalStorage = spec0.originalStorage
          , calldata = spec0.calldata
          , returndata = spec0.returndata
          , constraints = spec0.constraints <> initialConstraints
          , address = spec0.address
          , codeAddress = spec0.codeAddress
          , caller = spec0.caller
          , overrideCaller = spec0.overrideCaller
          , origin = spec0.origin
          , coinbase = spec0.coinbase
          , callvalue = spec0.callvalue
          , blockNumber = spec0.blockNumber
          , timestamp = spec0.timestamp
          , static = spec0.static
          , baseState = spec0.baseState
          }
  paddedSpec <- either die pure $ autoFillInitialStackDepth runSpec spec
  vm <- stToIO $ makeMidpointVM paddedSpec
  results <- runSegmentWithSolvers runSpec vm
  when opts.cliFailOnOverapproximation $
    failIfOverapproximated results
  reports <-
    case opts.cliPostconditions of
      [] -> pure Nothing
      _ -> Just <$> checkPostconditionsWithSolvers runSpec opts.cliPostconditions results
  if opts.cliJsonOutput
    then emitJsonOutput opts.cliTraceOpcodes results reports
    else do
      printSegmentResults opts.cliTraceOpcodes results
      maybe (pure ()) printPostconditionReports reports

unlessNull :: [a] -> IO () -> IO ()
unlessNull xs action =
  case xs of
    [] -> pure ()
    _ -> action

printSegmentResult :: Bool -> SegmentResult -> IO ()
printSegmentResult includeTraceOpcodes result = do
  frozenVm <- stToIO $ SymExec.freezeVM result.finalVm
  let currentContractState = lookupRunningContract frozenVm
  putStrLn $ "steps: " <> show result.steps
  putStrLn $ "stop:  " <> renderStop result.stopReason
  putStrLn $ "pc:    " <> show frozenVm.state.pc
  putStrLn $ "pc-trace: " <> renderPcTrace result.pcTrace
  when includeTraceOpcodes $
    putStrLn $ "pc-trace-opcodes: " <> renderPcTraceOpcodes frozenVm.state.code result.pcTrace
  putStrLn $ "stack: " <> renderWordExprList frozenVm.state.stack
  putStrLn $ "memory: " <> renderMemory frozenVm.state.memory
  putStrLn $ "returndata: " <> renderBufExpr frozenVm.state.returndata
  putStrLn $ "constraints: " <> show (length frozenVm.constraints)
  unlessNull frozenVm.constraints $ do
    putStrLn "path-constraints:"
    mapM_ (\prop0 -> putStrLn $ "  " <> renderProp prop0) frozenVm.constraints
  case currentContractState of
    Just contract -> do
      putStrLn $ "storage: " <> renderStorageExpr contract.storage
      putStrLn $ "transient-storage: " <> renderStorageExpr contract.tStorage
      putStrLn $ "original-storage: " <> renderStorageExpr contract.origStorage
      putStrLn $ "balance: " <> renderWordExpr contract.balance
    Nothing ->
      putStrLn "contract-state: <missing>"
  unlessNull (renderBalances frozenVm) $ do
    putStrLn "balances:"
    mapM_ (\line -> putStrLn $ "  " <> line) (renderBalances frozenVm)
  putStrLn $ "smt:   " <> if result.usedWeakenedSmt then "weakened" else "exact"
  putStrLn $ "overapprox: " <> renderOverapproximationSummary result.overapproximations
  unlessNull result.callBoundaries $
    mapM_ printIndexedCallBoundary (zip [(1 :: Int) ..] result.callBoundaries)
  case frozenVm.result of
    Just vmResult -> putStrLn $ "vm-result: " <> renderVmResult vmResult
    Nothing -> pure ()

printSegmentResults :: Bool -> [SegmentResult] -> IO ()
printSegmentResults _ [] = putStrLn "no results"
printSegmentResults includeTraceOpcodes [result] = printSegmentResult includeTraceOpcodes result
printSegmentResults includeTraceOpcodes results =
  mapM_ printOne (zip [(1 :: Int) ..] results)
  where
    printOne (idx, result) = do
      putStrLn $ "branch: " <> show idx
      printSegmentResult includeTraceOpcodes result

printPostconditionReports :: [[PostconditionReport]] -> IO ()
printPostconditionReports [] = pure ()
printPostconditionReports [reports] = do
  putStrLn "postconditions:"
  mapM_ printPostconditionReport reports
printPostconditionReports reportsByBranch =
  mapM_ printBranchReports (zip [(1 :: Int) ..] reportsByBranch)
  where
    printBranchReports (idx, reports) = do
      putStrLn $ "postconditions branch " <> show idx <> ":"
      mapM_ printPostconditionReport reports

printPostconditionReport :: PostconditionReport -> IO ()
printPostconditionReport PostconditionReport {..} =
  putStrLn $
    "  "
      <> renderCondition condition
      <> " => "
      <> renderPostconditionStatus status

renderPostconditionStatus :: PostconditionStatus -> String
renderPostconditionStatus = \case
  PostconditionQed -> "qed"
  PostconditionQedWithAbstraction -> "qed (weakened)"
  PostconditionCex Nothing -> "cex"
  PostconditionCex (Just details) -> "cex (" <> details <> ")"
  PostconditionUnknown msg -> "unknown (" <> msg <> ")"
  PostconditionError msg -> "error (" <> msg <> ")"

renderCondition :: Condition -> String
renderCondition = \case
  WordCondition op lhs rhs ->
    renderWordTerm lhs <> renderCompareOp op <> renderWordTerm rhs
  PcCondition op rhs ->
    "pc" <> renderCompareOp op <> show rhs
  StopCondition pred0 ->
    "stop==" <> renderStopPredicate pred0
  SmtCondition op smtMode ->
    "smt" <> renderCompareOp op <> renderSmtMode smtMode
  OverapproxCondition op overapproxMode ->
    "overapprox" <> renderCompareOp op <> renderOverapproxMode overapproxMode
  CallOutcomeCondition op idx outcome ->
    "call[" <> show idx <> "].outcome" <> renderCompareOp op <> renderCallBoundaryOutcome outcome
  CallFailureModeCondition op idx failureMode ->
    "call[" <> show idx <> "].failure-mode" <> renderCompareOp op <> renderCallFailureMode failureMode
  CallOpcodeCondition op idx opcode ->
    "call[" <> show idx <> "].opcode" <> renderCompareOp op <> renderCallOpcodeAtom opcode

renderWordTerm :: WordTerm -> String
renderWordTerm = \case
  StackTerm idx -> "stack[" <> show idx <> "]"
  VarTerm name -> "var:" <> T.unpack name
  LitTerm val -> show val
  AddressValueTerm addrExpr -> renderAddrExpr addrExpr
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
    "call[" <> show idx <> "]." <> renderCallField field
  CallReturndataWordTerm idx offset ->
    "call[" <> show idx <> "].returndata[" <> renderWordTerm offset <> "]"
  BufferWordTerm bufRef offset ->
    renderBufferRef bufRef <> "[" <> renderWordTerm offset <> "]"
  BufferLengthTerm bufRef ->
    "len(" <> renderBufferRef bufRef <> ")"
  StorageTerm slot ->
    "storage[" <> renderWordTerm slot <> "]"

renderCompareOp :: CompareOp -> String
renderCompareOp = \case
  CmpEq -> "=="
  CmpNe -> "!="
  CmpLt -> "<"
  CmpLe -> "<="
  CmpGt -> ">"
  CmpGe -> ">="

renderStopPredicate :: StopPredicate -> String
renderStopPredicate = \case
  StopSuccess -> "success"
  StopFailure -> "failure"
  StopPartial -> "partial"
  StopTarget -> "target"
  StopFuel -> "fuel"

renderBufferRef :: BufferRef -> String
renderBufferRef = \case
  MemoryBuf -> "memory"
  CalldataBuf -> "calldata"
  ReturndataBuf -> "returndata"

renderOverapproximation :: Overapproximation -> String
renderOverapproximation = \case
  OverapproxCallSuccess opcode ->
    renderCallOpcode opcode <> " success bit abstracted"
  OverapproxCallReturndata opcode ->
    renderCallOpcode opcode <> " returndata abstracted"
  OverapproxCallStorage opcode ->
    renderCallOpcode opcode <> " post-call storage abstracted"
  OverapproxGasOpcode ->
    "GAS opcode abstracted"
  OverapproxPostCallExtcodesize ->
    "EXTCODESIZE after abstract call world"
  OverapproxPostCallExtcodehash ->
    "EXTCODEHASH after abstract call world"
  OverapproxCoarseExtcodecopyMemory ->
    "EXTCODECOPY used coarse memory abstraction"

renderOverapproximationSummary :: [Overapproximation] -> String
renderOverapproximationSummary [] = "none"
renderOverapproximationSummary items =
  concatWith "; " (fmap renderOverapproximation items)

renderSmtMode :: SmtMode -> String
renderSmtMode = \case
  SmtExact -> "exact"
  SmtWeakened -> "weakened"

renderOverapproxMode :: OverapproxMode -> String
renderOverapproxMode = \case
  OverapproxNone -> "none"
  OverapproxSome -> "some"

renderCallField :: CallField -> String
renderCallField = \case
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

renderStop :: SegmentStop -> String
renderStop = \case
  StoppedAtTargetPc stopPc -> "target-pc " <> show stopPc
  StoppedAtFuelExhaustion -> "fuel exhausted"
  StoppedAtCallBoundary boundary -> "call-boundary " <> renderCallOpcode boundary.opcode
  StoppedAtResult vmResult -> show vmResult

printCallBoundary :: CallBoundary -> IO ()
printCallBoundary boundary = do
  putStrLn $ "call-op: " <> renderCallOpcode boundary.opcode
  putStrLn $ "call-outcome: " <> renderCallBoundaryOutcome boundary.outcome
  maybe (pure ()) (\mode -> putStrLn $ "call-failure-mode: " <> renderCallFailureMode mode) boundary.failureMode
  putStrLn $ "call-gas: " <> renderWordExpr boundary.gas
  putStrLn $ "call-to: " <> renderWordExpr boundary.callee
  case boundary.value of
    Just valueExpr -> putStrLn $ "call-value: " <> renderWordExpr valueExpr
    Nothing -> pure ()
  putStrLn $ "call-input:  offset=" <> renderWordExpr boundary.inputOffset <> " size=" <> renderWordExpr boundary.inputSize
  putStrLn $ "call-output: offset=" <> renderWordExpr boundary.outputOffset <> " size=" <> renderWordExpr boundary.outputSize
  putStrLn $ "call-post-returndata: " <> renderBufExpr boundary.postReturndata
  case boundary.postStorageBase of
    Just storageBase -> putStrLn $ "call-post-storage-base: " <> renderAddrExpr storageBase
    Nothing -> putStrLn "call-post-storage-base: unchanged"
  putStrLn $ "call-constraints: " <> show (length boundary.pathConstraints)
  case boundary.outcome of
    CallContinued ->
      case (boundary.opcode, boundary.postStorageBase) of
        (CallOpStaticcall, _) -> putStrLn "call-warning: storage left unchanged for STATICCALL; returndata and success are abstract"
        (_, Just _) -> putStrLn "call-warning: post-call storage has been abstracted; later storage reads are no longer tied to the pre-call store"
        _ -> pure ()
    CallFailedDeterministic ->
      case boundary.failureMode of
        Just CallFailureReturnsZero ->
          putStrLn "call-warning: deterministic pre-call failure branch; world left unchanged, returndata is empty, success is 0"
        Just CallFailureStopsFrame ->
          putStrLn "call-warning: deterministic pre-call failure branch; execution aborts before the call takes effect"
        Nothing ->
          putStrLn "call-warning: deterministic pre-call failure branch"
    CallFailedSymbolic ->
      case boundary.failureMode of
        Just CallFailureReturnsZero ->
          putStrLn "call-warning: symbolic pre-call failure branch; world left unchanged, returndata is empty, success is 0"
        Just CallFailureStopsFrame ->
          putStrLn "call-warning: symbolic pre-call failure branch; execution aborts before the call takes effect"
        Nothing ->
          putStrLn "call-warning: symbolic pre-call failure branch"

printIndexedCallBoundary :: (Int, CallBoundary) -> IO ()
printIndexedCallBoundary (idx, boundary) = do
  putStrLn $ "call-boundary: " <> show idx
  printCallBoundary boundary

renderCallOpcode :: CallOpcode -> String
renderCallOpcode = \case
  CallOpCall -> "CALL"
  CallOpCallcode -> "CALLCODE"
  CallOpDelegatecall -> "DELEGATECALL"
  CallOpStaticcall -> "STATICCALL"

renderCallOpcodeAtom :: CallOpcode -> String
renderCallOpcodeAtom = \case
  CallOpCall -> "call"
  CallOpCallcode -> "callcode"
  CallOpDelegatecall -> "delegatecall"
  CallOpStaticcall -> "staticcall"

renderCallBoundaryOutcome :: CallBoundaryOutcome -> String
renderCallBoundaryOutcome = \case
  CallContinued -> "continued"
  CallFailedDeterministic -> "failed-deterministic"
  CallFailedSymbolic -> "failed-symbolic"

renderCallFailureMode :: CallFailureMode -> String
renderCallFailureMode = \case
  CallFailureReturnsZero -> "returns-zero"
  CallFailureStopsFrame -> "stops-frame"

parseCli :: [String] -> Either String CliOptions
parseCli args = do
  opts0 <- defaultCliOptions
  go opts0 args
  where
    go opts [] = Right opts
    go opts ("--code" : value : rest) =
      (\codeBytes -> opts { cliCode = codeBytes }) <$> parseHexBytes value >>= \opts' -> go opts' rest
    go opts ("--pc" : value : rest) =
      (\n -> opts { cliPc = n }) <$> parseInt value >>= \opts' -> go opts' rest
    go opts ("--fuel" : value : rest) =
      (\n -> opts { cliFuel = n }) <$> parseInt value >>= \opts' -> go opts' rest
    go opts ("--target-pc" : value : rest) =
      (\n -> opts { cliTargetPc = Just n }) <$> parseInt value >>= \opts' -> go opts' rest
    go opts ("--stack" : value : rest) =
      (\wordExpr -> opts { cliStack = opts.cliStack <> [wordExpr] }) <$> parseWordExpr value >>= \opts' -> go opts' rest
    go opts ("--memory" : value : rest) =
      (\bufExpr -> opts { cliMemory = bufExpr }) <$> parseBufExpr value >>= \opts' -> go opts' rest
    go opts ("--calldata" : value : rest) =
      (\bufExpr -> opts { cliCalldata = bufExpr }) <$> parseBufExpr value >>= \opts' -> go opts' rest
    go opts ("--returndata" : value : rest) =
      (\bufExpr -> opts { cliReturndata = bufExpr }) <$> parseBufExpr value >>= \opts' -> go opts' rest
    go opts ("--address" : value : rest) =
      (\addrExpr -> opts { cliAddress = addrExpr }) <$> parseAddrExpr value >>= \opts' -> go opts' rest
    go opts ("--code-address" : value : rest) =
      (\addrExpr -> opts { cliCodeAddress = addrExpr }) <$> parseAddrExpr value >>= \opts' -> go opts' rest
    go opts ("--caller" : value : rest) =
      (\addrExpr -> opts { cliCaller = addrExpr }) <$> parseAddrExpr value >>= \opts' -> go opts' rest
    go opts ("--override-caller" : value : rest) =
      (\addrExpr -> opts { cliOverrideCaller = Just addrExpr }) <$> parseAddrExpr value >>= \opts' -> go opts' rest
    go opts ("--origin" : value : rest) =
      (\addrExpr -> opts { cliOrigin = addrExpr }) <$> parseAddrExpr value >>= \opts' -> go opts' rest
    go opts ("--coinbase" : value : rest) =
      (\addrExpr -> opts { cliCoinbase = addrExpr }) <$> parseAddrExpr value >>= \opts' -> go opts' rest
    go opts ("--callvalue" : value : rest) =
      (\wordExpr -> opts { cliCallvalue = wordExpr }) <$> parseWordExpr value >>= \opts' -> go opts' rest
    go opts ("--block-number" : value : rest) =
      (\wordExpr -> opts { cliBlockNumber = wordExpr }) <$> parseWordExpr value >>= \opts' -> go opts' rest
    go opts ("--timestamp" : value : rest) =
      (\wordExpr -> opts { cliTimestamp = wordExpr }) <$> parseWordExpr value >>= \opts' -> go opts' rest
    go opts ("--static" : rest) =
      go opts { cliStatic = True } rest
    go opts ("--empty-base" : rest) =
      go opts { cliBaseState = EmptyBase } rest
    go opts ("--abstract-base" : rest) =
      go opts { cliBaseState = AbstractBase } rest
    go opts ("--store" : value : rest) =
      (\(slot, val) -> opts { cliStores = Map.insert slot val opts.cliStores }) <$> parseStoreBinding value >>= \opts' -> go opts' rest
    go opts ("--pre" : value : rest) =
      (\cond -> opts { cliPreconditions = opts.cliPreconditions <> [cond] }) <$> parseCondition value >>= \opts' -> go opts' rest
    go opts ("--post" : value : rest) =
      (\cond -> opts { cliPostconditions = opts.cliPostconditions <> [cond] }) <$> parseCondition value >>= \opts' -> go opts' rest
    go opts ("--json" : rest) =
      go opts { cliJsonOutput = True } rest
    go opts ("--trace-opcodes" : rest) =
      go opts { cliTraceOpcodes = True } rest
    go opts ("--fail-on-overapproximation" : rest) =
      go opts { cliFailOnOverapproximation = True } rest
    go opts ("--no-smt-weakening" : rest) =
      go opts { cliAllowSmtWeakening = False } rest
    go opts ("--quiet-smt-weakening" : rest) =
      go opts { cliNotifySmtWeakening = False } rest
    go _ ("--help" : _) = Left usage
    go _ (flag : _) = Left $ "unknown or incomplete flag: " <> flag <> "\n\n" <> usage

usage :: String
usage = unlines $
  [ "usage:"
  , "  equivm-symcheck smoke-all"
  ]
    <> fmap (\(name, _) -> "  equivm-symcheck " <> name) smokeCommands
    <>
      [ "  equivm-symcheck run --code HEX [--pc N] [--fuel N] [--target-pc N] [--stack WORD]..."
      , "                      [--memory HEX|sym:NAME] [--calldata HEX|sym:NAME]"
      , "                      [--returndata HEX|sym:NAME] [--address ADDR|sym:NAME]"
      , "                      [--code-address ADDR|sym:NAME] [--caller ADDR|sym:NAME]"
      , "                      [--override-caller ADDR|sym:NAME] [--origin ADDR|sym:NAME]"
      , "                      [--coinbase ADDR|sym:NAME]"
      , "                      [--callvalue WORD] [--block-number WORD] [--timestamp WORD]"
      , "                      [--static] [--empty-base|--abstract-base] [--store SLOT=VALUE]..."
      , "                      [--pre COND]... [--post COND]... [--json]"
      , "                      [--trace-opcodes]"
      , "                      [--fail-on-overapproximation]"
      , "                      [--no-smt-weakening] [--quiet-smt-weakening]"
      ]

parseInt :: String -> Either String Int
parseInt s =
  case reads s of
    [(n, "")] -> Right n
    _ -> Left $ "invalid integer: " <> s

parseWordExpr :: String -> Either String (Expr EWord)
parseWordExpr value =
  case stripPrefix "var:" value of
    Just name -> Right $ Var (T.pack name)
    Nothing ->
      case reads value of
        [(wordVal, "")] -> Right $ Lit wordVal
        _ -> Left $ "invalid word expression: " <> value

parseAddrExpr :: String -> Either String (Expr EAddr)
parseAddrExpr value =
  case stripPrefix "sym:" value of
    Just name -> Right $ SymAddr (T.pack name)
    Nothing ->
      case reads value of
        [(addrVal, "")] -> Right $ LitAddr addrVal
        _ -> Left $ "invalid address expression: " <> value

parseBufExpr :: String -> Either String (Expr Buf)
parseBufExpr value =
  case stripPrefix "sym:" value of
    Just name -> Right $ AbstractBuf (T.pack name)
    Nothing -> ConcreteBuf <$> parseHexBytes value

parseStoreBinding :: String -> Either String (W256, W256)
parseStoreBinding value =
  case break (== '=') value of
    (slotText, '=' : valText) -> do
      slot <- parseWord slotText
      val <- parseWord valText
      pure (slot, val)
    _ -> Left $ "invalid store binding: " <> value

parseCondition :: String -> Either String Condition
parseCondition value
  | Just rhs <- stripPrefix "stop==" value =
      StopCondition <$> parseStopPredicate rhs
  | otherwise =
      case find (\(opText, _) -> containsOp opText value) compareOpParsers of
        Just (opText, op) ->
          let (lhsText, rest) = breakOn opText value
          in case stripPrefix opText rest of
              Just rhsText
                | lhsText == "pc" -> PcCondition op <$> parseInt rhsText
                | lhsText == "smt" -> SmtCondition op <$> parseSmtMode rhsText
                | lhsText == "overapprox" -> OverapproxCondition op <$> parseOverapproxMode rhsText
                | Just idx <- parseCallOutcomeLhs lhsText -> CallOutcomeCondition op idx <$> parseCallBoundaryOutcome rhsText
                | Just idx <- parseCallFailureModeLhs lhsText -> CallFailureModeCondition op idx <$> parseCallFailureModeAtom rhsText
                | Just idx <- parseCallOpcodeLhs lhsText -> CallOpcodeCondition op idx <$> parseCallOpcodeAtom rhsText
                | otherwise -> WordCondition op <$> parseWordTerm lhsText <*> parseWordTerm rhsText
              Nothing -> Left $ "invalid condition: " <> value
        Nothing ->
          Left $ "invalid condition: " <> value
  where
    compareOpParsers =
      [ ("==", CmpEq)
      , ("!=", CmpNe)
      , ("<=", CmpLe)
      , (">=", CmpGe)
      , ("<", CmpLt)
      , (">", CmpGt)
      ]

containsOp :: String -> String -> Bool
containsOp needle haystack =
  case breakOn needle haystack of
    (_, "") -> False
    _ -> True

breakOn :: String -> String -> (String, String)
breakOn needle haystack = go [] haystack
  where
    go acc rest =
      case stripPrefix needle rest of
        Just _ -> (reverse acc, rest)
        Nothing ->
          case rest of
            [] -> (reverse acc, [])
            c : cs -> go (c : acc) cs

parseStopPredicate :: String -> Either String StopPredicate
parseStopPredicate = \case
  "success" -> Right StopSuccess
  "failure" -> Right StopFailure
  "partial" -> Right StopPartial
  "target" -> Right StopTarget
  "fuel" -> Right StopFuel
  other -> Left $ "invalid stop predicate: " <> other

parseCallOutcomeLhs :: String -> Maybe Int
parseCallOutcomeLhs value = do
  rest <- stripPrefix "call[" value
  let (idxText, rest1) = break (== ']') rest
  suffix <- stripPrefix "]" rest1
  fieldText <- stripPrefix "." suffix
  if fieldText == "outcome"
    then either (const Nothing) Just (parseInt idxText)
    else Nothing

parseCallBoundaryOutcome :: String -> Either String CallBoundaryOutcome
parseCallBoundaryOutcome = \case
  "continued" -> Right CallContinued
  "failed-deterministic" -> Right CallFailedDeterministic
  "failed-symbolic" -> Right CallFailedSymbolic
  other -> Left $ "invalid call outcome: " <> other

parseCallFailureModeLhs :: String -> Maybe Int
parseCallFailureModeLhs value = do
  rest <- stripPrefix "call[" value
  let (idxText, rest1) = break (== ']') rest
  suffix <- stripPrefix "]" rest1
  fieldText <- stripPrefix "." suffix
  if fieldText == "failure-mode"
    then either (const Nothing) Just (parseInt idxText)
    else Nothing

parseCallFailureModeAtom :: String -> Either String CallFailureMode
parseCallFailureModeAtom = \case
  "returns-zero" -> Right CallFailureReturnsZero
  "stops-frame" -> Right CallFailureStopsFrame
  other -> Left $ "invalid call failure mode: " <> other

parseSmtMode :: String -> Either String SmtMode
parseSmtMode = \case
  "exact" -> Right SmtExact
  "weakened" -> Right SmtWeakened
  other -> Left $ "invalid smt mode: " <> other

parseOverapproxMode :: String -> Either String OverapproxMode
parseOverapproxMode = \case
  "none" -> Right OverapproxNone
  "some" -> Right OverapproxSome
  other -> Left $ "invalid overapprox mode: " <> other

parseCallOpcodeLhs :: String -> Maybe Int
parseCallOpcodeLhs value = do
  rest <- stripPrefix "call[" value
  let (idxText, rest1) = break (== ']') rest
  suffix <- stripPrefix "]" rest1
  fieldText <- stripPrefix "." suffix
  if fieldText == "opcode"
    then either (const Nothing) Just (parseInt idxText)
    else Nothing

parseCallOpcodeAtom :: String -> Either String CallOpcode
parseCallOpcodeAtom = \case
  "call" -> Right CallOpCall
  "callcode" -> Right CallOpCallcode
  "delegatecall" -> Right CallOpDelegatecall
  "staticcall" -> Right CallOpStaticcall
  other -> Left $ "invalid call opcode: " <> other

parseWordTerm :: String -> Either String WordTerm
parseWordTerm value =
  case value of
    "address" -> Right AddressTerm
    "code-address" -> Right CodeAddressTerm
    "codeaddress" -> Right CodeAddressTerm
    "caller" -> Right CallerTerm
    "origin" -> Right OriginTerm
    "coinbase" -> Right CoinbaseTerm
    "callvalue" -> Right CallvalueTerm
    "block-number" -> Right BlockNumberTerm
    "number" -> Right BlockNumberTerm
    "timestamp" -> Right TimestampTerm
    "call-count" -> Right CallCountTerm
    _ ->
      case stripPrefix "len(" value of
        Just rest ->
          case break (== ')') rest of
            (bufText, ")") -> BufferLengthTerm <$> parseBufferRef bufText
            (bufText, ')':suffix)
              | null suffix -> BufferLengthTerm <$> parseBufferRef bufText
            _ -> Left $ "invalid length term: " <> value
        Nothing ->
          case parseBracketed "stack" value of
            Just inner -> StackTerm <$> parseInt inner
            Nothing ->
              case parseBracketed "storage" value of
                Just inner -> StorageTerm <$> parseWordTerm inner
                Nothing ->
                  case parseCallReturndataWordTerm value of
                    Just parsed -> parsed
                    Nothing ->
                      case parseCallFieldTerm value of
                        Just parsed -> parsed
                        Nothing ->
                          case parseBufferWordTerm value of
                            Just parsed -> parsed
                            Nothing ->
                              case stripPrefix "var:" value of
                                Just name -> Right $ VarTerm (T.pack name)
                                Nothing ->
                                  case parseAddrExpr value of
                                    Right addrExpr -> Right $ AddressValueTerm addrExpr
                                    Left _ -> LitTerm <$> parseWord value

parseCallReturndataWordTerm :: String -> Maybe (Either String WordTerm)
parseCallReturndataWordTerm value = do
  rest <- stripPrefix "call[" value
  let (idxText, rest1) = break (== ']') rest
  suffix <- stripPrefix "]" rest1
  fieldRest <- stripPrefix ".returndata[" suffix
  let (inner, rest2) = break (== ']') fieldRest
  suffix2 <- stripPrefix "]" rest2
  if null suffix2
    then
      pure $ do
        idx <- parseInt idxText
        offset <- parseWordTerm inner
        pure (CallReturndataWordTerm idx offset)
    else Nothing

parseCallFieldTerm :: String -> Maybe (Either String WordTerm)
parseCallFieldTerm value = do
  rest <- stripPrefix "call[" value
  let (idxText, rest1) = break (== ']') rest
  suffix <- stripPrefix "]" rest1
  fieldText <- stripPrefix "." suffix
  pure $ do
    idx <- parseInt idxText
    field <- parseCallField fieldText
    pure (CallFieldTerm idx field)

parseCallField :: String -> Either String CallField
parseCallField = \case
  "gas" -> Right CallGasField
  "to" -> Right CallToField
  "callee" -> Right CallToField
  "value" -> Right CallValueField
  "input-offset" -> Right CallInputOffsetField
  "input-size" -> Right CallInputSizeField
  "output-offset" -> Right CallOutputOffsetField
  "output-size" -> Right CallOutputSizeField
  "returndata-len" -> Right CallReturndataLengthField
  "post-storage-base" -> Right CallPostStorageBaseField
  "constraint-count" -> Right CallConstraintCountField
  other -> Left $ "invalid call field: " <> other

parseBufferWordTerm :: String -> Maybe (Either String WordTerm)
parseBufferWordTerm value =
  asumMaybe
    [ fmap (fmap (\inner -> BufferWordTerm MemoryBuf inner) . parseWordTerm) (parseBracketed "memory" value)
    , fmap (fmap (\inner -> BufferWordTerm CalldataBuf inner) . parseWordTerm) (parseBracketed "calldata" value)
    , fmap (fmap (\inner -> BufferWordTerm ReturndataBuf inner) . parseWordTerm) (parseBracketed "returndata" value)
    ]

parseBracketed :: String -> String -> Maybe String
parseBracketed prefix value = do
  rest <- stripPrefix (prefix <> "[") value
  case break (== ']') rest of
    (inner, "]") -> Just inner
    (inner, ']':suffix)
      | null suffix -> Just inner
    _ -> Nothing

parseBufferRef :: String -> Either String BufferRef
parseBufferRef = \case
  "memory" -> Right MemoryBuf
  "calldata" -> Right CalldataBuf
  "returndata" -> Right ReturndataBuf
  other -> Left $ "invalid buffer name: " <> other

asumMaybe :: [Maybe a] -> Maybe a
asumMaybe = go
  where
    go [] = Nothing
    go (x : xs) =
      case x of
        Just _ -> x
        Nothing -> go xs

parseWord :: String -> Either String W256
parseWord value =
  case reads value of
    [(wordVal, "")] -> Right wordVal
    _ -> Left $ "invalid word literal: " <> value

parseHexBytes :: String -> Either String ByteString
parseHexBytes raw = do
  let stripped = maybe raw id (stripPrefix "0x" raw)
  when (odd (length stripped)) $
    Left $ "hex input must have even length: " <> raw
  when (any (not . isHexDigit) stripped) $
    Left $ "invalid hex input: " <> raw
  BS.pack <$> traverse hexPair (pairs stripped)
  where
    pairs [] = []
    pairs (a : b : rest) = [a, b] : pairs rest
    pairs _ = []

    hexPair [a, b] = do
      hiNibble <- hexNibble a
      loNibble <- hexNibble b
      pure $ fromIntegral ((hiNibble `shiftL` 4) .|. loNibble)
    hexPair _ = Left "internal hex parser error"

    hexNibble c
      | isHexDigit c = Right (digitToInt c .&. 0xf)
      | otherwise = Left $ "invalid hex digit: " <> [c]

renderWordExprList :: [Expr EWord] -> String
renderWordExprList exprs =
  "[" <> concatWith ", " (fmap renderWordExpr exprs) <> "]"

renderPcTrace :: [Int] -> String
renderPcTrace pcs =
  "[" <> concatWith ", " (fmap show pcs) <> "]"

renderPcTraceOpcodes :: ContractCode -> [Int] -> String
renderPcTraceOpcodes code0 pcs =
  "[" <> concatWith ", " (fmap renderOne pcs) <> "]"
  where
    renderOne pc0 =
      show pc0 <> ":" <> opcodeNameAtPc code0 pc0

renderWordExpr :: Expr EWord -> String
renderWordExpr = T.unpack . Format.formatExpr . Expr.simplify

renderAddrExpr :: Expr EAddr -> String
renderAddrExpr = T.unpack . Format.formatExpr . Expr.simplify

renderBufExpr :: Expr Buf -> String
renderBufExpr = T.unpack . Format.formatExpr . Expr.simplify

renderStorageExpr :: Expr Storage -> String
renderStorageExpr = T.unpack . Format.formatExpr . Expr.simplify

renderMemory :: Memory -> String
renderMemory = \case
  SymbolicMemory buf -> renderBufExpr buf
  ConcreteMemory _ -> "<mutable-memory>"

renderProp :: Prop -> String
renderProp = T.unpack . Format.formatProp

lookupRunningContract :: VM Symbolic -> Maybe Contract
lookupRunningContract vm =
  Map.lookup vm.state.contract vm.env.contracts

renderBalances :: VM Symbolic -> [String]
renderBalances vm =
  fmap renderOne (Map.toList vm.env.contracts)
  where
    renderOne (addr, contract) =
      renderAddrExpr addr <> " => " <> renderWordExpr contract.balance

renderVmResult :: VMResult Symbolic -> String
renderVmResult = \case
  VMSuccess buf -> "VMSuccess " <> renderBufExpr buf
  VMFailure (Revert buf) -> "VMFailure (Revert " <> renderBufExpr buf <> ")"
  other -> show other

concatWith :: String -> [String] -> String
concatWith _ [] = ""
concatWith _ [x] = x
concatWith sep (x : xs) = x <> sep <> concatWith sep xs

opcodeNameAtPc :: ContractCode -> Int -> String
opcodeNameAtPc code0 pc0 =
  case code0 of
    RuntimeCode (ConcreteRuntimeCode bytes)
      | pc0 < 0 -> "negative-pc"
      | pc0 >= BS.length bytes -> "out-of-bounds"
      | otherwise -> intToOpName (fromIntegral (BS.index bytes pc0))
    RuntimeCode (SymbolicRuntimeCode _) -> "symbolic-runtime-code"
    InitCode codeBytes _
      | pc0 < 0 -> "negative-pc"
      | pc0 >= BS.length codeBytes -> "out-of-bounds"
      | otherwise -> intToOpName (fromIntegral (BS.index codeBytes pc0))
    UnknownCode _ -> "unknown-code"

pcTraceOpcodesToJson :: ContractCode -> [Int] -> [Value]
pcTraceOpcodesToJson code0 pcs =
  fmap
    (\pc0 -> object ["pc" .= pc0, "opcode" .= opcodeNameAtPc code0 pc0])
    pcs

emitJsonOutput :: Bool -> [SegmentResult] -> Maybe [[PostconditionReport]] -> IO ()
emitJsonOutput includeTraceOpcodes results reports = do
  resultValues <- traverse (segmentResultToJson includeTraceOpcodes) (zip [1 :: Int ..] results)
  let jsonValue =
        object
          [ "results" .= resultValues
          , "postconditions" .= fmap postconditionReportsToJson reports
          ]
  LBS8.putStrLn (encode jsonValue)

segmentResultToJson :: Bool -> (Int, SegmentResult) -> IO Value
segmentResultToJson includeTraceOpcodes (idx, result) = do
  frozenVm <- stToIO $ SymExec.freezeVM result.finalVm
  let currentContractState = lookupRunningContract frozenVm
  pure $
    object
      ( [ "branch" .= idx
        , "steps" .= result.steps
        , "pcTrace" .= result.pcTrace
        , "stop" .= renderStop result.stopReason
        , "pc" .= frozenVm.state.pc
        , "stack" .= fmap renderWordExpr frozenVm.state.stack
        , "memory" .= renderMemory frozenVm.state.memory
        , "returndata" .= renderBufExpr frozenVm.state.returndata
        , "constraints" .= length frozenVm.constraints
        , "pathConstraints" .= fmap renderProp frozenVm.constraints
        , "storage" .= fmap (renderStorageExpr . (.storage)) currentContractState
        , "transientStorage" .= fmap (renderStorageExpr . (.tStorage)) currentContractState
        , "originalStorage" .= fmap (renderStorageExpr . (.origStorage)) currentContractState
        , "balance" .= fmap (renderWordExpr . (.balance)) currentContractState
        , "balances" .= fmap balanceEntryToJson (Map.toList frozenVm.env.contracts)
        , "usedWeakenedSmt" .= result.usedWeakenedSmt
        , "overapproximations" .= fmap renderOverapproximation result.overapproximations
        , "callBoundaries" .= fmap callBoundaryToJson result.callBoundaries
        , "vmResult" .= fmap renderVmResult frozenVm.result
        ]
          <> [ "pcTraceOpcodes" .= pcTraceOpcodesToJson frozenVm.state.code result.pcTrace
             | includeTraceOpcodes
             ]
      )

balanceEntryToJson :: (Expr EAddr, Contract) -> Value
balanceEntryToJson (addr, contract) =
  object
    [ "address" .= renderAddrExpr addr
    , "balance" .= renderWordExpr contract.balance
    ]

callBoundaryToJson :: CallBoundary -> Value
callBoundaryToJson boundary =
  object
    [ "opcode" .= renderCallOpcode boundary.opcode
    , "outcome" .= renderCallBoundaryOutcome boundary.outcome
    , "failureMode" .= fmap renderCallFailureMode boundary.failureMode
    , "gas" .= renderWordExpr boundary.gas
    , "callee" .= renderWordExpr boundary.callee
    , "value" .= fmap renderWordExpr boundary.value
    , "inputOffset" .= renderWordExpr boundary.inputOffset
    , "inputSize" .= renderWordExpr boundary.inputSize
    , "outputOffset" .= renderWordExpr boundary.outputOffset
    , "outputSize" .= renderWordExpr boundary.outputSize
    , "postReturndata" .= renderBufExpr boundary.postReturndata
    , "postStorageBase" .= fmap renderAddrExpr boundary.postStorageBase
    , "constraints" .= length boundary.pathConstraints
    ]

postconditionReportsToJson :: [[PostconditionReport]] -> Value
postconditionReportsToJson reportsByBranch =
  toJSON $
    fmap
      (\(idx, reports) ->
        object
          [ "branch" .= idx
          , "reports" .= fmap postconditionReportToJson reports
          ])
      (zip [1 :: Int ..] reportsByBranch)

postconditionReportToJson :: PostconditionReport -> Value
postconditionReportToJson report =
  object
    [ "condition" .= renderCondition report.condition
    , "status" .= postconditionStatusTag report.status
    , "details" .= postconditionStatusDetails report.status
    ]

postconditionStatusTag :: PostconditionStatus -> String
postconditionStatusTag = \case
  PostconditionQed -> "qed"
  PostconditionQedWithAbstraction -> "qed-weakened"
  PostconditionCex {} -> "cex"
  PostconditionUnknown {} -> "unknown"
  PostconditionError {} -> "error"

postconditionStatusDetails :: PostconditionStatus -> Maybe String
postconditionStatusDetails = \case
  PostconditionQed -> Nothing
  PostconditionQedWithAbstraction -> Just "proved after conservative SMT weakening"
  PostconditionCex details -> details
  PostconditionUnknown msg -> Just msg
  PostconditionError msg -> Just msg

failIfOverapproximated :: [SegmentResult] -> IO ()
failIfOverapproximated results =
  case filter (not . null . snd) flagged of
    [] -> pure ()
    _ ->
      die $
        unlines $
          "execution used overapproximation:" :
          fmap renderBranch flagged
  where
    flagged = [(idx, result.overapproximations) | (idx, result) <- zip [1 :: Int ..] results]

    renderBranch (idx, overapprox) =
      "branch "
        <> show idx
        <> ": "
        <> renderOverapproximationSummary overapprox
