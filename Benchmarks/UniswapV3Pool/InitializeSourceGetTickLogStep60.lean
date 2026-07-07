import Benchmarks.UniswapV3Pool.InitializeSourceGetTickLogStep61

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def getTickSourceLogRShifted60Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepRShiftedNat (getTickSourceLogRAfter61Nat I)

def getTickSourceLogF60Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepFNat (getTickSourceLogRAfter61Nat I)

def getTickSourceLog2After60Int (I : ExecutionEnv) : Int :=
  getTickSourceLogStepLog2AfterInt (getTickSourceLog2After61Int I)
    (getTickSourceLogRAfter61Nat I) 60

def getTickSourceLogRAfter60Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepRAfterNat (getTickSourceLogRAfter61Nat I)

def getTickStoreAfterLogStep60 (I : ExecutionEnv) : Store :=
  getTickSourceLogStepStoreAfter (getTickStoreAfterLogStep61 I)
    (getTickSourceLog2After61Int I) (getTickSourceLogRAfter61Nat I) 60

theorem getTickSourceLogRAfter60Nat_lt_twoPow128 (I : ExecutionEnv) :
    getTickSourceLogRAfter60Nat I < 2 ^ (128 : Nat) := by
  unfold getTickSourceLogRAfter60Nat
  exact getTickSourceLogStepRAfterNat_lt_twoPow128
    (getTickSourceLogRAfter61Nat I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)

theorem getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter60Nat I * getTickSourceLogRAfter60Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter60Nat
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter61Nat I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep61_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep61 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter61Nat I))) := by
  simpa [getTickStoreAfterLogStep61, getTickSourceLogRAfter61Nat,
    getTickSourceLogStepRAfterValue]
    using getTickSourceLogStepStoreAfter_r (getTickStoreAfterLogStep62 I)
      (getTickSourceLog2After62Int I) (getTickSourceLogRAfter62Nat I) 61

theorem getTickStoreAfterLogStep61_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep61 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After61Int I)) := by
  simpa [getTickStoreAfterLogStep61, getTickSourceLog2After61Int,
    getTickSourceLogStepLog2AfterValue]
    using getTickSourceLogStepStoreAfter_log2 (getTickStoreAfterLogStep62 I)
      (getTickSourceLog2After62Int I) (getTickSourceLogRAfter62Nat I) 61

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep60 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep61 I }
      evm (logStep 60 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep61 I)
    (getTickSourceLog2After61Int I) (getTickSourceLogRAfter61Nat I) 60
    (getTickStoreAfterLogStep61_r I)
    (getTickStoreAfterLogStep61_log2 I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep60 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreWithMsb I } evm
      (((((msbStep 7 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF ++
        msbStep 6 0xFFFFFFFFFFFFFFFF ++
        msbStep 5 0xFFFFFFFF ++
        msbStep 4 0xFFFF ++
        msbStep 3 0xFF ++
        msbStep 2 0xF ++
        msbStep 1 0x3 ++
        [ .letDecl "f" (some uint256)
            (.ite (gtE (.var "r") (.intLit 0x1)) (.intLit 1) (.intLit 0)),
          .assign .localVar (varRef "msb") (addE (.var "msb") (.var "f")),
          Stmt.ite (geE (.var "msb") (.intLit 128))
            [ .assign .localVar (varRef "r")
                (shrE (.var "ratio") (subE (.var "msb") (.intLit 127))) ]
            [ .assign .localVar (varRef "r")
                (shlE (.var "ratio") (subE (.intLit 127) (.var "msb"))) ],
          .letDecl "log_2" (some int256)
            (mulE (subE (.var "msb") (.intLit 128)) (.intLit (2 ^ (64 : Nat)))) ]) ++
        logStep 63 true) ++
        logStep 62 true) ++
        logStep 61 true) ++
        logStep 60 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceThroughLogStep61 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep60 evm I)

end Benchmarks.UniswapV3Pool
