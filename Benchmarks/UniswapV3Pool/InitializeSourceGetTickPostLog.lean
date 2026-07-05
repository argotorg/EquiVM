import Benchmarks.UniswapV3Pool.InitializeSourceGetTickLogRemaining

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def getTickSourceLogSqrt10001MultiplierInt : Int :=
  255738958999603826347141

def getTickSourceLogSqrt10001Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2After50Int I * getTickSourceLogSqrt10001MultiplierInt

def getTickSourceLogSqrt10001Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogSqrt10001Int I)

def getTickStoreAfterLogSqrt10001 (I : ExecutionEnv) : Store :=
  (getTickStoreAfterLogStep50 I).insert "log_sqrt10001" (getTickSourceLogSqrt10001Value I)

theorem getTickStoreAfterLogStep50_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep50 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After50Int I)) := by
  rw [getTickStoreAfterLogStep50, getTickSourceLogStepStoreAfterLog2, store_get_self]
  rfl

theorem getTickStoreAfterLogSqrt10001_log (I : ExecutionEnv) :
    (getTickStoreAfterLogSqrt10001 I).get? "log_sqrt10001" =
      some (getTickSourceLogSqrt10001Value I) := by
  rw [getTickStoreAfterLogSqrt10001, store_get_self]

theorem getTickStoreAfterLogSqrt10001_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogSqrt10001 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After50Int I)) := by
  rw [getTickStoreAfterLogSqrt10001]
  rw [store_get_ne (getTickStoreAfterLogStep50 I) (k := "log_sqrt10001") (a := "log_2")
    (getTickSourceLogSqrt10001Value I) (by decide)]
  exact getTickStoreAfterLogStep50_log2 I

theorem evalExpr_getTick_log2Var_afterLogStep50 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep50 I }
      evm (.var "log_2") = .ok (Value.int (getTickSourceLog2After50Int I)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogStep50_log2]

theorem evalExpr_getTick_log_sqrt10001 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogStep50 I }
      evm (mulE (.var "log_2") (.intLit 255738958999603826347141)) =
      .ok (getTickSourceLogSqrt10001Value I) := by
  unfold mulE getTickSourceLogSqrt10001Value getTickSourceLogSqrt10001Int
    getTickSourceLogSqrt10001MultiplierInt
  simp only [evalExpr?, evalExpr_getTick_log2Var_afterLogStep50, EvalResult.bind, bind,
    pure, evalBinaryOp?]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogSqrt10001Let {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep50 I }
      evm
      [ .letDecl "log_sqrt10001" (some int256)
          (mulE (.var "log_2") (.intLit 255738958999603826347141)) ]
      (.ok { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I } evm) := by
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_getTick_log_sqrt10001 evm I))
    ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To50AndLogSqrt {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      (((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false) ++
        [ .letDecl "log_sqrt10001" (some int256)
            (mulE (.var "log_2") (.intLit 255738958999603826347141)) ])
      (.ok { contract := contract v, locals := getTickStoreAfterLogSqrt10001 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To50 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLogSqrt10001Let evm I)

end Benchmarks.UniswapV3Pool
