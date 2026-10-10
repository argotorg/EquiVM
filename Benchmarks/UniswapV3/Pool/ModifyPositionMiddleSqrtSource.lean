import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleAmountsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState

def modifyPositionMiddleSqrtStmt (second : Bool) : Stmt :=
  .internalCall "TickMath_getSqrtRatioAtTick"
    [.field (.var "params") (if second then "tickLower" else "tickUpper")]
    (if second then "__c10" else "__c8")

def modifyPositionMiddleAmountBody (second : Bool) : List Stmt :=
  [modifyPositionMiddleSqrtStmt second,
    .internalCall (signedAmountDeltaName second) (modifyPositionMiddleAmountExprs second)
      (modifyPositionMiddleAmountName second),
    .assign .localVar ⟨if second then "amount1" else "amount0", []⟩
      (.var (modifyPositionMiddleAmountName second))]

theorem modifyPositionMiddleSqrtSource (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm evm' : EVM.State) (second : Bool)
    (ha : a.Fits) (ht : validTicks a.lower a.upper) :
    ExecStmt config (modifyPositionMiddleBeforeSqrtFrame v a evm second) evm'
      (modifyPositionMiddleSqrtStmt second)
      (.ok (modifyPositionMiddleSqrtFrame v a evm second) evm') := by
  have hp : evalExpr? config (modifyPositionMiddleBeforeSqrtFrame v a evm second) evm'
      (.var "params") = .ok a.value :=
    evalExpr_var_get (by cases second <;> modify_position_middle_amount_get)
  have he : evalExpr? config (modifyPositionMiddleBeforeSqrtFrame v a evm second) evm'
      (.field (.var "params") (if second then "tickLower" else "tickUpper")) =
      .ok (.int (if second then a.lower else a.upper)) :=
    evalExpr_structField hp (by cases second <;> rfl)
  have hr := tickSqrtInternalSource (if second then a.lower else a.upper)
    (modifyPositionMiddleBeforeSqrtFrame v a evm second) evm'
    [.field (.var "params") (if second then "tickLower" else "tickUpper")]
    (if second then "__c10" else "__c8") (by cases second <;> rfl)
    (by simp only [evalExprs?, he, bind, EvalResult.bind, pure])
    (by cases second; exact ha.2.1.1; exact ha.1.1)
    (by cases second; exact ha.2.1.2; exact ha.1.2)
    (by cases second; exact modifyPositionTickValid a ht true; exact modifyPositionTickValid a ht false)
  cases second <;> exact hr

end Benchmarks.UniswapV3.Pool
