import Benchmarks.UniswapV3.Pool.SwapStateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapLoopCondition : Expr :=
  .binary .and
    (.binary .ne (.field (.var "state") "amountSpecifiedRemaining") (.intLit 0))
    (.binary .ne (.field (.var "state") "sqrtPriceX96") (.var "sqrtPriceLimitX96"))

def swapContinues (a : SwapArgs) (s : SwapStateData) : Bool :=
  decide (s.remaining ≠ 0) && decide (s.price.toNat ≠ a.priceLimit.toNat)

def swapLoopBody : List Stmt :=
  match swapTransition.body[13]! with
  | .while _ body => body
  | _ => []

theorem swapLoopStmt : swapTransition.body[13]! = .while swapLoopCondition swapLoopBody := rfl

theorem evalSwapLoopCondition {frame : Frame} {evm : EVM.State} (a : SwapArgs) (s : SwapStateData)
    (hs : frame.locals.get? "state" = some s.value)
    (hl : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat))) :
    evalExpr? config frame evm swapLoopCondition = .ok (.bool (swapContinues a s)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hs
  have hr := evalExpr_structField (name := "amountSpecifiedRemaining") he rfl
  have hp := evalExpr_structField (name := "sqrtPriceX96") he rfl
  have hrem := evalExpr_int_ne hr (show evalExpr? config frame evm (.intLit 0) = .ok (.int 0) by
    simp only [evalExpr?, pure])
  have hlim := evalExpr_int_ne hp (evalExpr_var_get (cfg := config) (evm := evm) hl)
  have hprice : evalExpr? config frame evm
      (.binary .ne (.field (.var "state") "sqrtPriceX96") (.var "sqrtPriceLimitX96")) =
      .ok (.bool (decide (s.price.toNat ≠ a.priceLimit.toNat))) := by
    simpa only [ne_eq, Int.ofNat_eq_natCast, Int.natCast_inj] using hlim
  exact evalExpr_bool_and hrem hprice

end Benchmarks.UniswapV3.Pool
