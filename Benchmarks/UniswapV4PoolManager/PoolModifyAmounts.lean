import Benchmarks.UniswapV4PoolManager.PoolModifyOutside
import Benchmarks.UniswapV4PoolManager.PoolModifyInside
import Benchmarks.UniswapV4PoolManager.PoolModifyPricePrelude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyRegionStmt : Stmt :=
  .ite (.binary .lt (.var "tick") (.var "tickLower")) (poolModifyOutsideBlock false)
    [.ite (.binary .lt (.var "tick") (.var "tickUpper")) poolModifyInsideBlock (poolModifyOutsideBlock true)]
def poolModifyRegionResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (tick : Int) (sqrtPrice : UInt256) : ExecResult :=
  if tick < EVM.signed p.lower then poolModifyOutsideResult f evm false p else
    if tick < EVM.signed p.upper then poolModifyInsideResult f evm id p sqrtPrice else poolModifyOutsideResult f evm true p

theorem poolModifyRegion {f : Frame} {evm : State} {id sqrtPrice : UInt256} {p : PoolModifyParams} {tick : Int} {old : Value}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (htick : f.locals.get? "tick" = some (.int tick))
    (hprice : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat))) (hb : sqrtPrice.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some old) :
    ExecStmt config f evm poolModifyRegionStmt (poolModifyRegionResult f evm id p tick sqrtPrice) := by
  have hlo : evalExpr? config f evm (.binary .lt (.var "tick") (.var "tickLower")) =
      .ok (.bool (decide (tick < EVM.signed p.lower))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue htick, evalLocalValue hc.lower]
    rfl
  have hup : evalExpr? config f evm (.binary .lt (.var "tick") (.var "tickUpper")) =
      .ok (.bool (decide (tick < EVM.signed p.upper))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue htick, evalLocalValue hc.upper]
    rfl
  by_cases hl : tick < EVM.signed p.lower
  · rw [poolModifyRegionResult, if_pos hl]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hl] using hlo)
      (poolModifyOutside hc ht hdlo hdhi hd false)
  · rw [poolModifyRegionResult, if_neg hl]
    apply ExecStmt.iteFalse (by simpa only [decide_eq_false hl] using hlo)
    by_cases hu : tick < EVM.signed p.upper
    · rw [if_pos hu]
      exact execBlock_singleton (ExecStmt.iteTrue (by simpa only [decide_eq_true hu] using hup)
        (poolModifyInside hc ht hprice hb hdlo hdhi hd))
    · rw [if_neg hu]
      exact execBlock_singleton (ExecStmt.iteFalse (by simpa only [decide_eq_false hu] using hup)
        (poolModifyOutside hc ht hdlo hdhi hd true))

theorem poolModifyAmountsStmt : poolModifyFunction.body[24]! =
    .ite (.binary .ne (.var "liquidityDelta") (.intLit 0))
      (poolModifyPricePreludeBlock ++ [poolModifyRegionStmt]) [] := rfl

def poolModifyAmountsResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  if p.delta ≠ 0 then poolModifyRegionResult (poolModifyPricePreludeFrame f evm id) evm id p
    (poolCurrentTick evm id) (poolSqrtPriceWord evm id) else .ok f evm

theorem poolModifyAmounts {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams} {old : Value}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some old) :
    ExecStmt config f evm poolModifyFunction.body[24]! (poolModifyAmountsResult f evm id p) := by
  rw [poolModifyAmountsStmt]
  have he : evalExpr? config f evm (.binary .ne (.var "liquidityDelta") (.intLit 0)) =
      .ok (.bool (decide (p.delta ≠ 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hc.liquidityDelta]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?, BEq.beq, Value.int.injEq, decide_not]
  by_cases hz : p.delta ≠ 0
  · rw [poolModifyAmountsResult, if_pos hz]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using he)
    have hpre := poolModifyPricePrelude (evm := evm) hc
    have hc1 := poolModifyPricePreludeFrame_context hc evm
    have hregion := poolModifyRegion (f := poolModifyPricePreludeFrame f evm id) (evm := evm) hc1 ht
      ((store_get_ne2 _ _ _ (by decide : ("__c15" == "tick") = false)
        (by decide : ("sqrtPriceX96" == "tick") = false)).trans (store_get_self _ _ _))
      (store_get_self _ _ _) (poolSqrtPrice_bound evm id) hdlo hdhi
      ((poolModifyPricePreludeFrame_get _ _ _ "delta" (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hd)
    exact execBlock_append hpre (execBlock_singleton hregion)
  · rw [poolModifyAmountsResult, if_neg hz]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using he) ExecBlock.nil

end Benchmarks.UniswapV4PoolManager
