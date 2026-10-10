import Benchmarks.UniswapV4PoolManager.PoolModifyClear

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyClearsResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool) : ExecResult :=
  if p.delta < 0 then
    continueBlockResult (fun f1 post => poolModifyClearResult f1 post id (EVM.signed p.upper) true fu)
      (poolModifyClearResult f evm id (EVM.signed p.lower) false fl)
  else .ok f evm

theorem poolModifyClears {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {gl gu : UInt256} (hc : PoolModifyContext f id p)
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu)) :
    ExecStmt config f evm poolModifyFunction.body[23]! (poolModifyClearsResult f evm id p fl fu) := by
  have he : evalExpr? config f evm (.binary .lt (.var "liquidityDelta") (.intLit 0)) =
      .ok (.bool (decide (p.delta < 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hc.liquidityDelta]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  by_cases hd : p.delta < 0
  · rw [poolModifyClearsResult, if_pos hd]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hd] using he)
    have hlo := poolModifyClear (upper := false) (evm := evm) hc hc.lower hs
    apply execBlock_continue (execBlock_singleton hlo)
    intro f1 post hpost
    have hc1 := poolModifyClearResult_context hc hpost
    exact execBlock_singleton (poolModifyClear (upper := true) (evm := post) hc1 hc1.upper
      ((poolModifyClearResult_get hpost "state" (by decide) (by decide)).trans hs))
  · rw [poolModifyClearsResult, if_neg hd]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hd] using he) ExecBlock.nil

theorem poolModifyClearsResult_context {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {fl fu : Bool} (hc : PoolModifyContext f id p)
    (h : poolModifyClearsResult f evm id p fl fu = .ok f' post) : PoolModifyContext f' id p := by
  unfold poolModifyClearsResult at h
  split_ifs at h
  · obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
    exact poolModifyClearResult_context (poolModifyClearResult_context hc hlo) hup
  · cases h
    exact hc

theorem poolModifyClearsResult_get {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {fl fu : Bool}
    (h : poolModifyClearsResult f evm id p fl fu = .ok f' post)
    (name : Ident) (ha : ∀ upper, (poolModifyClearAlias upper == name) = false)
    (hr : ∀ upper, (poolModifyClearRet upper == name) = false) : f'.locals.get? name = f.locals.get? name := by
  unfold poolModifyClearsResult at h
  split_ifs at h
  · obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
    exact (poolModifyClearResult_get hup name (ha true) (hr true)).trans
      (poolModifyClearResult_get hlo name (ha false) (hr false))
  · cases h
    rfl

end Benchmarks.UniswapV4PoolManager
