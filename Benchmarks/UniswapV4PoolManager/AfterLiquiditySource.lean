import Benchmarks.UniswapV4PoolManager.AfterLiquiditySelectionSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterLiquidityPreludeFrame (f : Frame) (delta : UInt256) : Frame :=
  {f with locals := (f.locals.insert "hookDelta" (.int 0)).insert "callerDelta" (.int (EVM.signed delta))}
def afterLiquidityBlockResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if evm.executionEnv.source = hook then .returned f evm (some [.int (EVM.signed delta), .int 0])
  else continueBlockResult (fun f' next => afterLiquidityReturnResult f' next hook p delta out)
    (afterLiquiditySelectedResult (afterLiquidityPreludeFrame f delta) evm post hook key p delta fees data z out)
def afterLiquidityResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  finishBlockResult (afterLiquidityBlockResult f evm post hook key p delta fees data z out)

theorem afterLiquidityBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {delta fees : UInt256} {data out : ByteArray} {z : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (he : f.locals.get? "feesAccrued" = some (.int (EVM.signed fees)))
    (hb : f.locals.get? "hookData" = some (.bytes data))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hcall : evm.executionEnv.source ≠ hook → afterLiquidityActive hook p → callViaEVM evm hook 0
      (afterLiquidityPayload (afterLiquidityAdd p) evm.executionEnv.source key p delta fees data) (z, post, out)) :
    ExecFuncBody config f evm afterLiquidityFunction.body
      (afterLiquidityResult f evm post hook key p delta fees data z out) := by
  apply execFuncBody_block
  have hsender : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
    simp only [evalExpr?, envValue, pure]
  have heq := evalEqAddress hsender (evalLocalValue hs)
  by_cases hself : evm.executionEnv.source = hook
  · rw [afterLiquidityBlockResult, if_pos hself]
    apply ExecBlock.consReturn
    apply ExecStmt.iteTrue (heq.trans (by rw [decide_eq_true hself]))
    exact ExecBlock.consReturn (ExecStmt.return (by
      simp only [evalExprs?, evalLocalValue hd, evalExpr?, bind, EvalResult.bind, pure]))
  · rw [afterLiquidityBlockResult, if_neg hself]
    let f0 := {f with locals := f.locals.insert "hookDelta" (.int 0)}
    let f1 := afterLiquidityPreludeFrame f delta
    have hget (name : Ident) (hn0 : ("callerDelta" == name) = false) (hn1 : ("hookDelta" == name) = false) :
        f1.locals.get? name = f.locals.get? name :=
      (store_get_ne _ _ hn0).trans (store_get_ne _ _ hn1)
    have hcaller : f1.locals.get? "callerDelta" = some (.int (EVM.signed delta)) := store_get_self _ _ _
    have hhook : f1.locals.get? "hookDelta" = some (.int 0) :=
      (store_get_ne _ _ (by decide : ("callerDelta" == "hookDelta") = false)).trans (store_get_self _ _ _)
    have hpre : ExecBlock config f evm (afterLiquidityFunction.body.take 3) (.ok f1 evm) := by
      apply ExecBlock.consNormal (ExecStmt.iteFalse (heq.trans (by rw [decide_eq_false hself])) ExecBlock.nil)
      apply ExecBlock.consNormal (ExecStmt.letDecl (show evalExpr? config f evm (.intLit 0) = .ok (.int 0) by
        simp only [evalExpr?, pure]))
      exact ExecBlock.consNormal (ExecStmt.letDecl
        (evalLocalValue ((store_get_ne _ _ (by decide : ("hookDelta" == "delta") = false)).trans hd))) ExecBlock.nil
    have hsel := afterLiquiditySelectedBody (f := f1) hf
      ((hget "self" (by decide) (by decide)).trans hs)
      ((hget "key" (by decide) (by decide)).trans hk)
      ((hget "params" (by decide) (by decide)).trans hp)
      ((hget "delta" (by decide) (by decide)).trans hd)
      ((hget "feesAccrued" (by decide) (by decide)).trans he)
      ((hget "hookData" (by decide) (by decide)).trans hb)
      hcaller hhook hc hl hu (hcall hself)
    have htail : ExecBlock config f1 evm (afterLiquidityFunction.body.drop 3)
        (continueBlockResult (fun f' next => afterLiquidityReturnResult f' next hook p delta out)
          (afterLiquiditySelectedResult f1 evm post hook key p delta fees data z out)) := by
      apply execBlock_continue (execBlock_singleton hsel)
      intro f' next hr
      exact afterLiquiditySelectedReturn hcaller hhook hr
    exact execBlock_append hpre htail

end Benchmarks.UniswapV4PoolManager
