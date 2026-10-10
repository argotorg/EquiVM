import Benchmarks.UniswapV4PoolManager.AfterSwapSelectionSource
import Benchmarks.UniswapV4PoolManager.AfterSwapFinishSource
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterSwapPreludeFrame (f : Frame) (before : UInt256) : Frame :=
  valueLocal (valueLocal f "specified" (.int (balanceDeltaAmount0 before)))
    "unspecified" (.int (balanceDeltaAmount1 before))
def afterSwapBlockResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (delta before : UInt256) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if evm.executionEnv.source = hook then .returned f evm (some [.int (EVM.signed delta), .int 0])
  else continueBlockResult (fun f' next => afterSwapFinishResult f' next p delta (balanceDeltaAmount0 before)
    (afterSwapSelectedUnspecified hook (balanceDeltaAmount1 before) out))
    (afterSwapSelectedResult (afterSwapPreludeFrame f before) evm post hook key p delta (balanceDeltaAmount1 before) data z out)
def afterSwapResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (delta before : UInt256) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  finishBlockResult (afterSwapBlockResult f evm post hook key p delta before data z out)

theorem afterSwapPrelude_get (f : Frame) (before : UInt256) (name : Ident)
    (hs : ("specified" == name) = false) (hu : ("unspecified" == name) = false) :
    (afterSwapPreludeFrame f before).locals.get? name = f.locals.get? name := store_get_ne2 _ _ _ hs hu

theorem afterSwapBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {delta before : UInt256} {data out : ByteArray} {z : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes data))
    (hbefore : f.locals.get? "beforeSwapHookReturn" = some (.int (EVM.signed before)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hcall : evm.executionEnv.source ≠ hook → afterSwapActive hook →
      callViaEVM evm hook 0 (afterSwapPayload evm.executionEnv.source key p delta data) (z, post, out)) :
    ExecFuncBody config f evm afterSwapFunction.body (afterSwapResult f evm post hook key p delta before data z out) := by
  apply execFuncBody_block
  have heq := evalEqAddress
    (show evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) by
      simp only [evalExpr?, envValue, pure]) (evalLocalValue hs)
  by_cases hself : evm.executionEnv.source = hook
  · rw [afterSwapBlockResult, if_pos hself]
    exact ExecBlock.consReturn (ExecStmt.iteTrue (heq.trans (by rw [decide_eq_true hself]))
      (ExecBlock.consReturn (ExecStmt.return (by
        simp only [evalExprs?, evalLocalValue hd, evalExpr?, bind, EvalResult.bind, pure]))))
  · rw [afterSwapBlockResult, if_neg hself]
    let f1 := valueLocal f "specified" (.int (balanceDeltaAmount0 before))
    let f2 := afterSwapPreludeFrame f before
    have hs1 := balanceDeltaAmount0_eval (evalLocalValue (cfg := config) (evm := evm) hbefore)
    have hu1 := balanceDeltaAmount1_eval (evalLocalValue (cfg := config) (evm := evm) (f := f1)
      ((store_get_ne _ _ (by decide : ("specified" == "beforeSwapHookReturn") = false)).trans hbefore))
    have hpre : ExecBlock config f evm (afterSwapFunction.body.take 3) (.ok f2 evm) :=
      ExecBlock.consNormal (ExecStmt.iteFalse (heq.trans (by rw [decide_eq_false hself])) ExecBlock.nil)
        (ExecBlock.consNormal (ExecStmt.letDecl hs1) (ExecBlock.consNormal (ExecStmt.letDecl hu1) ExecBlock.nil))
    have hget := afterSwapPrelude_get f before
    have hp2 : f2.locals.get? "params" = some (swapParamsValue p) :=
      (hget "params" (by decide) (by decide)).trans hp
    have hd2 : f2.locals.get? "swapDelta" = some (.int (EVM.signed delta)) :=
      (hget "swapDelta" (by decide) (by decide)).trans hd
    have hs2 : f2.locals.get? "specified" = some (.int (balanceDeltaAmount0 before)) :=
      (store_get_ne _ _ (by decide : ("unspecified" == "specified") = false)).trans (store_get_self _ _ _)
    have hu2 : f2.locals.get? "unspecified" = some (.int (balanceDeltaAmount1 before)) := store_get_self _ _ _
    have hsel := afterSwapSelectedSource (f := f2) hf
      ((hget "self" (by decide) (by decide)).trans hs)
      ((hget "key" (by decide) (by decide)).trans hk) hp2 hd2
      ((hget "hookData" (by decide) (by decide)).trans hb) hu2 hc hl (hcall hself)
    have htail : ExecBlock config f2 evm (afterSwapFunction.body.drop 3)
        (continueBlockResult (fun f' next => afterSwapFinishResult f' next p delta (balanceDeltaAmount0 before)
          (afterSwapSelectedUnspecified hook (balanceDeltaAmount1 before) out))
          (afterSwapSelectedResult f2 evm post hook key p delta (balanceDeltaAmount1 before) data z out)) := by
      apply execBlock_continue (execBlock_singleton hsel)
      intro f' next hr
      obtain ⟨hf', hp', hs', hd', hu', huc⟩ := afterSwapSelectedResult_normal hu2 (balanceDeltaAmount1_fits before) hr
      exact afterSwapFinishSource (hf'.trans hf) (hp'.trans hp2) (hd'.trans hd2) (hs'.trans hs2) hu'
        (balanceDeltaAmount0_fits before) huc
    exact execBlock_append hpre htail

end Benchmarks.UniswapV4PoolManager
