import Benchmarks.UniswapV4PoolManager.AfterLiquiditySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem afterLiquidity_lookup : lookupCallable? contract "Hooks_afterModifyLiquidity" =
    some afterLiquidityFunction.toCallable := rfl

def afterLiquidityCallFrame (f : Frame) (hook : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) : Frame :=
  {f with locals := ((((((∅ : Store).insert "hookData" (.bytes data)).insert
    "feesAccrued" (.int (EVM.signed fees))).insert "delta" (.int (EVM.signed delta))).insert
    "params" (modifyLiquidityParamsValue p)).insert
    "key" (poolKeyValue key)).insert "self" (.address hook)}

def afterLiquidityInvocationResult (f : Frame) (ret : Ident) (evm post : State) (hook : AccountAddress)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray)
    (z : Bool) (out : ByteArray) : ExecResult :=
  let done := fun state caller hookDelta => ExecResult.ok
    {f with locals := f.locals.insert ret (.tuple [.int (EVM.signed caller), .int (EVM.signed hookDelta)])} state
  if evm.executionEnv.source = hook then done evm delta ⟨0⟩
  else if afterLiquidityActive hook p then
    let parse := afterLiquidityParse hook (afterLiquidityAdd p)
    let hookDelta := hookDeltaWord out parse
    if z = true ∧ hookReplyValid
      (afterLiquidityPayload (afterLiquidityAdd p) evm.executionEnv.source key p delta fees data) out then
      if parse = true ∧ out.size ≠ 64 then .reverted
      else if balanceDeltaCombineFits true delta hookDelta then
        done post (balanceDeltaCombineWord true delta hookDelta) hookDelta
      else .reverted
    else .reverted
  else done evm delta ⟨0⟩

theorem afterLiquidity_resume (caller callee : Frame) (ret : Ident) (evm post : State)
    (hook : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords)
    (delta fees : UInt256) (data : ByteArray) (z : Bool) (out : ByteArray) :
    resumeCallResult caller ret (afterLiquidityResult callee evm post hook key p delta fees data z out) =
      afterLiquidityInvocationResult caller ret evm post hook key p delta fees data z out := by
  unfold afterLiquidityResult afterLiquidityBlockResult afterLiquiditySelectedResult
    afterLiquidityBranchResult afterLiquidityFinishResult afterLiquidityInvocationResult
  split_ifs <;> simp_all only [continueBlockResult, afterLiquidityReturnResult,
    afterLiquidityReturnedCaller, afterLiquidityReturnedHook, if_pos, if_neg, true_and,
    finishBlockResult, resumeCallResult, resumeAfterInternalCall, collapseReturns] <;> try rfl
  rename_i hbad
  rw [if_pos hbad.2]

theorem afterLiquidityCall {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {delta fees : UInt256} {data out : ByteArray}
    {z : Bool} {es ek ep ed ee eb : Expr}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (modifyLiquidityParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.int (EVM.signed delta)))
    (he : evalExpr? config f evm ee = .ok (.int (EVM.signed fees)))
    (hb : evalExpr? config f evm eb = .ok (.bytes data))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hcall : evm.executionEnv.source ≠ hook → afterLiquidityActive hook p → callViaEVM evm hook 0
      (afterLiquidityPayload (afterLiquidityAdd p) evm.executionEnv.source key p delta fees data) (z, post, out))
    (ret : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_afterModifyLiquidity" [es, ek, ep, ed, ee, eb] ret)
      (afterLiquidityInvocationResult f ret evm post hook key p delta fees data z out) := by
  have hcf : (afterLiquidityCallFrame f hook key p delta fees data).contract = contract := by
    dsimp only [afterLiquidityCallFrame]
    exact hf
  have hbody := afterLiquidityBody (f := afterLiquidityCallFrame f hook key p delta fees data)
    (hook := hook) (key := key) (p := p) (delta := delta) (fees := fees) (data := data) (z := z) (out := out) hcf
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
        ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))))) hc hl hu hcall
  have hinvoke := internalCallFunctionExec (caller := f) (callee := afterLiquidityFunction)
    (args := [es, ek, ep, ed, ee, eb]) (retVar := ret)
    (argVals := [.address hook, poolKeyValue key, modifyLiquidityParamsValue p,
      .int (EVM.signed delta), .int (EVM.signed fees), .bytes data])
    (by simp only [evalExprs?, hs, hk, hp, hd, he, hb, bind, EvalResult.bind, pure])
    (by rw [hf]; exact afterLiquidity_lookup) rfl hbody
  simpa only [afterLiquidity_resume] using hinvoke

end Benchmarks.UniswapV4PoolManager
