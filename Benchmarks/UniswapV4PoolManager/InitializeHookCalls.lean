import Benchmarks.UniswapV4PoolManager.InitializeHookSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem beforeInitializeCall {f : Frame} {evm evm' : EVM.State} {hook : AccountAddress}
    {key : PoolKeyWords} {price : UInt256} {z : Bool} {out : ByteArray} {es ek ep : Expr}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (.int (Int.ofNat price.toNat)))
    (hc : PoolKeyCanonical key) (hprice : price.toNat < 2^160)
    (hcall : hookEnabled evm.executionEnv.source hook ⟨8192⟩ →
      callViaEVM evm hook 0 (beforeInitializePayload evm.executionEnv.source key price) (z, evm', out))
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_beforeInitialize" [es, ek, ep] retVar)
      (resumeCallResult f retVar (hookInvocationResult f evm evm'
        (hookEnabled evm.executionEnv.source hook ⟨8192⟩) z
        (beforeInitializePayload evm.executionEnv.source key price) out)) := by
  let locals : Store := (((∅ : Store).insert "sqrtPriceX96" (.int (Int.ofNat price.toNat))).insert
    "key" (poolKeyValue key)).insert "self" (.address hook)
  obtain ⟨f', hb⟩ := beforeInitializeBody (f := {f with locals := locals}) hf
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "key") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("key" == "sqrtPriceX96") = false)
      (by decide : ("self" == "sqrtPriceX96") = false)).trans (store_get_self _ _ _)) hc hprice hcall
  have hargs : evalExprs? config f evm [es, ek, ep] =
      .ok [.address hook, poolKeyValue key, .int (Int.ofNat price.toNat)] := by
    simp only [evalExprs?, hs, hk, hp, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "Hooks_beforeInitialize" = some beforeInitializeFunction.toCallable := by
    rw [hf]; exact beforeInitialize_lookup
  have hr := internalCallFunctionExec (retVar := retVar) hargs hlookup rfl hb
  simpa only [hookInvocationResult, resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_reverted] using hr

theorem afterInitializeCall {f : Frame} {evm evm' : EVM.State} {hook : AccountAddress}
    {key : PoolKeyWords} {price tick : UInt256} {z : Bool} {out : ByteArray} {es ek ep et : Expr}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (.int (Int.ofNat price.toNat)))
    (ht : evalExpr? config f evm et = .ok (.int (EVM.signed tick)))
    (hc : PoolKeyCanonical key) (hprice : price.toNat < 2^160) (htick : int24Canonical tick)
    (hcall : hookEnabled evm.executionEnv.source hook ⟨4096⟩ →
      callViaEVM evm hook 0 (afterInitializePayload evm.executionEnv.source key price tick) (z, evm', out))
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_afterInitialize" [es, ek, ep, et] retVar)
      (resumeCallResult f retVar (hookInvocationResult f evm evm'
        (hookEnabled evm.executionEnv.source hook ⟨4096⟩) z
        (afterInitializePayload evm.executionEnv.source key price tick) out)) := by
  let locals : Store := ((((∅ : Store).insert "tick" (.int (EVM.signed tick))).insert
    "sqrtPriceX96" (.int (Int.ofNat price.toNat))).insert "key" (poolKeyValue key)).insert "self" (.address hook)
  obtain ⟨f', hb⟩ := afterInitializeBody (f := {f with locals := locals}) hf
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "key") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("key" == "sqrtPriceX96") = false)
      (by decide : ("self" == "sqrtPriceX96") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("sqrtPriceX96" == "tick") = false)
      (by decide : ("key" == "tick") = false) (by decide : ("self" == "tick") = false)).trans
      (store_get_self _ _ _)) hc hprice htick hcall
  have hargs : evalExprs? config f evm [es, ek, ep, et] =
      .ok [.address hook, poolKeyValue key, .int (Int.ofNat price.toNat), .int (EVM.signed tick)] := by
    simp only [evalExprs?, hs, hk, hp, ht, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "Hooks_afterInitialize" = some afterInitializeFunction.toCallable := by
    rw [hf]; exact afterInitialize_lookup
  have hr := internalCallFunctionExec (retVar := retVar) hargs hlookup rfl hb
  simpa only [hookInvocationResult, resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_reverted] using hr

end Benchmarks.UniswapV4PoolManager
