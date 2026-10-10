import Benchmarks.UniswapV4PoolManager.BeforeLiquiditySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem beforeLiquidity_lookup : lookupCallable? contract "Hooks_beforeModifyLiquidity" =
    some beforeLiquidityFunction.toCallable := rfl

def beforeLiquidityCallFrame (f : Frame) (hook : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (data : ByteArray) : Frame :=
  {f with locals := ((((∅ : Store).insert "hookData" (.bytes data)).insert "params"
    (modifyLiquidityParamsValue p)).insert "key" (poolKeyValue key)).insert "self" (.address hook)}

def beforeLiquidityInvocationResult (f : Frame) (ret : Ident) (evm post : State) (hook : AccountAddress)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  let done := fun state => ExecResult.ok {f with locals := f.locals.insert ret .unit} state
  let called := fun add => if z = true ∧ hookReplyValid (beforeLiquidityPayload add evm.executionEnv.source key p data) out
    then done post else .reverted
  if evm.executionEnv.source = hook then done evm
  else if beforeLiquidityEnabled hook p true then called true
  else if beforeLiquidityEnabled hook p false then called false
  else done evm

theorem beforeLiquidity_resume (caller callee : Frame) (ret : Ident) (evm post : State) (hook : AccountAddress)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (data : ByteArray) (z : Bool) (out : ByteArray) :
    resumeCallResult caller ret (beforeLiquidityResult callee evm post hook key p data z out) =
      beforeLiquidityInvocationResult caller ret evm post hook key p data z out := by
  simp only [beforeLiquidityResult, beforeLiquidityBlockResult, beforeLiquidityTailResult,
    hookPayloadResult, finishBlockResult_ite, finishBlockResult_ok, finishBlockResult_reverted,
    resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_reverted,
    beforeLiquidityInvocationResult]
  split_ifs <;> rfl

theorem beforeLiquidityCall {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {data out : ByteArray} {z : Bool} {es ek ep ed : Expr}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (modifyLiquidityParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.bytes data))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hcall : ∀ add, evm.executionEnv.source ≠ hook → beforeLiquidityEnabled hook p add →
      callViaEVM evm hook 0 (beforeLiquidityPayload add evm.executionEnv.source key p data) (z, post, out))
    (ret : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_beforeModifyLiquidity" [es, ek, ep, ed] ret)
      (beforeLiquidityInvocationResult f ret evm post hook key p data z out) := by
  rw [← beforeLiquidity_resume f (beforeLiquidityCallFrame f hook key p data)]
  apply internalCallFunctionExec (argVals := [.address hook, poolKeyValue key, modifyLiquidityParamsValue p, .bytes data])
    (by simp only [evalExprs?, hs, hk, hp, hd, bind, EvalResult.bind, pure])
    (by rw [hf]; exact beforeLiquidity_lookup) rfl
  exact beforeLiquidityBody hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))) hc hl hu hcall

end Benchmarks.UniswapV4PoolManager
