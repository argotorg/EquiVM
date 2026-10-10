import Benchmarks.UniswapV4PoolManager.AfterSwapSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem afterSwap_lookup : lookupCallable? contract "Hooks_afterSwap" = some afterSwapFunction.toCallable := rfl
def afterSwapCallFrame (f : Frame) (hook : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (delta before : UInt256) (data : ByteArray) : Frame :=
  {f with locals := ((((((∅ : Store).insert "beforeSwapHookReturn" (.int (EVM.signed before))).insert
    "hookData" (.bytes data)).insert "swapDelta" (.int (EVM.signed delta))).insert "params"
    (swapParamsValue p)).insert "key" (poolKeyValue key)).insert "self" (.address hook)}

theorem afterSwapCall {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {delta before : UInt256} {data out : ByteArray}
    {z : Bool} {es ek ep ed eb er : Expr}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (swapParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.int (EVM.signed delta)))
    (hb : evalExpr? config f evm eb = .ok (.bytes data))
    (hr : evalExpr? config f evm er = .ok (.int (EVM.signed before)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hcall : evm.executionEnv.source ≠ hook → afterSwapActive hook →
      callViaEVM evm hook 0 (afterSwapPayload evm.executionEnv.source key p delta data) (z, post, out))
    (ret : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_afterSwap" [es, ek, ep, ed, eb, er] ret)
      (resumeCallResult f ret (afterSwapResult (afterSwapCallFrame f hook key p delta before data)
        evm post hook key p delta before data z out)) := by
  apply internalCallFunctionExec
    (argVals := [.address hook, poolKeyValue key, swapParamsValue p, .int (EVM.signed delta), .bytes data, .int (EVM.signed before)])
    (by simp only [evalExprs?, hs, hk, hp, hd, hb, hr, bind, EvalResult.bind, pure])
    (by rw [hf]; exact afterSwap_lookup) rfl
  exact afterSwapBody hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
        ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))))) hc hl hcall

end Benchmarks.UniswapV4PoolManager
