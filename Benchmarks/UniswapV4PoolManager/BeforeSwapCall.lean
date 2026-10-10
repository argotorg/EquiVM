import Benchmarks.UniswapV4PoolManager.BeforeSwapSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem beforeSwap_lookup : lookupCallable? contract "Hooks_beforeSwap" = some beforeSwapFunction.toCallable := rfl
def beforeSwapCallFrame (f : Frame) (hook : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (data : ByteArray) : Frame :=
  {f with locals := ((((∅ : Store).insert "hookData" (.bytes data)).insert "params"
    (swapParamsValue p)).insert "key" (poolKeyValue key)).insert "self" (.address hook)}

theorem beforeSwapCall {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {data out : ByteArray} {z : Bool} {es ek ep ed : Expr}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (swapParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.bytes data))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hcall : evm.executionEnv.source ≠ hook → beforeSwapActive hook →
      callViaEVM evm hook 0 (beforeSwapPayload evm.executionEnv.source key p data) (z, post, out))
    (ret : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_beforeSwap" [es, ek, ep, ed] ret)
      (resumeCallResult f ret (beforeSwapResult (beforeSwapCallFrame f hook key p data) evm post hook key p data z out)) := by
  apply internalCallFunctionExec (argVals := [.address hook, poolKeyValue key, swapParamsValue p, .bytes data])
    (by simp only [evalExprs?, hs, hk, hp, hd, bind, EvalResult.bind, pure])
    (by rw [hf]; exact beforeSwap_lookup) rfl
  exact beforeSwapBody hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))) hc hl hcall

end Benchmarks.UniswapV4PoolManager
