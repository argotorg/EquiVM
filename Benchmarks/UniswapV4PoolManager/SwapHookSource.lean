import Benchmarks.UniswapV4PoolManager.SwapHookABI
import Benchmarks.UniswapV4PoolManager.InitializeHookSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapHookPayloadExpr (after : Bool) (sender key params delta data : Expr) : Expr :=
  .abiEncodeCall (swapHookName after)
    ([sender, poolKeyTupleExpr key, swapParamsTupleExpr params] ++ (if after then [delta] else []) ++ [data])

theorem swapHookPayload_eval {f : Frame} {evm : State} {sender : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {delta : UInt256} {data : ByteArray}
    {es ek ep ed eb : Expr} (after : Bool) (hs : evalExpr? config f evm es = .ok (.address sender))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (swapParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.int (EVM.signed delta)))
    (hb : evalExpr? config f evm eb = .ok (.bytes data))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160) :
    evalExpr? config f evm (swapHookPayloadExpr after es ek ep ed eb) =
      .ok (.bytes (swapHookPayload after sender key p delta data)) := by
  have hkey := evalPoolKeyTuple hk
  have hparams := evalSwapParamsTuple hp
  apply evalABIEncodeCall (he := swapHookEncode after sender delta data hc hl)
  cases after <;> simp only [swapHookValues, Bool.false_eq_true, if_false, if_true,
    List.cons_append, List.nil_append, evalExprList?, hs, hkey, hparams, hd, hb,
    bind, EvalResult.bind, pure]

end Benchmarks.UniswapV4PoolManager
