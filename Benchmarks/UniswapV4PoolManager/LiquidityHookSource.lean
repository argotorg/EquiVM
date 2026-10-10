import Benchmarks.UniswapV4PoolManager.LiquidityHookABI
import Benchmarks.UniswapV4PoolManager.InitializeHookSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def liquidityHookPayloadExpr (after add : Bool) (sender key params delta fees data : Expr) : Expr :=
  .abiEncodeCall (liquidityHookName after add)
    ([sender, poolKeyTupleExpr key, modifyLiquidityTupleExpr params] ++
      (if after then [delta, fees] else []) ++ [data])

theorem liquidityHookPayload_eval {f : Frame} {evm : State} {sender : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {delta fees : UInt256} {data : ByteArray}
    {es ek ep ed ef eb : Expr} (after add : Bool)
    (hs : evalExpr? config f evm es = .ok (.address sender))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (modifyLiquidityParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.int (EVM.signed delta)))
    (hf : evalExpr? config f evm ef = .ok (.int (EVM.signed fees)))
    (hb : evalExpr? config f evm eb = .ok (.bytes data))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) :
    evalExpr? config f evm (liquidityHookPayloadExpr after add es ek ep ed ef eb) =
      .ok (.bytes (liquidityHookPayload after add sender key p delta fees data)) := by
  have hkey := evalPoolKeyTuple hk
  have hparams := evalModifyLiquidityTuple hp
  apply evalABIEncodeCall (he := liquidityHookEncode after add sender delta fees data hc hl hu)
  cases after <;>
    simp only [liquidityHookValues, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append, evalExprList?, hs, hkey, hparams, hd, hf, hb,
      bind, EvalResult.bind, pure]

end Benchmarks.UniswapV4PoolManager
