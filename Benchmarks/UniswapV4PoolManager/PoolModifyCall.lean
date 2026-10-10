import Benchmarks.UniswapV4PoolManager.PoolModifySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyCallFrame (f : Frame) (id : UInt256) (p : PoolModifyParams) : Frame :=
  {f with locals := ((∅ : Store).insert "params" (poolModifyParamsValue p)).insert "self" (poolRefValue id)}

theorem poolModifyCall {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams} {es ep : Expr}
    (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (hp : evalExpr? config f evm ep = .ok (poolModifyParamsValue p))
    (hlo : int24Canonical p.lower) (hup : int24Canonical p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Pool_modifyLiquidity" [es, ep] ret)
      (resumeCallResult f ret (poolModifyResult (poolModifyCallFrame f id p) evm id p)) := by
  have hbody := poolModifyBody (f := poolModifyCallFrame f id p) (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "params") = false)).trans (store_get_self _ _ _)) hlo hup hdlo hdhi
  exact internalCallFunctionExec (caller := f) (name := "Pool_modifyLiquidity") (retVar := ret)
    (args := [es, ep]) (argVals := [poolRefValue id, poolModifyParamsValue p])
    (by simp only [evalExprs?, hs, hp, bind, EvalResult.bind, pure])
    (by rw [hf]; exact poolModify_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
