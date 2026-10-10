import Benchmarks.UniswapV4PoolManager.SwapParams
import Benchmarks.UniswapV4PoolManager.SourceComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapParamsFromTuple (e : Expr) : Expr := .structLit "SwapParams_8914"
  [("zeroForOne", .tupleGet e 0), ("amountSpecified", .tupleGet e 1), ("sqrtPriceLimitX96", .tupleGet e 2)]

theorem swapParamsFromTuple_eval {cfg : Config} {f : Frame} {evm : State} {e : Expr}
    {p : SwapParamsWords} (he : evalExpr? cfg f evm e = .ok (.tuple (swapParamsValues p))) :
    evalExpr? cfg f evm (swapParamsFromTuple e) = .ok (swapParamsValue p) := by
  have h0 := evalTupleProjection he (i := 0) rfl
  have h1 := evalTupleProjection he (i := 1) rfl
  have h2 := evalTupleProjection he (i := 2) rfl
  simp only [swapParamsFromTuple, evalExpr?, evalStructFields?, h0, h1, h2, bind, EvalResult.bind, pure]
  rfl

def swapPreludeFrame (locals imms : Store) (evm : State) (key : PoolKeyWords) (p : SwapParamsWords) : Frame :=
  {contract := contract, immutables := imms,
   locals := (((locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
     "key" (poolKeyValue key)).insert "params" (swapParamsValue p)).insert "swapDelta" (.int 0)}

theorem swapPreludeSource {locals imms : Store} {evm : State} {key : PoolKeyWords} {p : SwapParamsWords}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hk : locals.get? "key" = some (.tuple (poolKeyValues key)))
    (hp : locals.get? "params" = some (.tuple (swapParamsValues p))) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (swapTransition.body.take 6) (.ok (swapPreludeFrame locals imms evm key p) evm) := by
  apply nonpayableCalldataBlock hwv hhi
  have hkey := poolKeyFromTuple_eval (evalLocalValue (cfg := config)
    (f := calldataFrame contract locals imms evm) (evm := evm)
    ((store_get_ne _ _ (by decide : ("__calldata" == "key") = false)).trans hk))
  have hparams := swapParamsFromTuple_eval (evalLocalValue (cfg := config)
    (f := {calldataFrame contract locals imms evm with
      locals := (calldataFrame contract locals imms evm).locals.insert "key" (poolKeyValue key)})
    (evm := evm) ((store_get_ne2 _ _ _ (by decide : ("__calldata" == "params") = false)
      (by decide : ("key" == "params") = false)).trans hp))
  exact ExecBlock.consNormal (ExecStmt.letDecl hkey)
    (ExecBlock.consNormal (ExecStmt.letDecl hparams)
      (execBlock_singleton (ExecStmt.letDecl (by simp only [evalExpr?, pure]))))

end Benchmarks.UniswapV4PoolManager
