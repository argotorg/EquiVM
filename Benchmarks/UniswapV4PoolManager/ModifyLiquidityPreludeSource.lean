import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams
import Benchmarks.UniswapV4PoolManager.SourceComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityFromTuple (e : Expr) : Expr := .structLit "ModifyLiquidityParams_8903"
  [("tickLower", .tupleGet e 0), ("tickUpper", .tupleGet e 1),
   ("liquidityDelta", .tupleGet e 2), ("salt", .tupleGet e 3)]

theorem modifyLiquidityFromTuple_eval {cfg : Config} {f : Frame} {evm : State} {e : Expr}
    {p : ModifyLiquidityWords}
    (he : evalExpr? cfg f evm e = .ok (.tuple (modifyLiquidityValues p))) :
    evalExpr? cfg f evm (modifyLiquidityFromTuple e) = .ok (modifyLiquidityParamsValue p) := by
  have h0 := evalTupleProjection he (i := 0) rfl
  have h1 := evalTupleProjection he (i := 1) rfl
  have h2 := evalTupleProjection he (i := 2) rfl
  have h3 := evalTupleProjection he (i := 3) rfl
  simp only [modifyLiquidityFromTuple, evalExpr?, evalStructFields?, h0, h1, h2, h3,
    bind, EvalResult.bind, pure]
  rfl

def modifyLiquidityPreludeFrame (locals imms : Store) (evm : State) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) : Frame :=
  {contract := contract, immutables := imms,
   locals := ((((locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
     "key" (poolKeyValue key)).insert "params" (modifyLiquidityParamsValue p)).insert
     "callerDelta" (.int 0)).insert "feesAccrued" (.int 0)}

theorem modifyLiquidityPreludeSource {locals imms : Store} {evm : State} {key : PoolKeyWords}
    {p : ModifyLiquidityWords} (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hk : locals.get? "key" = some (.tuple (poolKeyValues key)))
    (hp : locals.get? "params" = some (.tuple (modifyLiquidityValues p))) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (modifyLiquidityTransition.body.take 7)
      (.ok (modifyLiquidityPreludeFrame locals imms evm key p) evm) := by
  apply nonpayableCalldataBlock hwv hhi
  have hkey := poolKeyFromTuple_eval (evalLocalValue (cfg := config)
    (f := calldataFrame contract locals imms evm) (evm := evm)
    ((store_get_ne _ _ (by decide : ("__calldata" == "key") = false)).trans hk))
  have hparams := modifyLiquidityFromTuple_eval (evalLocalValue (cfg := config)
    (f := {calldataFrame contract locals imms evm with
      locals := (calldataFrame contract locals imms evm).locals.insert "key" (poolKeyValue key)})
    (evm := evm) ((store_get_ne2 _ _ _ (by decide : ("__calldata" == "params") = false)
      (by decide : ("key" == "params") = false)).trans hp))
  exact ExecBlock.consNormal (ExecStmt.letDecl hkey)
    (ExecBlock.consNormal (ExecStmt.letDecl hparams)
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
        (execBlock_singleton (ExecStmt.letDecl (by simp only [evalExpr?, pure])))))

end Benchmarks.UniswapV4PoolManager
