import Benchmarks.UniswapV4PoolManager.PoolKeySource
import Benchmarks.UniswapV4PoolManager.SourceComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def donatePreludeFrame (locals imms : Store) (evm : State) (key : PoolKeyWords) : Frame :=
  {contract := contract, immutables := imms,
   locals := ((locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
     "key" (poolKeyValue key)).insert "delta" (.int 0)}

theorem donatePreludeSource {locals imms : Store} {evm : State} {key : PoolKeyWords}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hk : locals.get? "key" = some (.tuple (poolKeyValues key))) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (donateTransition.body.take 5) (.ok (donatePreludeFrame locals imms evm key) evm) := by
  apply nonpayableCalldataBlock hwv hhi
  have hkey := poolKeyFromTuple_eval (evalLocalValue (cfg := config)
    (f := calldataFrame contract locals imms evm) (evm := evm)
    ((store_get_ne _ _ (by decide : ("__calldata" == "key") = false)).trans hk))
  exact ExecBlock.consNormal (ExecStmt.letDecl hkey)
    (execBlock_singleton (ExecStmt.letDecl (by simp only [evalExpr?, pure])))

end Benchmarks.UniswapV4PoolManager
