import Benchmarks.UniswapV4PoolManager.PoolKeySource
import Benchmarks.UniswapV4PoolManager.SourceComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def initializePreludeFrame (locals imms : Store) (evm : EVM.State) (key : PoolKeyWords) : Frame :=
  {contract := contract, immutables := imms,
   locals := (((locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
     "key" (poolKeyValue key)).insert "tick" (.int 0))}

theorem initializePreludeSource {locals imms : Store} {evm : EVM.State} {key : PoolKeyWords}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hk : locals.get? "key" = some (.tuple (poolKeyValues key))) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (initializeTransition.body.take 5) (.ok (initializePreludeFrame locals imms evm key) evm) := by
  apply nonpayableCalldataBlock hwv hhi
  have hkey := poolKeyFromTuple_eval (evalLocalValue (cfg := config)
    (f := calldataFrame contract locals imms evm) (evm := evm)
    ((store_get_ne _ _ (by decide : ("__calldata" == "key") = false)).trans hk))
  exact ExecBlock.consNormal (ExecStmt.letDecl hkey)
    (execBlock_singleton (ExecStmt.letDecl (by simp only [evalExpr?, pure])))

end Benchmarks.UniswapV4PoolManager
