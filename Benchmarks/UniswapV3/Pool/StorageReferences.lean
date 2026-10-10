import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.SolmBody.evalExpr_storage_scalar to resolved local storage references.
theorem evalExpr_storage_resolved {cfg : Config} {layout : StorageLayout}
    {frame : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    (hresolve : resolveStorageRef? cfg frame evm slot = .ok (er, .elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc)) :
    evalExpr? cfg frame evm (.storage slot) = .ok (storageLocLoad evm loc) := by
  rw [evalExpr?]
  simp only [hresolve, bind, EvalResult.bind, readStorage?_elem hbackend hloc]

-- GENERALIZES Reasoning.SolmBody.assignStorageRef_storage_scalar_value to resolved aliases.
theorem assignStorageRef_resolved_scalar {cfg : Config} {layout : StorageLayout}
    {frame : Frame} {evm evm' : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc} {value : Value}
    (hresolve : resolveStorageRef? cfg frame evm slot = .ok (er, .elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg frame evm .storage slot value = .ok (frame, evm') := by
  simp [assignStorageRef?, hresolve, hbackend, solidityStorageBackend,
    solidityWriteStorage?, solidityLeafLoc?_of_leaf hloc, hstore,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.UniswapV3.Pool
