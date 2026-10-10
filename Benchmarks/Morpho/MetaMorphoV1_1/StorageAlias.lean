import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon

/-! Scalar storage access through a resolved local storage reference. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: field resolution from a typed local storage alias.
theorem resolveStorageAliasField {cfg : Config} {frame : Frame} {evm : State}
    {name field : Ident} {er : EvaledStorageRef} {ty fieldTy : StorageType}
    (halias : frame.locals.get? name = some (.storageRef er ty))
    (hfield : storageTypeStep? ty (.field field) = some fieldTy) :
    resolveStorageRef? cfg frame evm ⟨name, [.field field]⟩ =
      .ok ({ er with steps := er.steps ++ [.field field] }, fieldTy) := by
  simp only [resolveStorageRef?, halias, evalStorageRefFrom?, evalStorageRefStep,
    hfield, EvalResult.ofOption, bind, EvalResult.bind, pure]

-- GENERALIZES Reasoning.SolmBody.evalExpr_storage_scalar_value to resolved storage aliases.
theorem evalStorageResolved {cfg : Config} {layout : StorageLayout}
    {frame : Frame} {evm : State} {ref : StorageRef} {er : EvaledStorageRef}
    {t : ElemType} {loc : StorageLoc} {value : Value}
    (hresolve : resolveStorageRef? cfg frame evm ref = .ok (er, .elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc)) (hload : storageLocLoad evm loc = value) :
    evalExpr? cfg frame evm (.storage ref) = .ok value := by
  rw [evalExpr?]
  simp only [hresolve, bind, EvalResult.bind, readStorage?_elem hbackend hloc, hload]

-- GENERALIZES Reasoning.SolmBody.assignStorageRef_storage_scalar_value to resolved aliases.
theorem assignStorageResolved {cfg : Config} {layout : StorageLayout}
    {frame : Frame} {evm evm' : State} {ref : StorageRef} {er : EvaledStorageRef}
    {t : ElemType} {loc : StorageLoc} {value : Value}
    (hresolve : resolveStorageRef? cfg frame evm ref = .ok (er, .elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg frame evm .storage ref value = .ok (frame, evm') := by
  simp only [assignStorageRef?, hresolve, hbackend, bind, EvalResult.bind,
    solidityStorageBackend, solidityWriteStorage?, solidityLeafLoc?_of_leaf hloc,
    hstore, EvalResult.ofOption, pure]

end Benchmarks.Morpho.MetaMorphoV1_1
