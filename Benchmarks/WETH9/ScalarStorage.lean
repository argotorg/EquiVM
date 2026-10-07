import Benchmarks.WETH9.Spec
import Reasoning.SolmBody

open Solm ABI Ethereum Reasoning.Theory

namespace Benchmarks.WETH9

/-- Scalar reads still use the ordinary Solidity leaf path in WETH9's string-aware backend. -/
theorem evalExpr_storage_scalar_value {solm : Frame} {evm : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    {value : Value}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef config solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some (.elem t))
    (hloc : config.storageBackend.locate? er = some (.leaf loc))
    (hload : storageLocLoad evm loc = value) :
    evalExpr? config solm evm (.storage slot) = .ok value := by
  rw [evalExpr?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind]
  change (weth9StorageBackend storageLayout).read er (.elem t) evm = .ok value
  have hloc' : storageLayout er = some (.leaf loc) := hloc
  simp [weth9StorageBackend, solidityStorageBackend, solidityReadStorage?,
    solidityLeafLoc?, hloc', hload, EvalResult.ofOption, EvalResult.bind, bind]
  rfl

/-- Scalar writes use the ordinary Solidity leaf path in WETH9's string-aware backend. -/
theorem assignStorageRef_storage_scalar_value {solm : Frame} {evm evm' : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc}
    {value : Value}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef config solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : config.storageBackend.locate? er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True)
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? config solm evm .storage slot value = .ok (solm, evm') := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind]
  have hloc' : storageLayout er = some (.leaf loc) := hloc
  rcases hleaf with ⟨t, rfl⟩ | ⟨name, rfl⟩
  · cases value <;> simp at hscalar ⊢
    all_goals simp [config, weth9StorageBackend, solidityStorageBackend,
      solidityWriteStorage?, solidityLeafLoc?, hloc', hstore,
      EvalResult.ofOption, EvalResult.bind, bind, pure]
  · cases value <;> simp at hscalar ⊢
    all_goals simp [config, weth9StorageBackend, solidityStorageBackend,
      solidityWriteStorage?, solidityLeafLoc?, hloc', hstore,
      EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem assignStorageRef_storage_scalar {solm : Frame} {evm evm' : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc}
    {n : Int}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef config solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : config.storageBackend.locate? er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : storageLocStore evm loc (.int n) = some evm') :
    assignStorageRef? config solm evm .storage slot (.int n) = .ok (solm, evm') := by
  exact assignStorageRef_storage_scalar_value hbase her hty hloc hleaf (by trivial) hstore

end Benchmarks.WETH9
