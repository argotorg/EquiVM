import Benchmarks.CompoundIII.Comet.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES Reasoning.SolmBody.evalExpr_storage_scalar_value to aggregate values.
theorem evalExpr_storage_typed {cfg : Config} {frame : Frame} {evm : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {value : Value}
    (hbase : frame.locals.get? slot.base = none)
    (her : evalStorageRef cfg frame evm slot = .ok er)
    (hty : storageTypeAt? frame.contract.storage er = some ty)
    (hread : cfg.storageBackend.read er ty evm = .ok value) :
    evalExpr? cfg frame evm (.storage slot) = .ok value := by
  rw [evalExpr?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind, hread]

-- LIBRARY CANDIDATE: read a Solidity structure from the corresponding per-field reads.
theorem solidityReadFields_from_fields (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (fields : List (Ident × StorageType)) (values : List (Ident × Value))
    (hfields : List.Forall₂ (fun f v ↦ f.1 = v.1 ∧
      solidityReadStorage? layout evm { er with steps := er.steps ++ [.field f.1] } f.2 = .ok v.2)
      fields values) : solidityReadFields? layout evm er fields = .ok values := by
  induction hfields with
  | nil => simp only [solidityReadFields?]
  | @cons f v fields values hhead htail ih =>
      rcases f with ⟨name, ty⟩
      rcases v with ⟨actual, value⟩
      obtain ⟨rfl, hv⟩ := hhead
      simp only [solidityReadFields?, hv, ih, bind, EvalResult.bind, pure]

-- LIBRARY CANDIDATE: compose typed aggregate writes in source field order.
theorem solidityWriteFields_cons {layout : StorageLayout} {evm evm' evm'' : EVM.State}
    {er : EvaledStorageRef} {name : Ident} {ty : StorageType} {value : Value}
    {types : List (Ident × StorageType)} {values : List (Ident × Value)}
    (hhead : solidityWriteStorage? layout evm
      { er with steps := er.steps ++ [.field name] } ty value = .ok evm')
    (htail : solidityWriteFields? layout evm' er types values = .ok evm'') :
    solidityWriteFields? layout evm er ((name, ty) :: types) ((name, value) :: values) =
      .ok evm'' := by
  rw [solidityWriteFields?]
  simpa only [if_pos rfl, hhead, bind, EvalResult.bind] using htail

-- GENERALIZES Reasoning.SolmBody.assignStorageRef_storage_scalar to aggregate values.
theorem assignStorageRef_storage_typed {cfg : Config} {frame : Frame}
    {evm evm' : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {ty : StorageType} {value : Value}
    (hbase : frame.locals.get? slot.base = none)
    (her : evalStorageRef cfg frame evm slot = .ok er)
    (hty : storageTypeAt? frame.contract.storage er = some ty)
    (hwrite : cfg.storageBackend.write er ty value evm = .ok evm') :
    assignStorageRef? cfg frame evm .storage slot value = .ok (frame, evm') := by
  simp only [assignStorageRef?, resolveStorageRef?_ok hbase her hty, hwrite,
    bind, EvalResult.bind, pure]

end Benchmarks.CompoundIII.Comet
