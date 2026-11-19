import Benchmarks.Midnight.PackedFields

/-! Source evaluation through local Solidity storage aliases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def midnightStorageLayout : StorageLayout := solidityLayout! [contract.structs] [contract.storage]

-- LIBRARY CANDIDATE: field selection through an evaluated storage alias.
theorem resolveStorageAliasField {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name field : Ident} {er : EvaledStorageRef} {ty fieldTy : StorageType}
    (hget : frame.locals.get? name = some (.storageRef er ty))
    (hty : storageTypeStep? ty (.field field) = some fieldTy) :
    resolveStorageRef? cfg frame evm { base := name, steps := [.field field] } =
      .ok ({ er with steps := er.steps ++ [.field field] }, fieldTy) := by
  simp only [resolveStorageRef?, hget, evalStorageRefFrom?, evalStorageRefStep, hty,
    EvalResult.ofOption, EvalResult.bind, pure, bind]

-- LIBRARY CANDIDATE: a scalar Solidity read through a local storage alias.
theorem evalStorageAliasField {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name field : Ident} {er : EvaledStorageRef} {ty : StorageType} {t : ElemType}
    {layout : StorageLayout} {loc : StorageLoc} {value : Value}
    (hget : frame.locals.get? name = some (.storageRef er ty))
    (hty : storageTypeStep? ty (.field field) = some (.elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout { er with steps := er.steps ++ [.field field] } = some (.leaf loc))
    (hload : storageLocLoad evm loc = value) :
    evalExpr? cfg frame evm (.storage { base := name, steps := [.field field] }) =
      .ok value := by
  rw [evalExpr?]
  simp only [resolveStorageAliasField hget hty, bind, EvalResult.bind,
    readStorage?_elem hbackend hloc, hload]

-- LIBRARY CANDIDATE: resolve a mapping root for binding a local storage alias.
theorem resolveBytes32Mapping {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name arg : Ident} {key : UInt256} {ty : StorageType}
    (hbase : frame.locals.get? name = none)
    (hget : frame.locals.get? arg = some (wordBytes32Value key))
    (hty : storageTypeAt? frame.contract.storage { base := name, steps :=
      [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))] } = some ty) :
    resolveStorageRef? cfg frame evm { base := name, steps := [.mindex (.var arg)] } =
      .ok ({ base := name, steps :=
        [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))] }, ty) := by
  apply resolveStorageRef?_ok hbase ?_ hty
  have hlen : (EVM.Word.toBytesBE key).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size key
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
    EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
    hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]

-- LIBRARY CANDIDATE: scalar writes through a local Solidity storage alias.
theorem assignStorageAliasField {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {name field : Ident} {er : EvaledStorageRef} {ty : StorageType} {t : ElemType}
    {layout : StorageLayout} {loc : StorageLoc} {value : Value}
    (hget : frame.locals.get? name = some (.storageRef er ty))
    (hty : storageTypeStep? ty (.field field) = some (.elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout { er with steps := er.steps ++ [.field field] } = some (.leaf loc))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg frame evm .storage { base := name, steps := [.field field] } value =
      .ok (frame, evm') := by
  simp only [assignStorageRef?, resolveStorageAliasField hget hty, hbackend,
    solidityStorageBackend, solidityWriteStorage?, solidityLeafLoc?_of_leaf hloc,
    hstore, EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
