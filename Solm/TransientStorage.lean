import Solm.SolidityStorage

/-!
# Solidity transient storage

Transient storage uses the same slot representation and packing as persistent storage, in a
separate map belonging to the executing account. Reuse the Solidity backend by exchanging only
that account's maps on entry and restoring them after every successful mutation. Reverts and
errors carry no updated state. Call rollback and transaction-end clearing remain EVM operations.

The aggregate operations are also available to Solm specs; Solidity's high-level `transient`
declarations currently support only value types.
-/

namespace Solm

/-- The Solidity backend operating on `Account.tstorage`. Its locator is state-independent. -/
def solidityTransientStorageBackend (layout : StorageLayout) : StorageBackend :=
  let backend := solidityStorageBackend layout
  { read := fun er ty evm ↦ backend.read er ty (EVM.swapCodeOwnerMaps evm)
    write := fun er ty value evm ↦ do
      let evm' ← backend.write er ty value (EVM.swapCodeOwnerMaps evm)
      pure (EVM.swapCodeOwnerMaps evm')
    clear := fun er ty evm ↦ do
      let evm' ← backend.clear er ty (EVM.swapCodeOwnerMaps evm)
      pure (EVM.swapCodeOwnerMaps evm')
    length := fun er ty evm ↦ backend.length er ty (EVM.swapCodeOwnerMaps evm)
    push := fun er ty value evm ↦ do
      let evm' ← backend.push er ty value (EVM.swapCodeOwnerMaps evm)
      pure (EVM.swapCodeOwnerMaps evm')
    pop := fun er ty evm ↦ do
      let evm' ← backend.pop er ty (EVM.swapCodeOwnerMaps evm)
      pure (EVM.swapCodeOwnerMaps evm')
    locate? := layout }

@[simp] theorem solidityTransientStorageBackend_locate (layout : StorageLayout) :
    (solidityTransientStorageBackend layout).locate? = layout := rfl

@[simp] theorem solidityTransientStorageBackend_read_elem (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : ABI.ElemType) (evm : EVM.State) (loc : StorageLoc)
    (hloc : layout er = some (.leaf loc)) :
    (solidityTransientStorageBackend layout).read er (.elem ty) evm =
      .ok (transientLocLoad evm loc) := by
  exact solidityStorageBackend_read_elem layout er ty (EVM.swapCodeOwnerMaps evm) loc hloc

@[simp] theorem solidityTransientStorageBackend_write_elem (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : ABI.ElemType) (value : Value) (evm evm' : EVM.State)
    (loc : StorageLoc) (hloc : layout er = some (.leaf loc))
    (hstore : transientLocStore evm loc value = some evm') :
    (solidityTransientStorageBackend layout).write er (.elem ty) value evm = .ok evm' := by
  unfold transientLocStore at hstore
  cases h : storageLocStore (EVM.swapCodeOwnerMaps evm) loc value with
  | none => simp [h] at hstore
  | some evm1 =>
      simp only [h, Option.map_some, Option.some.injEq] at hstore
      subst evm'
      change (do
        let evm2 ← (solidityStorageBackend layout).write er (.elem ty) value
          (EVM.swapCodeOwnerMaps evm)
        pure (EVM.swapCodeOwnerMaps evm2)) = _
      rw [solidityStorageBackend_write_elem layout er ty value _ evm1 loc hloc h]
      rfl

end Solm
