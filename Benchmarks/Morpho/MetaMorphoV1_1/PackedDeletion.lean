import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! Clearing all fields of the packed pending-update records clears their entire slot. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def clearFieldWord (old : UInt256) (offset size : Nat) : UInt256 :=
  UInt256.ofNat (old.toNat % 256 ^ offset +
    old.toNat / 256 ^ (offset + size) * 256 ^ (offset + size))

theorem storageLocStore_zero_field (evm : EVM.State) (loc : StorageLoc)
    (hbit : loc.bitOffset = none) :
    storageLocStore evm loc (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner loc.slot
        (clearFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot)
          loc.offset.val loc.size.val)) := by
  unfold storageLocStore
  simp only [valueToWord, wordOfInt_zero, bind, Option.bind, storageLocWriteWord, hbit]
  congr 2
  apply u256_inj
  change fromBytes' _ = (clearFieldWord _ _ _).toNat
  have hlenOld := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot)).2
  have hlenZero := (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2
  have hoff := loc.offset.isLt
  have hsize := loc.size.isLt
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    Nat.zero_mod, Nat.mul_zero, Nat.add_zero,
    List.length_append, List.length_take, hlenOld, hlenZero,
    Nat.min_eq_left (by omega : loc.offset.val ≤ 32),
    Nat.min_eq_left (by omega : loc.size.val ≤ 32)]
  have hp (n : Nat) : 2 ^ (8 * n) = 256 ^ n := by rw [Nat.pow_mul]
  rw [hp, Nat.mul_comm]
  unfold clearFieldWord
  symm
  apply UInt256.toNat_ofNat_of_lt
  have hbound := loc.hbound
  have hw := (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot).val.isLt
  have hdiv : 256 ^ loc.offset.val ∣ 256 ^ (loc.offset.val + loc.size.val) := by
    exact ⟨256 ^ loc.size.val, by rw [Nat.pow_add]⟩
  have hmod := Nat.mod_le
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot).toNat %
      256 ^ (loc.offset.val + loc.size.val)) (256 ^ loc.offset.val)
  rw [Nat.mod_mod_of_dvd _ hdiv] at hmod
  have hdecomp := Nat.mod_add_div
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot).toNat
      (256 ^ (loc.offset.val + loc.size.val))
  change _ < UInt256.size
  change (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot).toNat <
    UInt256.size at hw
  nlinarith

theorem storageStore_overwrite (evm : EVM.State) (addr : AccountAddress)
    (slot first last : UInt256) :
    Solm.EVM.storageStore (Solm.EVM.storageStore evm addr slot first) addr slot last =
      Solm.EVM.storageStore evm addr slot last := by
  rw [← storageStore_eq_accountMap_update
    (Solm.EVM.storageStore evm addr slot first) addr slot last,
    ← storageStore_eq_accountMap_update evm addr slot first,
    ← storageStore_eq_accountMap_update evm addr slot last]
  simp only [storageStore_accountMap]
  rw [← sstoreAccountMap_self_update]

theorem clearFieldWord_prefix_toNat (old : UInt256) (size : Nat) :
    (clearFieldWord old 0 size).toNat = old.toNat / 256 ^ size * 256 ^ size := by
  simp only [clearFieldWord, pow_zero, Nat.mod_one, Nat.zero_add]
  apply UInt256.toNat_ofNat_of_lt
  exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt

theorem clearFieldWord_append (old : UInt256) (offset size : Nat) :
    clearFieldWord (clearFieldWord old 0 offset) offset size =
      clearFieldWord old 0 (offset + size) := by
  unfold clearFieldWord at *
  have hp := clearFieldWord_prefix_toNat old offset
  unfold clearFieldWord at hp
  rw [hp]
  simp only [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
    pow_zero, Nat.mod_one]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_div_left _ (by positivity),
    Nat.div_div_eq_div_mul]

theorem clearFieldWord_all (old : UInt256) : clearFieldWord old 0 32 = ⟨0⟩ := by
  apply u256_inj
  rw [clearFieldWord_prefix_toNat]
  have hdiv : old.toNat / 256 ^ 32 = 0 := Nat.div_eq_of_lt old.val.isLt
  rw [hdiv]
  rfl

def clearFieldState (evm : EVM.State) (slot : UInt256) (offset size : Nat) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (clearFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset size)

theorem clearFieldState_load (evm : EVM.State) (slot : UInt256) (offset size : Nat) :
    Solm.EVM.storageLoad (clearFieldState evm slot offset size) evm.executionEnv.codeOwner
      slot = clearFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        offset size := by
  cases hacc : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
    rw [clearFieldState, storageStore_absent _ _ hacc]
    simp [Solm.EVM.storageLoad, State.lookupAccount,
      -Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option, clearFieldWord]
    rfl
  | some acc => exact storageLoad_storageStore_same_present _ _ hacc _ _

theorem clearFieldState_append (evm : EVM.State) (slot : UInt256) (offset size : Nat) :
    clearFieldState (clearFieldState evm slot 0 offset) slot offset size =
      clearFieldState evm slot 0 (offset + size) := by
  have hl := clearFieldState_load evm slot 0 offset
  unfold clearFieldState at hl ⊢
  rw [storageStore_executionEnv]
  rw [hl, clearFieldWord_append, storageStore_overwrite]

theorem clearFieldState_all (evm : EVM.State) (slot : UInt256) :
    clearFieldState evm slot 0 32 =
      Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩ := by
  rw [clearFieldState, clearFieldWord_all]

theorem clearStorage_field {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {ty : ElemType} (loc : StorageLoc)
    (hloc : layout er = some (.leaf loc)) (hbit : loc.bitOffset = none) :
    solidityClearStorage? layout evm er (.elem ty) =
      .ok (clearFieldState evm loc.slot loc.offset.val loc.size.val) := by
  simp only [solidityClearStorage?, solidityLeafLoc?, hloc, EvalResult.ofOption,
    bind, EvalResult.bind]
  rw [storageLocStore_zero_field evm loc hbit]
  rfl

theorem deleteStorage_pendingTimelock (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "pendingTimelock" = none) :
    deleteStorage? config { contract := contract, locals := locals, immutables := imms }
      evm ⟨"pendingTimelock", []⟩ =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨17⟩ ⟨0⟩) := by
  have hr := resolveStorageRef?_ok (cfg := config) (evm := evm)
    (solm := { contract := contract, locals := locals, immutables := imms })
    (slot := ⟨"pendingTimelock", []⟩) (er := ⟨"pendingTimelock", []⟩) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, bind, pure, EvalResult.bind])
    (show storageTypeAt? contract.storage ⟨"pendingTimelock", []⟩ = some
      (.struct "PendingUint192" [("value", .elem (.int (.uint ⟨192, by decide⟩))),
        ("validAt", .elem (.int (.uint ⟨64, by decide⟩)))]) from rfl)
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hr,
    Bool.false_eq_true, ↓reduceIte, hr, bind, EvalResult.bind]
  change solidityClearStorage? _ evm ⟨"pendingTimelock", []⟩
    (.struct "PendingUint192" _) = _
  rw [solidityClearStorage?, solidityClearFields?]
  rw [clearStorage_field
    ⟨⟨17⟩, 0, 24, by decide, none, .int (.uint ⟨192, by decide⟩)⟩ rfl rfl]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?]
  rw [clearStorage_field
    ⟨⟨17⟩, 24, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩ rfl rfl]
  simp only [bind, EvalResult.bind, solidityClearFields?]
  change EvalResult.ok (clearFieldState (clearFieldState evm ⟨17⟩ 0 24) ⟨17⟩ 24 8) = _
  rw [clearFieldState_append, clearFieldState_all]

theorem deleteStorage_pendingGuardian (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "pendingGuardian" = none) :
    deleteStorage? config { contract := contract, locals := locals, immutables := imms }
      evm ⟨"pendingGuardian", []⟩ =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨15⟩ ⟨0⟩) := by
  have hr := resolveStorageRef?_ok (cfg := config) (evm := evm)
    (solm := { contract := contract, locals := locals, immutables := imms })
    (slot := ⟨"pendingGuardian", []⟩) (er := ⟨"pendingGuardian", []⟩) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, bind, pure, EvalResult.bind])
    (show storageTypeAt? contract.storage ⟨"pendingGuardian", []⟩ = some
      (.struct "PendingAddress" [("value", .elem .address),
        ("validAt", .elem (.int (.uint ⟨64, by decide⟩))),
        ("padding", .elem (.int (.uint ⟨32, by decide⟩)))]) from rfl)
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hr,
    Bool.false_eq_true, ↓reduceIte, hr, bind, EvalResult.bind]
  change solidityClearStorage? _ evm ⟨"pendingGuardian", []⟩ (.struct "PendingAddress" _) = _
  rw [solidityClearStorage?, solidityClearFields?]
  rw [clearStorage_field ⟨⟨15⟩, 0, 20, by decide, none, .address⟩ rfl rfl]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?]
  rw [clearStorage_field
    ⟨⟨15⟩, 20, 8, by decide, none, .int (.uint ⟨64, by decide⟩)⟩ rfl rfl]
  simp only [bind, EvalResult.bind]
  rw [solidityClearFields?]
  rw [clearStorage_field
    ⟨⟨15⟩, 28, 4, by decide, none, .int (.uint ⟨32, by decide⟩)⟩ rfl rfl]
  simp only [bind, EvalResult.bind, solidityClearFields?]
  change EvalResult.ok (clearFieldState
    (clearFieldState (clearFieldState evm ⟨15⟩ 0 20) ⟨15⟩ 20 8) ⟨15⟩ 28 4) = _
  rw [clearFieldState_append, clearFieldState_append, clearFieldState_all]

end Benchmarks.Morpho.MetaMorphoV1_1
