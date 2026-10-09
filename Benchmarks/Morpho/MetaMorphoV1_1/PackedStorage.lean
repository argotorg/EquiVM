import Benchmarks.Morpho.MetaMorphoV1_1.Storage

/-! Reads of packed pending-update structs. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: express a bounded EVM shift as division by a power of two.
theorem wordShiftRight_eq_div (w : UInt256) (bits : Nat) (hbits : bits < 256) :
    UInt256.shiftRight w (UInt256.ofNat bits) = UInt256.div w (UInt256.ofNat (2 ^ bits)) := by
  apply u256_inj
  rw [wordShiftRight_toNat w bits hbits, udiv_toNat,
    ulit_toNat' _ (Nat.pow_lt_pow_right (by decide) hbits)]

-- GENERALIZES Reasoning.Storage.storageLocLoad_uint_offset with the EVM SHR representation.
theorem storageLocLoad_uint_shift (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (width : ABI.BitWidth)
    {hbound : offset.val + size.val - 1 < 32}
    (hwidth : width.val = 8 * size.val)
    (hoff : 8 * offset.val < 256) (hsize : 8 * size.val ≤ 256) :
    storageLocLoad evm
      { slot := slot, offset := offset, size := size, hbound := hbound,
        type := .int (.uint width) } =
      .int (Int.ofNat (UInt256.land
        (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (8 * offset.val))) (UInt256.ofNat (2 ^ (8 * size.val) - 1))).toNat) := by
  rw [storageLocLoad_uint_offset evm slot offset size width hwidth hoff hsize]
  rw [wordShiftRight_eq_div _ _ hoff]
  congr 4 <;> rw [Nat.pow_mul]

-- LIBRARY CANDIDATE: the remaining high bits after a bounded logical right shift.
theorem wordShiftRight_lt (w : UInt256) (bits : Nat) (hbits : bits < 256) :
    (UInt256.shiftRight w (UInt256.ofNat bits)).toNat < 2 ^ (256 - bits) := by
  rw [wordShiftRight_toNat w bits hbits]
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hbits)]
  exact w.val.isLt

-- LIBRARY CANDIDATE: an unsigned field extending to the high end of a storage slot.
theorem storageLocLoad_uint_high (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (width : ABI.BitWidth)
    {hbound : offset.val + size.val - 1 < 32}
    (hwidth : width.val = 8 * size.val) (htop : offset.val + size.val = 32) :
    storageLocLoad evm
      { slot := slot, offset := offset, size := size, hbound := hbound,
        type := .int (.uint width) } =
      .int (Int.ofNat (UInt256.shiftRight
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (8 * offset.val))).toNat) := by
  have hoff : 8 * offset.val < 256 := by have := offset.isLt; omega
  have hbits : 8 * size.val ≤ 256 := by omega
  rw [storageLocLoad_uint_shift evm slot offset size width hwidth hoff hbits]
  have hcanon := wordShiftRight_lt
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (8 * offset.val) hoff
  rw [show 256 - 8 * offset.val = 8 * size.val by omega] at hcanon
  have hpow : 2 ^ (8 * size.val) ≤ UInt256.size := Nat.pow_le_pow_right (by decide) hbits
  have hpos : 0 < 2 ^ (8 * size.val) := by positivity
  rw [u256LandMaskCleanOfToNat _ _ (ulit_toNat' _ (by omega)) hcanon]

theorem evalStorage_pendingTimelockValue (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "pendingTimelock" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"pendingTimelock", [.field "value"]⟩) =
      .ok (.int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨17⟩)
        (UInt256.ofNat (2 ^ 192 - 1))).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"pendingTimelock", [.field "value"]⟩)
    (t := .int (.uint ⟨192, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"pendingTimelock", [.field "value"]⟩ =
      some (.elem (.int (.uint ⟨192, by decide⟩))) from by decide +kernel)
    rfl rfl (storageLocLoad_uint_offset0 evm ⟨17⟩ 24 ⟨192, by decide⟩ rfl (by decide))

theorem evalStorage_pendingTimelockValidAt (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "pendingTimelock" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"pendingTimelock", [.field "validAt"]⟩) =
      .ok (.int (Int.ofNat (UInt256.shiftRight
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨17⟩) ⟨192⟩).toNat)) := by
  apply evalExpr_storage_scalar_value (er := ⟨"pendingTimelock", [.field "validAt"]⟩)
    (t := .int (.uint ⟨64, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"pendingTimelock", [.field "validAt"]⟩ =
      some (.elem (.int (.uint ⟨64, by decide⟩))) from by decide +kernel) rfl rfl
  exact storageLocLoad_uint_high evm ⟨17⟩ 24 8 ⟨64, by decide⟩ rfl rfl

theorem evalStorage_pendingGuardianValue (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "pendingGuardian" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"pendingGuardian", [.field "value"]⟩) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"pendingGuardian", [.field "value"]⟩)
    (t := .address) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"pendingGuardian", [.field "value"]⟩ =
      some (.elem .address) from by decide +kernel)
    rfl rfl (storageLocLoad_address_offset0 evm ⟨15⟩)

theorem evalStorage_pendingGuardianValidAt (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "pendingGuardian" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"pendingGuardian", [.field "validAt"]⟩) =
      .ok (.int (Int.ofNat (UInt256.land
        (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨15⟩) ⟨160⟩)
        (UInt256.ofNat (2 ^ 64 - 1))).toNat)) := by
  exact evalExpr_storage_scalar_value (er := ⟨"pendingGuardian", [.field "validAt"]⟩)
    (t := .int (.uint ⟨64, by decide⟩)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      EvalResult.bind, pure, bind])
    (show storageTypeAt? contract.storage ⟨"pendingGuardian", [.field "validAt"]⟩ =
      some (.elem (.int (.uint ⟨64, by decide⟩))) from by decide +kernel)
    rfl rfl (storageLocLoad_uint_shift evm ⟨15⟩ 20 8 ⟨64, by decide⟩ rfl (by decide) (by decide))

end Benchmarks.Morpho.MetaMorphoV1_1
