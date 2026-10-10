import Benchmarks.Morpho.MetaMorphoV1_1.PendingGuardianMutation

/-! The two fields of the pending timelock record. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def setPendingUint192Word (old data : UInt256) : UInt256 :=
  UInt256.ofNat (data.toNat % 2 ^ 192 + old.toNat / 2 ^ 192 * 2 ^ 192)

def setPendingTimeHighWord (old data : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 192 + data.toNat % 2 ^ 64 * 2 ^ 192)

theorem setPendingUint192Word_toNat (old data : UInt256) :
    (setPendingUint192Word old data).toNat =
      data.toNat % 2 ^ 192 + old.toNat / 2 ^ 192 * 2 ^ 192 := by
  apply UInt256.toNat_ofNat_of_lt
  have hw : old.toNat < 2 ^ 256 := old.val.isLt
  have hd := Nat.mod_lt data.toNat (by decide : 0 < 2 ^ 192)
  change _ < 2 ^ 256
  omega

theorem setPendingTimeHighWord_toNat (old data : UInt256) :
    (setPendingTimeHighWord old data).toNat =
      old.toNat % 2 ^ 192 + data.toNat % 2 ^ 64 * 2 ^ 192 := by
  apply UInt256.toNat_ofNat_of_lt
  have hlo := Nat.mod_lt old.toNat (by decide : 0 < 2 ^ 192)
  have hhi := Nat.mod_lt data.toNat (by decide : 0 < 2 ^ 64)
  change _ < 2 ^ 256
  omega

theorem setPendingUint192Word_bytecode (old data : UInt256) :
    UInt256.lor (UInt256.land data (UInt256.ofNat (2 ^ 192 - 1)))
      (UInt256.land (UInt256.lnot (UInt256.ofNat (2 ^ 192 - 1))) old) =
      setPendingUint192Word old data := by
  apply u256_inj
  rw [u256_lor_toNat_exact, uland_toNat, u256_land_comm, uland_toNat]
  change Nat.lor (Nat.land data.toNat (2 ^ 192 - 1))
    (Nat.land old.toNat (2 ^ 256 - 2 ^ 192)) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat 192 (by decide) old.val.isLt,
    nat_lor_shift_add _ _ 192 (Nat.mod_lt _ (by decide)), setPendingUint192Word_toNat]

set_option maxRecDepth 2000 in
theorem pendingTimeHighShift (data : UInt256) :
    (UInt256.shiftLeft data ⟨192⟩).toNat = data.toNat % 2 ^ 64 * 2 ^ 192 := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨192⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftLeft_val]
  rw [show (⟨192⟩ : UInt256).val.val = 192 by decide]
  rw [Nat.shiftLeft_eq]
  conv_lhs => arg 2; change (2 : Nat) ^ 64 * 2 ^ 192
  exact Nat.mul_mod_mul_right _ _ _

theorem setPendingTimeHighWord_bytecode (old data : UInt256) :
    UInt256.lor
      (UInt256.land (UInt256.lnot (UInt256.ofNat (2 ^ 192 - 1)))
        (UInt256.shiftLeft data ⟨192⟩))
      (UInt256.land (UInt256.ofNat (2 ^ 192 - 1)) old) =
      setPendingTimeHighWord old data := by
  apply u256_inj
  rw [u256_lor_toNat_exact, u256_land_comm, uland_toNat,
    u256_land_comm (UInt256.ofNat (2 ^ 192 - 1)), uland_toNat]
  change Nat.lor (Nat.land (UInt256.shiftLeft data ⟨192⟩).toNat (2 ^ 256 - 2 ^ 192))
    (Nat.land old.toNat (2 ^ 192 - 1)) = _
  rw [natLandClearLow (UInt256.shiftLeft data ⟨192⟩).toNat 192 (by decide)
      (UInt256.shiftLeft data ⟨192⟩).val.isLt,
    pendingTimeHighShift, Nat.mul_div_cancel _ (by decide : 0 < 2 ^ 192),
    nat_land_mask_eq_mod, nat_lor_comm,
    nat_lor_shift_add _ _ 192 (Nat.mod_lt _ (by decide)), setPendingTimeHighWord_toNat]

theorem storageLocStore_pendingUint192 (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm
      { slot := slot, offset := 0, size := 24, hbound := by decide,
        type := .int (.uint ⟨192, by decide⟩) }
      (uint256Value data) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setPendingUint192Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof data).1.take 24 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 24) = _
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE,
    setPendingUint192Word_toNat]
  simp only [List.length_take, (EVM.Word.toBytesLEWithSizeProof data).2]
  change data.toNat % 2 ^ 192 + 2 ^ 192 * (_ / 2 ^ 192) = _
  omega

theorem storageLocStore_pendingTimeHigh (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm
      { slot := slot, offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }
      (uint256Value data) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setPendingTimeHighWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 24 ++
      (EVM.Word.toBytesLEWithSizeProof data).1.take 8 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 32) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setPendingTimeHighWord_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof data).2]
  change _ % 2 ^ 192 + 2 ^ 192 * (data.toNat % 2 ^ 64) + 2 ^ 256 * (_ / 2 ^ 256) = _
  have hw : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 2 ^ 256 :=
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
  rw [Nat.div_eq_of_lt hw]
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
