import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! The uint64 timestamp field at byte offset twenty in a pending guardian record. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def setPendingTimeWord (old data : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 160 + data.toNat % 2 ^ 64 * 2 ^ 160 +
    old.toNat / 2 ^ 224 * 2 ^ 224)

theorem setPendingTimeWord_toNat (old data : UInt256) :
    (setPendingTimeWord old data).toNat =
      old.toNat % 2 ^ 160 + data.toNat % 2 ^ 64 * 2 ^ 160 +
        old.toNat / 2 ^ 224 * 2 ^ 224 := by
  apply UInt256.toNat_ofNat_of_lt
  have hw : old.toNat < 2 ^ 256 := old.val.isLt
  have hlo : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by decide)
  have hmid : data.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  change _ < 2 ^ 256
  omega

set_option maxRecDepth 2000 in
theorem pendingTimeShiftMask (data : UInt256) :
    (UInt256.land (UInt256.shiftLeft (UInt256.ofNat (2 ^ 64 - 1)) ⟨160⟩)
      (UInt256.shiftLeft data ⟨160⟩)).toNat = data.toNat % 2 ^ 64 * 2 ^ 160 := by
  rw [uland_toNat]
  rw [show (UInt256.shiftLeft (UInt256.ofNat (2 ^ 64 - 1)) ⟨160⟩).toNat =
    (2 ^ 64 - 1) <<< 160 by decide]
  have hs : (UInt256.shiftLeft data ⟨160⟩).toNat = (data.toNat <<< 160) % 2 ^ 256 := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide : ¬ (⟨160⟩ : UInt256).val ≥ 256)]
    unfold UInt256.toNat
    rw [Fin.shiftLeft_val]
    rfl
  rw [hs]
  change ((2 ^ 64 - 1) <<< 160) &&& ((data.toNat <<< 160) % 2 ^ 256) = _
  have hm : ((2 ^ 64 - 1) <<< 160) % 2 ^ 256 = (2 ^ 64 - 1) <<< 160 := by decide
  rw [← hm, ← Nat.and_mod_two_pow, ← Nat.shiftLeft_and_distrib, Nat.and_comm]
  change (Nat.land data.toNat (2 ^ 64 - 1) <<< 160) % 2 ^ 256 = _
  rw [nat_land_mask_eq_mod, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by
    have hmid := Nat.mod_lt data.toNat (by decide : 0 < 2 ^ 64)
    omega)

theorem setPendingTimeWord_bytecode (old data : UInt256) :
    UInt256.lor
      (UInt256.land (UInt256.shiftLeft (UInt256.ofNat (2 ^ 64 - 1)) ⟨160⟩)
        (UInt256.shiftLeft data ⟨160⟩))
      (UInt256.land (UInt256.lnot
        (UInt256.shiftLeft (UInt256.ofNat (2 ^ 64 - 1)) ⟨160⟩)) old) =
      setPendingTimeWord old data := by
  have hm : (UInt256.lnot
      (UInt256.shiftLeft (UInt256.ofNat (2 ^ 64 - 1)) ⟨160⟩)).toNat =
      (2 ^ 160 - 1) ||| (2 ^ 256 - 2 ^ 224) := by decide
  apply u256_inj
  rw [u256_lor_toNat_exact, pendingTimeShiftMask, u256_land_comm, uland_toNat, hm,
    Nat.and_or_distrib_left]
  change Nat.lor (data.toNat % 2 ^ 64 * 2 ^ 160)
    (Nat.lor (Nat.land old.toNat (2 ^ 160 - 1))
      (Nat.land old.toNat (2 ^ 256 - 2 ^ 224))) = _
  rw [nat_land_mask_eq_mod, natLandClearLow old.toNat 224 (by decide) old.val.isLt]
  rw [show Nat.lor (data.toNat % 2 ^ 64 * 2 ^ 160)
      (Nat.lor (old.toNat % 2 ^ 160) (old.toNat / 2 ^ 224 * 2 ^ 224)) =
      Nat.lor (Nat.lor (old.toNat % 2 ^ 160) (data.toNat % 2 ^ 64 * 2 ^ 160))
        (old.toNat / 2 ^ 224 * 2 ^ 224) by
      exact (Nat.or_left_comm _ _ _).trans (Nat.or_assoc _ _ _).symm,
    nat_lor_shift_add _ _ 160 (Nat.mod_lt _ (by decide)),
    nat_lor_shift_add _ _ 224 (by
      have hlo := Nat.mod_lt old.toNat (by decide : 0 < 2 ^ 160)
      have hmid := Nat.mod_lt data.toNat (by decide : 0 < 2 ^ 64)
      omega), setPendingTimeWord_toNat]

theorem storageLocStore_pendingTime (evm : EVM.State) (slot data : UInt256) :
    storageLocStore evm
      { slot := slot, offset := 20, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }
      (uint256Value data) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setPendingTimeWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) data)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20 ++
      (EVM.Word.toBytesLEWithSizeProof data).1.take 8 ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 28) = _
  rw [fromBytes'_append, fromBytes'_append, fromBytes'_take_wordLE,
    fromBytes'_take_wordLE, fromBytes'_drop_wordLE, setPendingTimeWord_toNat]
  simp only [List.length_append, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2,
    (EVM.Word.toBytesLEWithSizeProof data).2]
  change _ % 2 ^ 160 + 2 ^ 160 * (data.toNat % 2 ^ 64) + 2 ^ 224 * (_ / 2 ^ 224) = _
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
