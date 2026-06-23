import Examples.OpenZeppelinBench.AccessControl.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl benchmark storage helpers

Helpers for the `_roles` nested mapping layout and full-slot/low-byte storage load-store facts.
-/

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
theorem fromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fromBytes', Nat.ofDigits, ih]

theorem accessControlWordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

theorem accessControlKeyValueToWord_fixedBytes32 (w : UInt256) :
    keyValueToWord (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) = w := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [keyValueToWord, bytes32Width, hlen]
  apply u256_inj
  have hfrom : fromBytesBigEndian (EVM.Word.toBytesBE w) = w.toNat := by
    have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray w)
    simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
      h.trans (fromByteArrayBigEndian_toByteArray w)
  rw [EVM.Word.ofNat, hfrom]
  exact Nat.mod_eq_of_lt w.val.isLt

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem accessControlNat_land_mask_eq_mod (n k : Nat) :
    Nat.land n (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& (2 ^ k - 1)).testBit i = (n % 2 ^ k).testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · rw [decide_eq_true hi]
    simp
  · rw [decide_eq_false hi]
    simp

theorem accessControlStorageLocLoad_bytes32_raw (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 32, hbound := by decide,
          type := .bytes ⟨31, by decide⟩ }
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  simp only [show 32 - (31 + 1) = 0 by norm_num, List.drop_zero]
  congr
  rw [htake]
  exact fromBytes'_toBytesLEWithSizeProof _

theorem accessControlStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot)
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [bytes32Loc] using accessControlStorageLocLoad_bytes32_raw evm slot

-- LIBRARY CANDIDATE: `Reasoning.Memory`.
theorem accessControlFromBytes'_take1_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 1) =
      (UInt256.land w ⟨255⟩).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 1 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [fromBytes'_eq_ofDigits (bs.take 1), List.map_take]
  rw [← htake, hfull]
  show w.toNat % 256 ^ 1 = (Nat.land w.toNat (⟨255⟩ : UInt256).toNat) % UInt256.size
  rw [show 256 ^ 1 = 2 ^ 8 by norm_num]
  rw [show (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 by decide]
  rw [accessControlNat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ 8 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 8)) (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

theorem accessControlStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (boolLoc slot)
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  unfold storageLocLoad boolLoc
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [accessControlFromBytes'_take1_wordLE]
  rfl

theorem accessControlStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool false := by
  rw [accessControlStorageLocLoad_bool_offset0 evm slot]
  simp [wordToElem, hzero]

theorem accessControlStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (boolLoc slot) = .bool true := by
  rw [accessControlStorageLocLoad_bool_offset0 evm slot]
  have hbeq :
      ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

end OpenZeppelinBench.AccessControl
