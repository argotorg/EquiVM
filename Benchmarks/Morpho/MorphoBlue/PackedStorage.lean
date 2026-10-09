import Benchmarks.Morpho.MorphoBlue.Common

/-! Shared facts for storage packed into uint128 halves. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MorphoBlue

def uint128Mask : UInt256 := UInt256.ofNat 340282366920938463463374607431768211455

def halfWord (high : Bool) (w : UInt256) : UInt256 :=
  if high then UInt256.shiftRight w (UInt256.ofNat 128) else UInt256.land w uint128Mask

-- LIBRARY CANDIDATE: bounds for the low or high 128-bit half of a word.
theorem halfWord_bound (high : Bool) (w : UInt256) : (halfWord high w).toNat < 2 ^ 128 := by
  cases high
  · exact u256LandMaskToNatLtOfToNat w uint128Mask (by decide)
  · change (UInt256.shiftRight w ⟨128⟩).toNat < 2 ^ 128
    rw [rpowShiftRight128_toNat]
    apply (Nat.div_lt_iff_lt_mul (by norm_num)).mpr
    exact w.val.isLt

def uint128HalfLoc (slot : UInt256) (high : Bool) : StorageLoc :=
  { slot := slot, offset := if high then 16 else 0, size := 16,
    hbound := by cases high <;> decide, type := .int (.uint ⟨128, by decide⟩) }

-- LIBRARY CANDIDATE: packed uint128 storage reads in the bytecode's SHR/AND form.
theorem storageLocLoad_uint128Half (evm : EVM.State) (slot : UInt256) (high : Bool) :
    storageLocLoad evm (uint128HalfLoc slot high) =
      .int (Int.ofNat (halfWord high
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat) := by
  cases high
  · exact storageLocLoad_uint_offset0 evm slot ⟨16, by decide⟩ ⟨128, by decide⟩
      (by decide) (by decide)
  · have h := storageLocLoad_uint_offset (hbound := by decide) evm slot ⟨16, by decide⟩ ⟨16, by decide⟩
      ⟨128, by decide⟩ (by decide) (by decide) (by decide)
    have hdiv (w : UInt256) : UInt256.div w (UInt256.ofNat (256 ^ 16)) = halfWord true w := by
      apply u256_inj
      change (UInt256.div w (UInt256.ofNat (256 ^ 16))).toNat = (UInt256.shiftRight w ⟨128⟩).toNat
      rw [udiv_toNat, rpowShiftRight128_toNat]
      rfl
    have hmask : UInt256.ofNat (256 ^ 16 - 1) = uint128Mask := by native_decide
    rw [hdiv, hmask, u256LandMaskCleanOfToNat _ uint128Mask (by decide) (halfWord_bound true _)] at h
    exact h

def setUint128LowWord (old value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint128Mask)) value

-- LIBRARY CANDIDATE: a packed unsigned 128-bit store preserves the upper half.
theorem storageLocStore_uint128Low (evm : EVM.State) (slot value : UInt256)
    (hc : value.toNat < 2 ^ 128) :
    storageLocStore evm (uint128HalfLoc slot false) (.int (Int.ofNat value.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint128LowWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  have hhigh (old : UInt256) : (UInt256.land old (UInt256.lnot uint128Mask)).toNat =
      old.toNat / 2 ^ 128 * 2 ^ 128 := by
    change (UInt256.land old (UInt256.ofNat (2 ^ 256 - 2 ^ 128))).toNat = _
    rw [u256_land_comm]
    exact u256_land_high_mask_toNat old 128 (by decide)
  unfold storageLocStore storageLocWriteWord uint128HalfLoc
  simp only [Bool.false_eq_true, ↓reduceIte, valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof value).1.take 16 ++
    (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 16) = _
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  simp only [setUint128LowWord, u256_lor_toNat_exact, hhigh, List.length_take,
    (EVM.Word.toBytesLEWithSizeProof value).2]
  rw [show 256 ^ 16 = (2 : Nat) ^ 128 from rfl, Nat.mod_eq_of_lt hc]
  change value.toNat + 2 ^ 128 * _ = Nat.lor (_ * 2 ^ 128) value.toNat
  rw [nat_lor_comm, nat_lor_shift_add value.toNat _ 128 hc, Nat.mul_comm]

end Benchmarks.Morpho.MorphoBlue
