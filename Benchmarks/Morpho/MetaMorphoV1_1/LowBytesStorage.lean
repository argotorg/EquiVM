import Benchmarks.Morpho.MetaMorphoV1_1.PendingTimelockStorage

/-! Replacing a low byte field while retaining the high bytes of its storage slot. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: instantiate the generic mask-cleaning lemma with a low-bit mask.
theorem wordLowMask_eq_self (word : UInt256) (bits : Nat) (hbits : bits ≤ 256)
    (hword : word.toNat < 2 ^ bits) :
    UInt256.land word (UInt256.ofNat (2 ^ bits - 1)) = word := by
  have hp : 2 ^ bits ≤ UInt256.size := Nat.pow_le_pow_right (by decide) hbits
  have hm : 2 ^ bits - 1 < UInt256.size := by
    have : 0 < 2 ^ bits := by positivity
    omega
  exact u256LandMaskCleanOfToNat word _ (ulit_toNat' _ hm) hword

-- LIBRARY CANDIDATE: packed low-field writes, parameterized by the byte count.
def setLowBytesWord (old data : UInt256) (size : Nat) : UInt256 :=
  UInt256.ofNat (data.toNat % 256 ^ size + old.toNat / 256 ^ size * 256 ^ size)

theorem setLowBytesWord_toNat (old data : UInt256) (size : Nat) (hsize : size ≤ 32) :
    (setLowBytesWord old data size).toNat =
      data.toNat % 256 ^ size + old.toNat / 256 ^ size * 256 ^ size := by
  apply UInt256.toNat_ofNat_of_lt
  have hp : 0 < 256 ^ size := by positivity
  have hpow : 256 ^ size * 256 ^ (32 - size) = UInt256.size := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hsize]
    rfl
  have hdiv : old.toNat / 256 ^ size < 256 ^ (32 - size) := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [Nat.mul_comm, hpow]
    exact old.val.isLt
  have hm := Nat.mod_lt data.toNat hp
  nlinarith

-- GENERALIZES the fixed-width packed integer stores to all low byte widths.
theorem storageLocStore_uint_lowBytes (evm : State) (slot data : UInt256)
    (size : Fin 33) (width : BitWidth) :
    storageLocStore evm
      { slot := slot, offset := 0, size := size, hbound := by have := size.isLt; omega,
        type := .int (.uint width) }
      (.int (Int.ofNat data.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setLowBytesWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          data size.val)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  simp only [Fin.val_zero, Nat.zero_add, List.take_zero, List.nil_append]
  change fromBytes'
    ((EVM.Word.toBytesLEWithSizeProof data).1.take size.val ++
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop size.val) = _
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE,
    setLowBytesWord_toNat _ _ _ (by have := size.isLt; omega)]
  simp only [List.length_take, (EVM.Word.toBytesLEWithSizeProof data).2,
    Nat.min_eq_left (by have := size.isLt; omega : size.val ≤ 32)]
  rw [Nat.pow_mul]
  simp only [show (2 : Nat) ^ 8 = 256 by decide, Nat.mul_comm]

theorem setLowBytesWord_bytecode (old data : UInt256) (size : Nat) (hsize : size ≤ 32) :
    UInt256.lor
      (UInt256.land (UInt256.lnot (UInt256.ofNat (2 ^ (8 * size) - 1))) old)
      (UInt256.land data (UInt256.ofNat (2 ^ (8 * size) - 1))) =
      setLowBytesWord old data size := by
  apply u256_inj
  rw [u256_lor_toNat_exact, u256_land_comm, uland_toNat, uland_toNat]
  have hb : 8 * size ≤ 256 := by omega
  have hp : 2 ^ (8 * size) ≤ UInt256.size := by
    exact Nat.pow_le_pow_right (by decide) hb
  have hm : 2 ^ (8 * size) - 1 < UInt256.size := by
    have : 0 < 2 ^ (8 * size) := by positivity
    omega
  rw [ulit_toNat' _ hm]
  change Nat.lor
    (Nat.land old.toNat (UInt256.lnot (UInt256.ofNat (2 ^ (8 * size) - 1))).toNat)
    (Nat.land data.toNat (2 ^ (8 * size) - 1)) = _
  rw [lnot_toNat_gen]
  rw [ulit_toNat' _ hm]
  have hmask : 2 ^ 256 - 1 - (2 ^ (8 * size) - 1) =
      2 ^ 256 - 2 ^ (8 * size) := by
    have : 0 < 2 ^ (8 * size) := by positivity
    change 2 ^ 256 - 1 - (2 ^ (8 * size) - 1) = _
    omega
  rw [hmask, natLandClearLow old.toNat (8 * size) hb old.val.isLt,
    nat_land_mask_eq_mod, nat_lor_comm,
    nat_lor_shift_add _ _ (8 * size) (Nat.mod_lt _ (by positivity)),
    setLowBytesWord_toNat old data size hsize, Nat.pow_mul]

end Benchmarks.Morpho.MetaMorphoV1_1
