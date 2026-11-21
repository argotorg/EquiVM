import Benchmarks.Midnight.Storage

/-! Packed-word identities for Midnight's market and position fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem uint128Mask_computed :
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2^128 - 1) := by native_decide

-- LIBRARY CANDIDATE: word SHR is division by a power of two below the word width.
theorem shiftRight_toNat (word shift : UInt256) (hshift : shift.toNat < 256) :
    (UInt256.shiftRight word shift).toNat = word.toNat / 2^shift.toNat := by
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg]
  · change (word.val >>> shift.val).val = word.val.val / 2^shift.val.val
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
  · change ¬ shift.toNat ≥ 256
    omega

theorem shiftRight128_lt (word : UInt256) :
    (UInt256.shiftRight word (UInt256.ofNat 128)).toNat < EVM.twoPow 128 := by
  rw [shiftRight_toNat _ _ (by decide)]
  have h := word.val.isLt
  change word.toNat / 2^128 < 2^128
  apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
  exact h

theorem shiftRight_zero (word : UInt256) : UInt256.shiftRight word (UInt256.ofNat 0) = word := by
  apply u256_inj
  rw [shiftRight_toNat _ _ (by decide)]
  exact Nat.div_one word.toNat

theorem uint128HighWord (word : UInt256) :
    UInt256.land (UInt256.div word (UInt256.ofNat (256^16)))
      (UInt256.ofNat (256^16 - 1)) =
        UInt256.shiftRight word (UInt256.ofNat 128) := by
  have hdiv : UInt256.div word (UInt256.ofNat (256^16)) =
      UInt256.shiftRight word (UInt256.ofNat 128) := by
    apply u256_inj
    rw [udiv_toNat, shiftRight_toNat _ _ (by decide)]
    rfl
  rw [hdiv]
  exact u256LandMaskCleanOfToNat _ _ (by decide) (shiftRight128_lt word)

theorem storageLocLoad_uint128_high (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm {
      slot := slot, offset := 16, size := 16, hbound := by decide,
      type := .int (.uint ⟨128, by decide⟩) } =
      .int (Int.ofNat (UInt256.shiftRight
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat 128)).toNat) := by
  simpa only [show (16 : Fin 32).val = 16 from rfl,
    show (16 : Fin 33).val = 16 from rfl, uint128HighWord] using
    storageLocLoad_uint_offset evm slot 16 16 ⟨128, by decide⟩
      (hbound := by decide) (by decide) (by decide) (by decide)

-- LIBRARY CANDIDATE: translate byte-offset storage extraction to SHR.
theorem div_byteOffset_eq_shiftRight (word : UInt256) (offset : Fin 32) :
    UInt256.div word (UInt256.ofNat (256^offset.val)) =
      UInt256.shiftRight word (UInt256.ofNat (8 * offset.val)) := by
  have hoff : 8 * offset.val < 256 := by omega
  have hbits : 8 * offset.val < UInt256.size := lt_trans hoff (by decide)
  have hpow : 256^offset.val < UInt256.size := by
    change (2^8)^offset.val < 2^256
    rw [← Nat.pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hoff
  apply u256_inj
  rw [udiv_toNat, UInt256.toNat_ofNat_of_lt hpow,
    shiftRight_toNat _ _ (by rwa [UInt256.toNat_ofNat_of_lt hbits]),
    UInt256.toNat_ofNat_of_lt hbits]
  rw [show (256 : Nat) = 2^8 from rfl, ← Nat.pow_mul]

theorem storageLocLoad_uint32_offset14 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm {
      slot := slot, offset := 14, size := 4, hbound := by decide,
      type := .int (.uint ⟨32, by decide⟩) } =
      .int (Int.ofNat (UInt256.land (UInt256.shiftRight
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat 112)) (UInt256.ofNat (2^32 - 1))).toNat) := by
  rw [storageLocLoad_uint_offset evm slot 14 4 ⟨32, by decide⟩
    (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
  rfl

theorem storageLocLoad_uint8_offset18 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm {
      slot := slot, offset := 18, size := 1, hbound := by decide,
      type := .int (.uint ⟨8, by decide⟩) } =
      .int (Int.ofNat (UInt256.land (UInt256.shiftRight
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat 144)) (UInt256.ofNat (2^8 - 1))).toNat) := by
  rw [storageLocLoad_uint_offset evm slot 18 1 ⟨8, by decide⟩
    (by decide) (by decide) (by decide), div_byteOffset_eq_shiftRight]
  rfl

end Benchmarks.Midnight
