import Benchmarks.Midnight.PackedUint128

/-! Writes to the upper uint128 field of a packed storage word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def uint128HighLoc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 16, size := 16, hbound := by decide, type := .int packedUInt128Int }

theorem shiftLeft128_toNat (value : UInt256) :
    (UInt256.shiftLeft value (UInt256.ofNat 128)).toNat = value.toNat % 2^128 * 2^128 := by
  unfold UInt256.shiftLeft
  rw [if_neg (show ¬ (UInt256.ofNat 128).val ≥ 256 from by decide)]
  change (value.toNat <<< 128) % UInt256.size = _
  rw [show UInt256.size = 2^128 * 2^128 by norm_num [UInt256.size]]
  rw [Nat.shiftLeft_eq, Nat.mul_mod_mul_right]

theorem shiftLeft128_highMask (value : UInt256) :
    UInt256.land (UInt256.shiftLeft value (UInt256.ofNat 128)) (UInt256.lnot uint128Mask) =
      UInt256.shiftLeft value (UInt256.ofNat 128) := by
  apply u256_inj
  rw [uland_toNat]
  change Nat.land _ (2^256 - 2^128) = _
  rw [natLandClearLow (UInt256.shiftLeft value (UInt256.ofNat 128)).toNat 128 (by decide)
    (UInt256.shiftLeft value (UInt256.ofNat 128)).val.isLt,
    shiftLeft128_toNat]
  simp

def setUint128HighWord (old value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old uint128Mask) (UInt256.shiftLeft value (UInt256.ofNat 128))

theorem setUint128HighWord_toNat (old value : UInt256) :
    (setUint128HighWord old value).toNat = old.toNat % 2^128 + value.toNat % 2^128 * 2^128 := by
  rw [setUint128HighWord, u256_lor_toNat_exact, uland_toNat, shiftLeft128_toNat]
  change (Nat.land old.toNat (2^128 - 1) ||| (value.toNat % 2^128 * 2^128)) = _
  rw [nat_land_mask_eq_mod]
  exact nat_lor_shift_add _ _ 128 (Nat.mod_lt _ (by decide))

theorem storageLocStore_uint128_high_word (evm : EVM.State) (slot value : UInt256) :
    storageLocStore evm (uint128HighLoc slot) (.int (Int.ofNat value.toNat)) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint128HighWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  apply storageLocStore_packed_of_toNat evm _ _ value _
    (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
  rw [setUint128HighWord_toNat]
  dsimp only [uint128HighLoc]
  change _ = _ % 256^16 + 256^16 * (value.toNat % 256^16) +
    256^(16 + 16) * (_ / 256^(16 + 16))
  have hb := (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt
  change (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat < 256^(16+16) at hb
  rw [Nat.div_eq_of_lt hb]
  simp only [show (256 : Nat)^16 = 2^128 by decide, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.mul_comm]

end Benchmarks.Midnight
