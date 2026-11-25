import Benchmarks.Midnight.PackedStore

/-! A uint128 write preserves the upper half of its storage word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def packedUInt128Int : IntType := .uint ⟨128, by decide⟩

abbrev uint128Mask : UInt256 := UInt256.ofNat (2 ^ 128 - 1)

def uint128LowLoc (slot : UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 16, hbound := by decide, type := .int packedUInt128Int }

def setUint128LowWord (old value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot uint128Mask)) (UInt256.land value uint128Mask)

theorem setUint128LowWord_toNat (old value : UInt256) :
    (setUint128LowWord old value).toNat =
      value.toNat % 2 ^ 128 + old.toNat / 2 ^ 128 * 2 ^ 128 := by
  have hv : (UInt256.land value uint128Mask).toNat = value.toNat % 2 ^ 128 := by
    rw [uland_toNat]
    exact nat_land_mask_eq_mod _ 128
  have h := packedMaskedWord_toNat old (UInt256.lnot uint128Mask)
    (UInt256.land value uint128Mask) 0 128 (value.toNat % 2 ^ 128) (by decide)
    (by decide) (by simpa only [Nat.pow_zero, Nat.mul_one] using hv)
    (Nat.mod_lt _ (by decide))
  simpa only [Nat.pow_zero, Nat.mod_one, Nat.mul_one, zero_add] using h

-- GENERALIZES Reasoning.Theory.storageLocStore_uint48_offset0_word to 128-bit fields.
theorem storageLocStore_uint128_low_word (evm : EVM.State) (slot value : UInt256) :
    storageLocStore evm (uint128LowLoc slot) (.int (Int.ofNat value.toNat)) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint128LowWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  apply storageLocStore_packed_of_toNat evm _ _ value _
    (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
  rw [setUint128LowWord_toNat]
  change _ = (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 256 ^ 0 +
    256 ^ 0 * (value.toNat % 256 ^ 16) +
    256 ^ (0 + 16) * ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 256 ^ (0 + 16))
  simp only [Nat.pow_zero, Nat.mod_one, Nat.one_mul, zero_add,
    show (256 : Nat) ^ 16 = 2 ^ 128 by decide, Nat.mul_comm]

theorem uint128Mask_clean {value : UInt256} (hvalue : value.toNat < 2 ^ 128) :
    UInt256.land value uint128Mask = value :=
  u256LandMaskCleanOfToNat value _ (by decide) hvalue

end Benchmarks.Midnight
