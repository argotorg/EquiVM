import Benchmarks.UniswapV3.Pool.StorageWordUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def packedFieldMask (offset width : Nat) : UInt256 :=
  UInt256.ofNat ((2 ^ offset - 1) ||| (2 ^ 256 - 2 ^ (offset + width)))

def packedFieldValue (value : UInt256) (offset width : Nat) : UInt256 :=
  UInt256.mul (UInt256.land value (UInt256.ofNat (2 ^ width - 1))) (UInt256.ofNat (2 ^ offset))

def packedFieldUpdate (old value : UInt256) (offset width : Nat) : UInt256 :=
  UInt256.lor (UInt256.land old (packedFieldMask offset width)) (packedFieldValue value offset width)

theorem packedFieldMask_toNat (offset width : Nat) (hoff : offset < 256) :
    (packedFieldMask offset width).toNat = (2 ^ offset - 1) ||| (2 ^ 256 - 2 ^ (offset + width)) := by
  apply UInt256.toNat_ofNat_of_lt
  change (2 ^ offset - 1) ||| (2 ^ 256 - 2 ^ (offset + width)) < 2 ^ 256
  apply Nat.or_lt_two_pow
  · exact lt_trans (Nat.sub_lt (by positivity) (by decide))
      (Nat.pow_lt_pow_right (by decide) hoff)
  · exact Nat.sub_lt (by positivity) (by positivity)

theorem packedFieldValue_toNat (value : UInt256) (offset width : Nat)
    (hoff : offset < 256) (hb : offset + width ≤ 256) :
    (packedFieldValue value offset width).toNat = (value.toNat % 2 ^ width) * 2 ^ offset := by
  have hmask : (UInt256.ofNat (2 ^ width - 1)).toNat = 2 ^ width - 1 := by
    apply UInt256.toNat_ofNat_of_lt
    exact lt_of_lt_of_le (Nat.sub_lt (by positivity) (by decide))
      (Nat.pow_le_pow_right (by decide) (by omega : width ≤ 256))
  have hland : (UInt256.land value (UInt256.ofNat (2 ^ width - 1))).toNat =
      value.toNat % 2 ^ width := by
    rw [uland_toNat, hmask]
    exact nat_land_mask_eq_mod _ _
  have hshift : (UInt256.ofNat (2 ^ offset)).toNat = 2 ^ offset :=
    UInt256.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hoff)
  have hf : (value.toNat % 2 ^ width) * 2 ^ offset < UInt256.size := by
    calc
      _ < 2 ^ width * 2 ^ offset := Nat.mul_lt_mul_of_pos_right
        (Nat.mod_lt _ (by positivity)) (by positivity)
      _ = 2 ^ (offset + width) := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hb
  unfold packedFieldValue
  change (UInt256.land value (UInt256.ofNat (2 ^ width - 1)) *
    UInt256.ofNat (2 ^ offset)).toNat = _
  rw [umul_toNat _ _ (by rw [hland, hshift]; exact hf), hland, hshift]

-- LIBRARY CANDIDATE: a uniform word model for any byte-aligned scalar storage field.
theorem storageLocStore_packedValue (evm : EVM.State) (loc : StorageLoc)
    (value : Value) (word : UInt256) (hv : valueToWord value = some word)
    (hbit : loc.bitOffset = none) :
    storageLocStore evm loc value = some (modifyStorageWord evm loc.slot
      (fun old ↦ packedFieldUpdate old word (8 * loc.offset.val) (8 * loc.size.val))) := by
  apply storageLocStore_masked evm loc value word _ _ hv hbit
  · rw [packedFieldMask_toNat _ _ (by have h := loc.offset.isLt; omega), Nat.mul_add]
  · exact packedFieldValue_toNat word _ _ (by have h := loc.offset.isLt; omega)
      (by have h := loc.hbound; omega)

end Benchmarks.UniswapV3.Pool
