import Benchmarks.CompoundIII.Comet.ConstructorInputEncoding
import Benchmarks.CompoundIII.Comet.MemoryAllocate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem constructorAssetCount_toNat {n : Nat} (hsize : 22161 + 224 * n < UInt256.size) :
    (UInt256.ofNat n).toNat = n :=
  UInt256.toNat_ofNat_of_lt (by omega)

theorem constructorArgumentSize_toNat {n : Nat} (hsize : 22161 + 224 * n < UInt256.size) :
    (UInt256.ofNat (736 + 224 * n)).toNat = 736 + 224 * n :=
  UInt256.toNat_ofNat_of_lt (by omega)

theorem constructorAllocationEnd_toNat {n : Nat} (hsize : 22161 + 224 * n < UInt256.size) :
    (allocationEnd ⟨928⟩ (UInt256.ofNat (736 + 224 * n))).toNat = 1664 + 224 * n := by
  have hlen := constructorArgumentSize_toNat hsize
  have hadd : (UInt256.ofNat (736 + 224 * n) + (⟨31⟩ : UInt256)).toNat = 767 + 224 * n := by
    rw [uadd_toNat, hlen]
    change (736 + 224 * n + 31) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [allocationEnd, uadd_toNat, u256_land_comm, longDataCutoff_toNat, hadd]
  change (928 + (767 + 224 * n) / 32 * 32) % UInt256.size = _
  have hround : (767 + 224 * n) / 32 * 32 = 736 + 224 * n := by omega
  rw [hround, Nat.mod_eq_of_lt (by omega)]
  omega

theorem constructorAllocationEnd_eq {n : Nat} (hsize : 22161 + 224 * n < UInt256.size) :
    allocationEnd ⟨928⟩ (UInt256.ofNat (736 + 224 * n)) =
      UInt256.ofNat (1664 + 224 * n) := by
  apply u256_inj
  rw [constructorAllocationEnd_toNat hsize, UInt256.toNat_ofNat_of_lt (by omega)]

/-- The allocator's actual 64-bit guard remains a branch of the constructor proof. -/
theorem constructorAllocationGuard_zero {n : Nat}
    (hsize : 22161 + 224 * n < UInt256.size) (hsmall : 1664 + 224 * n < 2^64) :
    UInt256.lor
      (UInt256.lt (allocationEnd ⟨928⟩ (UInt256.ofNat (736 + 224 * n))) ⟨928⟩)
      (UInt256.gt (allocationEnd ⟨928⟩ (UInt256.ofNat (736 + 224 * n)))
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩)) = ⟨0⟩ := by
  have he := constructorAllocationEnd_toNat hsize
  rw [ult_zero (by rw [he]; change 928 ≤ _; omega), ugt_zero (by
    rw [he]; change _ ≤ 2^64 - 1; omega)]
  rfl

theorem constructorAllocationGuard_ne_zero {n : Nat}
    (hsize : 22161 + 224 * n < UInt256.size) (hlarge : 2^64 ≤ 1664 + 224 * n) :
    UInt256.lor
      (UInt256.lt (allocationEnd ⟨928⟩ (UInt256.ofNat (736 + 224 * n))) ⟨928⟩)
      (UInt256.gt (allocationEnd ⟨928⟩ (UInt256.ofNat (736 + 224 * n)))
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩ := by
  rw [ugt_one (by
    rw [constructorAllocationEnd_toNat hsize]; change 2^64 - 1 < _; omega)]
  rw [u256_lor_comm]
  exact u256_lor_one_ne_zero _

end Benchmarks.CompoundIII.Comet
