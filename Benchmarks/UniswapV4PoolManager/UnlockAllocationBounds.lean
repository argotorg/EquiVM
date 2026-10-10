import Benchmarks.UniswapV4PoolManager.UnlockReturnTail
import Benchmarks.UniswapV4PoolManager.BytesWordOverlap

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem unlockDecodedEnd_toNat {out : ByteArray} (hout : out.size < 2^138)
    (hb : BytesReturnBounds out) :
    (unlockDecodedEnd out).toNat = 192+paddedSize out.size+paddedSize (unlockReturnLength out).toNat := by
  have ho : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (lt_trans hout (by decide))
  have hl : (unlockReturnLength out).toNat ≤ 2^64-1 := hb.2.2.2.2.1
  have hp : (unlockRawEnd out).toNat = 160+paddedSize out.size := by
    rw [allocationEnd_toNat _ _ (by rw [ho]; change 160+out.size+31 < 2^256; omega), ho]
    rfl
  have hpad := paddedSize_le_add31 out.size
  rw [unlockDecodedEnd, bytesAllocationEnd_toNat _ _ (by rw [hp]; change _ < 2^256; omega), hp]
  omega

/-- Only one raw-reply word range remains after the larger-reply gas argument. -/
theorem unlockSecondAllocation_range {out : ByteArray} (hout : out.size < 2^138)
    (hb : BytesReturnBounds out)
    (hbad : ¬AllocationBounds (unlockRawEnd out) (bytesAllocationSize (unlockReturnLength out))) :
    2^63-63 ≤ out.size ∨
      (2^63-95 ≤ out.size ∧ out.size ≤ 2^63-64 ∧
        2^63-159 ≤ (unlockReturnLength out).toNat ∧
        (unlockReturnLength out).toNat ≤ 2^63-128 ∧
        32 ≤ (calldataWord out 0).toNat ∧ (calldataWord out 0).toNat ≤ 63) := by
  by_cases hlarge : 2^63-63 ≤ out.size
  · exact .inl hlarge
  have he := unlockDecodedEnd_toNat hout hb
  have ho : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (lt_trans hout (by decide))
  have hp : (unlockRawEnd out).toNat = 160+paddedSize out.size := by
    rw [allocationEnd_toNat _ _ (by rw [ho]; change 160+out.size+31 < 2^256; omega), ho]
    rfl
  have hfull : 2^64 ≤ 192+paddedSize out.size+paddedSize (unlockReturnLength out).toNat := by
    by_contra hn
    apply hbad
    change (unlockRawEnd out).toNat ≤ (unlockDecodedEnd out).toNat ∧
      (unlockDecodedEnd out).toNat ≤ 2^64-1
    rw [he, hp]
    omega
  have hlo : 2^63-159 ≤ (unlockReturnLength out).toNat := by
    unfold paddedSize at hfull
    omega
  have hoff := bytesReturn_large_offset hb (by change 2^59 ≤ (unlockReturnLength out).toNat; omega)
  have hsize := hb.2.2.2.2.2
  change (calldataWord out 0).toNat+32+(unlockReturnLength out).toNat ≤ out.size at hsize
  exact .inr ⟨by omega, by omega, hlo, by omega, hoff, by omega⟩

end Benchmarks.UniswapV4PoolManager
