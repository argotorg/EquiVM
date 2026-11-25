import Benchmarks.Midnight.SafeTransferAfterCall

/-! Allocation growth paid for by a token call and its return-data copy. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def transferOutputWork (out : ByteArray) : Nat :=
  100 + 3 * ((out.size + 31) / 32) +
    if out.size ≤ 1024 then 0 else memoryCost ((out.size + 31) / 32)

theorem transferOutputWork_growth (out : ByteArray) {allocation : Nat}
    (ha : allocation ≤ 160) :
    4 * ((allocation + (if out.size = 0 then 0 else returnDataAllocation out.size)) / 32) ≤
      transferOutputWork out := by
  unfold transferOutputWork returnDataAllocation memoryCost
  split <;> split <;> omega

theorem safeTransferOutputPtr_toNat {ptr : UInt256} {out : ByteArray}
    (hfit : ptr.toNat + returnDataAllocation out.size < UInt256.size) :
    (safeTransferOutputPtr ptr out).toNat =
      ptr.toNat + if out.size = 0 then 0 else returnDataAllocation out.size := by
  unfold safeTransferOutputPtr
  split
  · omega
  · exact uadd_word_ofNat_toNat ptr _ hfit

theorem safeTransferOutputPtr_aligned {ptr : UInt256} {out : ByteArray}
    (hfit : ptr.toNat + returnDataAllocation out.size < UInt256.size)
    (halign : ptr.toNat % 32 = 0) : (safeTransferOutputPtr ptr out).toNat % 32 = 0 := by
  rw [safeTransferOutputPtr_toNat hfit]
  split
  · simpa only [Nat.add_zero] using halign
  · unfold returnDataAllocation
    omega

theorem safeTransferOutputPtr_covered {mem out : ByteArray} {ptr aw : UInt256}
    (hm : 96 ≤ mem.size) (hl : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + returnDataAllocation out.size < UInt256.size)
    (halign : ptr.toNat % 32 = 0) (hptr : ptr.toNat ≤ 32 * aw.toNat)
    (hc : MemoryCovered (safeTransferOutputMem mem out ptr) aw) :
    (safeTransferOutputPtr ptr out).toNat ≤ 32 * aw.toNat := by
  rw [safeTransferOutputPtr_toNat hfit]
  by_cases hz : out.size = 0
  · simpa only [if_pos hz, Nat.add_zero] using hptr
  · rw [if_neg hz]
    have hp := (returnDataMem_properties hm hl hz (by
      unfold returnDataAllocation at hfit
      omega)).1
    unfold MemoryCovered at hc
    simp only [safeTransferOutputMem, if_neg hz, hp] at hc
    unfold returnDataAllocation
    omega

end Benchmarks.Midnight
