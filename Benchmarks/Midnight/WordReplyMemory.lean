import Benchmarks.Midnight.ByteCopyMemory
import Benchmarks.Midnight.CalldataArrayWords

/-! A CALL reply copied into an already covered, one-word output buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def wordReplyMemory (mem out : ByteArray) (root : UInt256) : ByteArray :=
  out.write 0 mem root.toNat (min 32 out.size)

theorem wordReplyMemory_eq (mem out : ByteArray) (root : UInt256)
    (hout : out.size < UInt256.size) :
    out.write 0 mem root.toNat (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat =
      wordReplyMemory mem out root := by
  have hn : (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
    change (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size
    by_cases h : 32 ≤ out.size
    · rw [u256_min32_ofNat_toNat_of_ge32 out.size h hout, Nat.min_eq_left h]
    · rw [u256_min32_ofNat_toNat_of_lt32 out.size (by omega), Nat.min_eq_right (by omega)]
  rw [hn]
  rfl

theorem wordReplyMemory_size (mem out : ByteArray) (root : UInt256)
    (hm : root.toNat + 32 ≤ mem.size) : (wordReplyMemory mem out root).size = mem.size := by
  by_cases hz : min 32 out.size = 0
  · simp only [wordReplyMemory, hz, ByteArray.write, if_true]
  · rw [wordReplyMemory, copySparse_size _ _ _ _ _ hz (by omega)]
    omega

theorem wordReplyMemory_load_before (mem out : ByteArray) (root read : UInt256)
    (hm : root.toNat + 32 ≤ mem.size) (hl : read.toNat + 32 ≤ root.toNat) :
    memLoad read (wordReplyMemory mem out root) = memLoad read mem := by
  by_cases hz : min 32 out.size = 0
  · simp only [wordReplyMemory, hz, ByteArray.write, if_true]
  · unfold memLoad
    rw [wordReplyMemory_size _ _ _ hm, if_neg (by omega), if_neg (by omega)]
    exact congrArg (fun bytes ↦ UInt256.ofNat (fromByteArrayBigEndian bytes))
      (copySparse_read_before out mem 0 root.toNat (min 32 out.size) read.toNat 32 hz
        (by omega) (by decide) (by omega) hl)

theorem wordReplyMemory_load (mem out : ByteArray) (root : UInt256)
    (hm : root.toNat + 32 ≤ mem.size) (h32 : 32 ≤ out.size) :
    memLoad root (wordReplyMemory mem out root) = calldataWord out 0 := by
  apply mloadWordValue_of_readWithPadding (by rw [wordReplyMemory_size _ _ _ hm]; omega)
  rw [wordReplyMemory, Nat.min_eq_left h32, calldataWord_bytes h32]
  have hr := copySparse_read out mem 0 root.toNat 32 0 32 (by omega) (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add, readWithPadding_eq_extract_unbounded out 0 32
    (by decide) h32] using hr

end Benchmarks.Midnight
