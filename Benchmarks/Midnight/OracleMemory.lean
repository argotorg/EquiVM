import Benchmarks.Midnight.OracleABI
import Benchmarks.Midnight.ByteCopyMemory

/-! The oracle's selector and fixed-size return buffer preserve the decoded market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def oracleCallMemory (mem : ByteArray) (root : UInt256) : ByteArray :=
  writeWord mem root.toNat oraclePriceSelectorWord

def oracleReplyMemory (mem : ByteArray) (root : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (oracleCallMemory mem root) root.toNat 32

def oraclePriceMemory (mem : ByteArray) (root : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (oracleReplyMemory mem root out) 64 (root + UInt256.ofNat 32)

theorem oracleCallMemory_read (mem : ByteArray) (root : UInt256) :
    (oracleCallMemory mem root).readWithPadding root.toNat 4 = oraclePriceCalldata := by
  have h := writeWord_sparse_read_window mem root.toNat 0 4 oraclePriceSelectorWord
    (by decide) (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add, oraclePriceSelectorWord_bytes] using h

theorem oracleReplyMemory_size (mem : ByteArray) (root : UInt256) {out : ByteArray}
    (h32 : 32 ≤ out.size) :
    (oracleReplyMemory mem root out).size = max mem.size (root.toNat + 32) := by
  rw [oracleReplyMemory, copySparse_size _ _ _ _ _ (by decide) h32,
    oracleCallMemory, writeWord_sparse_size]
  omega

theorem oracleReplyMemory_read (mem : ByteArray) (root : UInt256) {out : ByteArray}
    (h32 : 32 ≤ out.size) :
    (oracleReplyMemory mem root out).readWithPadding root.toNat 32 =
      (calldataWord out 0).toByteArray := by
  rw [calldataWord_bytes h32]
  have h := copySparse_read out (oracleCallMemory mem root) 0 root.toNat 32 0 32 h32
    (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add,
    readWithPadding_eq_extract_unbounded out 0 32 (by decide) h32] using h

theorem oracleReplyMemory_prefix (mem : ByteArray) (root : UInt256) {out : ByteArray}
    (h32 : 32 ≤ out.size) : MemoryPrefix mem (oracleReplyMemory mem root out) root.toNat := by
  refine (memoryPrefix_writeWord mem root.toNat root.toNat oraclePriceSelectorWord
    (Or.inl le_rfl)).trans ?_
  refine ⟨?_, fun off _ hlim hin ↦ ?_⟩
  · rw [oracleReplyMemory_size mem root h32, writeWord_sparse_size]
  · exact copySparse_read_before out _ 0 root.toNat 32 off 32 (by decide) h32
      (by decide) hin hlim

theorem oraclePriceMemory_properties (mem : ByteArray) (root : UInt256) {out : ByteArray}
    (h32 : 32 ≤ out.size) (hroot : 96 ≤ root.toNat) :
    (oraclePriceMemory mem root out).size = max mem.size (root.toNat + 32) ∧
    memLoad (UInt256.ofNat 64) (oraclePriceMemory mem root out) = root + UInt256.ofNat 32 ∧
    memLoad root (oraclePriceMemory mem root out) = calldataWord out 0 ∧
    MemoryPrefix mem (oraclePriceMemory mem root out) root.toNat := by
  have hs := oracleReplyMemory_size mem root h32
  refine ⟨?_, memLoad_writeWord _ ⟨64⟩ _, ?_, ?_⟩
  · rw [oraclePriceMemory, writeWord_sparse_size, hs]
    omega
  · rw [oraclePriceMemory, memLoad_writeWord_preserved _ _ _ _ (by rw [hs]; omega)
      (Or.inr hroot)]
    exact mloadWordValue_of_readWithPadding (by rw [hs]; omega)
      (oracleReplyMemory_read mem root h32)
  · exact (oracleReplyMemory_prefix mem root h32).trans
      (memoryPrefix_writeWord _ 64 root.toNat _ (Or.inr (by decide)))

end Benchmarks.Midnight
