import Benchmarks.Midnight.MemoryPrefix

/-! Arbitrary-length memory reads above an in-bounds word write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the read length need not fit in a machine integer.
theorem writeWord_read_above (mem : ByteArray) (off read len : Nat) (word : UInt256)
    (habove : off + 32 ≤ read) (hin : read + len ≤ mem.size) :
    (writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  by_cases hz : len = 0
  · subst len; simp only [byteArray_readWithPadding_zero]
  have hbsz : (mem.extract 0 off).size = off := by rw [ByteArray.size_extract]; omega
  have hsz32 : (word.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hcsz : (mem.extract (off + 32) mem.size).size = mem.size - (off + 32) := by
    rw [ByteArray.size_extract]; omega
  have habsz : (mem.extract 0 off ++ word.toByteArray.extract 0 32).size = off + 32 := by
    rw [ByteArray.size_append, hbsz, hsz32]
  unfold Reasoning.Theory.writeWord
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    readWithPadding_eq_extract_unbounded _ read len (by omega) (by
      rw [ByteArray.size_append, habsz, hcsz]; omega),
    readWithPadding_eq_extract_unbounded mem read len (by omega) hin]
  rw [extract_append_right_window (mem.extract 0 off ++ word.toByteArray.extract 0 32)
    (mem.extract (off + 32) mem.size) read (read + len) (by rw [habsz]; omega),
    habsz, extract_extract_BA]
  rw [show off + 32 + (read - (off + 32)) = read by omega,
    show min (off + 32 + (read + len - (off + 32))) mem.size = read + len by omega]

end Benchmarks.Midnight
