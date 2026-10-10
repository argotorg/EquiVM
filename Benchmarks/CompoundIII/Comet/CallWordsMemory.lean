import Benchmarks.CompoundIII.Comet.CallWordMemory

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: extend any bounded memory payload by one ABI word.
theorem memoryPayload_append_word {mem : ByteArray} {ptr len : Nat} {w : UInt256}
    (hpos : 0 < len) (hsize : ptr + len ≤ mem.size)
    (hbound : ptr + len + 32 < 2^64) :
    (writeWord mem (ptr + len) w).readWithPadding ptr (len + 32) =
      mem.readWithPadding ptr len ++ w.toByteArray := by
  rw [byteArray_readWithPadding_split _ _ _ _ (by omega) (by decide)
    (by omega) (by omega) (by omega) (by rw [writeWord_sparse_size]; omega)]
  rw [writeWord_sparse_read_back]
  rw [writeWord_read_preserved_len _ _ _ _ _
    (by rw [Nat.sub_eq_zero_of_le hsize]; exact lt_usize 0 (by decide))
    (Or.inl ⟨by omega, hsize⟩) (by omega) (by omega)]

def callTwoWordMemory (mem : ByteArray) (ptr selector first second : UInt256) : ByteArray :=
  writeWord (callWordMemory mem ptr selector first) (ptr + UInt256.ofNat 36).toNat second

theorem callTwoWordMemory_size {mem : ByteArray} {ptr selector first second : UInt256}
    (hb : ptr.toNat + 68 < UInt256.size) :
    (callTwoWordMemory mem ptr selector first second).size = max mem.size (ptr.toNat + 68) := by
  rw [callTwoWordMemory, writeWord_sparse_size, callWordMemory_size (by omega),
    uadd_word_ofNat_toNat ptr 36 (by omega)]
  omega

theorem callTwoWordMemory_payload {mem : ByteArray} {ptr selector first second : UInt256}
    (hb : ptr.toNat + 68 < 2^64) :
    (callTwoWordMemory mem ptr selector first second).readWithPadding ptr.toNat 68 =
      (selector.toByteArray.extract 0 4 ++ first.toByteArray) ++ second.toByteArray := by
  have hu : ptr.toNat + 68 < UInt256.size := by change _ < 2^256; omega
  rw [callTwoWordMemory, uadd_word_ofNat_toNat ptr 36 (by omega)]
  rw [memoryPayload_append_word (len := 36) (by decide)
    (by rw [callWordMemory_size (by omega)]; omega) (by omega)]
  rw [callWordMemory_payload (by omega)]

end Benchmarks.CompoundIII.Comet
