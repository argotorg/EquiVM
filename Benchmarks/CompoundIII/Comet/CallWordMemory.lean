import Reasoning.HeapMemory

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: a four-byte call selector followed by one ABI word.
def callWordMemory (mem : ByteArray) (ptr selector arg : UInt256) : ByteArray :=
  writeWord (writeWord mem ptr.toNat selector) (ptr + UInt256.ofNat 4).toNat arg

theorem callWordMemory_size {mem : ByteArray} {ptr selector arg : UInt256}
    (hb : ptr.toNat + 36 < UInt256.size) :
    (callWordMemory mem ptr selector arg).size = max mem.size (ptr.toNat + 36) := by
  rw [callWordMemory, writeWord_sparse_size, writeWord_sparse_size,
    uadd_word_ofNat_toNat ptr 4 (by omega)]
  omega

theorem callWordMemory_payload {mem : ByteArray} {ptr selector arg : UInt256}
    (hb : ptr.toNat + 36 < UInt256.size) :
    (callWordMemory mem ptr selector arg).readWithPadding ptr.toNat 36 =
      selector.toByteArray.extract 0 4 ++ arg.toByteArray := by
  have ha := uadd_word_ofNat_toNat ptr 4 (by omega)
  have hs := callWordMemory_size (mem := mem) (selector := selector) (arg := arg) hb
  rw [show 36 = 4 + 32 by rfl,
    byteArray_readWithPadding_split _ _ _ _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by rw [hs]; omega)]
  have hword : (callWordMemory mem ptr selector arg).readWithPadding (ptr.toNat + 4) 32 =
      arg.toByteArray := by
    rw [callWordMemory, ha, writeWord_sparse_read_back]
  have hsel : (callWordMemory mem ptr selector arg).readWithPadding ptr.toNat 4 =
      selector.toByteArray.extract 0 4 := by
    rw [callWordMemory, ha, writeWord_read_preserved_len _ _ _ _ _
      (by rw [writeWord_sparse_size]; exact lt_of_le_of_lt (by omega) (lt_usize 0 (by decide)))
      (Or.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩) (by decide) (by decide)]
    simpa only [Nat.add_zero] using writeWord_sparse_read_window mem ptr.toNat 0 4 selector
      (by decide) (by decide) (by decide)
  rw [hsel, hword]

end Benchmarks.CompoundIII.Comet
