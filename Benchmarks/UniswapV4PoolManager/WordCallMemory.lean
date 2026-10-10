import Benchmarks.UniswapV4PoolManager.MemorySlice
import Benchmarks.UniswapV4PoolManager.BytesObjectMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES singleWordCallMemory to an arbitrary static ABI word sequence and sparse writes.
def wordCallMemory (mem : ByteArray) (off : Nat) (selector : UInt256) (words : List UInt256) : ByteArray :=
  wordSequenceMemory (writeWord mem off selector) (off+4) words

theorem wordCallMemory_size (mem : ByteArray) (off : Nat) (selector : UInt256) (words : List UInt256) :
    (wordCallMemory mem off selector words).size =
      max (max mem.size (off+32)) (off+4+32*words.length) := by
  rw [wordCallMemory, wordSequenceMemory_size words (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_size]

theorem wordCallMemory_read (mem : ByteArray) (off : Nat) (selector : UInt256) (words : List UInt256) :
    (wordCallMemory mem off selector words).readWithPadding off (4+32*words.length) =
      selector.toByteArray.extract 0 4 ++ wordBytes words := by
  rw [readWithPadding_split _ _ _ _ (by rw [wordCallMemory_size]; omega), wordCallMemory,
    wordSequenceMemory_read_below_unbounded _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (le_refl _),
    wordSequenceMemory_read]
  have hsel := writeWord_sparse_read_window mem off 0 4 selector (by decide) (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add] using congrArg (fun bytes => bytes ++ wordBytes words) hsel

def wordCallObjectMemory (mem : ByteArray) (ptr : UInt256) (selector : UInt256) (words : List UInt256) : ByteArray :=
  writeWord (wordCallMemory mem (ptr.toNat+32) selector words) ptr.toNat (UInt256.ofNat (4+32*words.length))

theorem wordCallObjectMemory_view (mem : ByteArray) (ptr : UInt256) (selector : UInt256)
    (words : List UInt256) :
    BytesObjectView (wordCallObjectMemory mem ptr selector words) ptr
      (selector.toByteArray.extract 0 4 ++ wordBytes words) := by
  have hs : (selector.toByteArray.extract 0 4 ++ wordBytes words).size = 4+32*words.length := by
    rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, wordBytes_size]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, wordCallObjectMemory, writeWord_sparse_load_back]
  · rw [hs, wordCallObjectMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by rw [wordCallMemory_size]; omega) (.inr (le_refl _)), wordCallMemory_read]
  · rw [hs, wordCallObjectMemory, writeWord_sparse_size, wordCallMemory_size]; omega

theorem wordCallObjectMemory_size (mem : ByteArray) (ptr selector : UInt256) (words : List UInt256)
    (hw : 0 < words.length) :
    (wordCallObjectMemory mem ptr selector words).size = max mem.size (ptr.toNat+36+32*words.length) := by
  rw [wordCallObjectMemory, writeWord_sparse_size, wordCallMemory_size]; omega

theorem MemorySlice.wordCallObject {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (ptr selector : UInt256) (words : List UInt256)
    (hb : base+data.size ≤ ptr.toNat) :
    MemorySlice (wordCallObjectMemory mem ptr selector words) base data :=
  ((h.writeWord (ptr.toNat+32) selector (.inl (by omega))).wordSequence (ptr.toNat+36) words
    (by omega)).writeWord ptr.toNat _ (.inl hb)

end Benchmarks.UniswapV4PoolManager
