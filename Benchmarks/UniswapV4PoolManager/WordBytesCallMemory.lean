import Benchmarks.UniswapV4PoolManager.WordCallMemory
import Benchmarks.UniswapV4PoolManager.BytesValueMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a static ABI head followed by a calldata-backed bytes tail.
def wordBytesCallMemory (src mem : ByteArray) (srcOff off : Nat) (selector : UInt256)
    (words : List UInt256) (len : UInt256) : ByteArray :=
  bytesValueMemory src (wordCallMemory mem off selector words) srcOff (off+4+32*words.length) len

theorem wordBytesCallMemory_size (src mem : ByteArray) (srcOff off : Nat) (selector : UInt256)
    (words : List UInt256) (len : UInt256) (hs : srcOff+len.toNat ≤ src.size) :
    (wordBytesCallMemory src mem srcOff off selector words len).size =
      max mem.size (off+68+32*words.length+len.toNat) := by
  rw [wordBytesCallMemory, bytesValueMemory_size _ _ _ _ _ hs, wordCallMemory_size]
  omega

theorem wordBytesCallMemory_read (src mem : ByteArray) (srcOff off : Nat) (selector : UInt256)
    (words : List UInt256) (len : UInt256) (hs : srcOff+len.toNat ≤ src.size) :
    (wordBytesCallMemory src mem srcOff off selector words len).readWithPadding off
      (36+32*words.length+paddedSize len.toNat) =
      selector.toByteArray.extract 0 4 ++ wordBytes words ++
        bytesValueEncoding (src.extract srcOff (srcOff+len.toNat)) := by
  have hp := paddedSize_le_add31 len.toNat
  rw [show 36+32*words.length+paddedSize len.toNat =
      (4+32*words.length)+(32+paddedSize len.toNat) by omega,
    readWithPadding_split _ _ _ _ (by rw [wordBytesCallMemory_size _ _ _ _ _ _ _ hs]; omega)]
  change (bytesValueMemory _ _ _ _ _).readWithPadding _ _ ++
    (bytesValueMemory _ _ _ _ _).readWithPadding _ _ = _
  rw [bytesValueMemory_read_before _ _ _ _ _ _ _ hs
      (by rw [wordCallMemory_size]; omega) (by omega),
    show off+(4+32*words.length) = off+4+32*words.length by omega,
    bytesValueMemory_read _ _ _ _ _ hs, wordCallMemory_read]

theorem wordBytesCallMemory_read_before (src mem : ByteArray) (srcOff off : Nat) (selector : UInt256)
    (words : List UInt256) (len : UInt256) (read count : Nat) (hs : srcOff+len.toNat ≤ src.size)
    (hin : read+count ≤ mem.size) (hb : read+count ≤ off) :
    (wordBytesCallMemory src mem srcOff off selector words len).readWithPadding read count =
      mem.readWithPadding read count := by
  rw [wordBytesCallMemory, bytesValueMemory_read_before _ _ _ _ _ _ _ hs
    (by rw [wordCallMemory_size]; omega) (by omega), wordCallMemory,
    wordSequenceMemory_read_below_unbounded _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inl hb)]

def wordBytesCallObjectMemory (src mem : ByteArray) (srcOff : Nat) (ptr selector : UInt256)
    (words : List UInt256) (len : UInt256) : ByteArray :=
  writeWord (wordBytesCallMemory src mem srcOff (ptr.toNat+32) selector words len) ptr.toNat
    (UInt256.ofNat (36+32*words.length+paddedSize len.toNat))

theorem wordBytesCallObjectMemory_view (src mem : ByteArray) (srcOff : Nat) (ptr selector : UInt256)
    (words : List UInt256) (len : UInt256) (hs : srcOff+len.toNat ≤ src.size) :
    BytesObjectView (wordBytesCallObjectMemory src mem srcOff ptr selector words len) ptr
      (selector.toByteArray.extract 0 4 ++ wordBytes words ++
        bytesValueEncoding (src.extract srcOff (srcOff+len.toNat))) := by
  have hp := paddedSize_le_add31 len.toNat
  have hl := nat_le_paddedSize len.toNat
  have hz : (src.extract srcOff (srcOff+len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  have hsize : (selector.toByteArray.extract 0 4 ++ wordBytes words ++
      bytesValueEncoding (src.extract srcOff (srcOff+len.toNat))).size =
      36+32*words.length+paddedSize len.toNat := by
    simp only [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, wordBytes_size,
      bytesValueEncoding, ByteArray_zeroes_size, hz]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hsize, wordBytesCallObjectMemory, writeWord_sparse_load_back]
  · rw [hsize, wordBytesCallObjectMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by rw [wordBytesCallMemory_size _ _ _ _ _ _ _ hs]; omega) (.inr (le_refl _)),
      wordBytesCallMemory_read _ _ _ _ _ _ _ hs]
  · rw [hsize, wordBytesCallObjectMemory, writeWord_sparse_size, wordBytesCallMemory_size _ _ _ _ _ _ _ hs]
    omega

theorem wordBytesCallObjectMemory_size (src mem : ByteArray) (srcOff : Nat) (ptr selector : UInt256)
    (words : List UInt256) (len : UInt256) (hs : srcOff+len.toNat ≤ src.size) :
    (wordBytesCallObjectMemory src mem srcOff ptr selector words len).size =
      max mem.size (ptr.toNat+100+32*words.length+len.toNat) := by
  rw [wordBytesCallObjectMemory, writeWord_sparse_size, wordBytesCallMemory_size _ _ _ _ _ _ _ hs]
  omega

theorem MemorySlice.wordBytesCallObject {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (src : ByteArray) (srcOff : Nat) (ptr selector : UInt256)
    (words : List UInt256) (len : UInt256) (hs : srcOff+len.toNat ≤ src.size)
    (hb : base+data.size ≤ ptr.toNat) :
    MemorySlice (wordBytesCallObjectMemory src mem srcOff ptr selector words len) base data := by
  have hm : MemorySlice (wordBytesCallMemory src mem srcOff (ptr.toNat+32) selector words len) base data := by
    refine ⟨?_, ?_⟩
    · rw [wordBytesCallMemory_read_before _ _ _ _ _ _ _ _ _ hs h.inBounds (by omega)]
      exact h.bytes
    · rw [wordBytesCallMemory_size _ _ _ _ _ _ _ hs]
      have := h.inBounds
      omega
  exact hm.writeWord ptr.toNat _ (.inl hb)

end Benchmarks.UniswapV4PoolManager
