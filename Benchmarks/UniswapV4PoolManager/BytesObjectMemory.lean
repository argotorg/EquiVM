import Benchmarks.UniswapV4PoolManager.SparseBytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the observable part of a Solidity memory bytes object.
structure BytesObjectView (mem : ByteArray) (ptr : UInt256) (data : ByteArray) : Prop where
  lengthWord : memLoad ptr mem = UInt256.ofNat data.size
  payload : mem.readWithPadding (ptr.toNat+32) data.size = data
  inBounds : ptr.toNat+32+data.size ≤ mem.size

theorem BytesObjectView.writeWord_after {mem data : ByteArray} {ptr : UInt256}
    (h : BytesObjectView mem ptr data) (off : Nat) (word : UInt256)
    (hoff : ptr.toNat+32+data.size ≤ off) :
    BytesObjectView (writeWord mem off word) ptr data := by
  refine ⟨?_, ?_, ?_⟩
  · rw [writeWord_sparse_load_before _ _ _ _ (by have := h.inBounds; omega) (by omega)]
    exact h.lengthWord
  · rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _ h.inBounds (.inl hoff)]
    exact h.payload
  · rw [writeWord_sparse_size]
    have := h.inBounds
    omega

-- LIBRARY CANDIDATE: a word stored before a bytes object preserves its header and payload.
theorem BytesObjectView.writeWord_before {mem data : ByteArray} {ptr : UInt256}
    (h : BytesObjectView mem ptr data) (off : Nat) (word : UInt256)
    (hoff : off+32 ≤ ptr.toNat) :
    BytesObjectView (writeWord mem off word) ptr data := by
  refine ⟨?_, ?_, ?_⟩
  · have hi : ptr.toNat+32 ≤ mem.size := by have := h.inBounds; omega
    rw [memLoad, if_neg (by rw [writeWord_sparse_size]; omega),
      writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hi (.inr hoff)]
    simpa only [memLoad, if_neg (by omega : ¬ptr.toNat ≥ mem.size)] using h.lengthWord
  · rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _ h.inBounds (.inr (by omega))]
    exact h.payload
  · rw [writeWord_sparse_size]; have := h.inBounds; omega

-- LIBRARY CANDIDATE: allocate a length word, copy a bytes slice, and zero its padding.
def bytesObjectMemory (mem : ByteArray) (srcOff : Nat) (ptr len : UInt256) : ByteArray :=
  copyZeroMemory (writeWord mem ptr.toNat len) (writeWord mem ptr.toNat len)
    srcOff (ptr.toNat+32) len.toNat

theorem bytesObjectMemory_size (mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (hsrc : srcOff+len.toNat ≤ mem.size) :
    (bytesObjectMemory mem srcOff ptr len).size = max mem.size (ptr.toNat+len.toNat+64) := by
  rw [bytesObjectMemory, copyZeroMemory_size _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_size]
  omega

theorem bytesObjectMemory_length (mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (hsrc : srcOff+len.toNat ≤ mem.size) :
    memLoad ptr (bytesObjectMemory mem srcOff ptr len) = len := by
  rw [bytesObjectMemory, copyZeroMemory_load_before _ _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (by rw [writeWord_sparse_size]; omega) (by omega)]
  apply mloadWordValue_of_readWithPadding
  · rw [writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ _ _

theorem bytesObjectMemory_payload (mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (hsrc : srcOff+len.toNat ≤ mem.size) (hbefore : srcOff+len.toNat ≤ ptr.toNat) :
    (bytesObjectMemory mem srcOff ptr len).readWithPadding (ptr.toNat+32) len.toNat =
      mem.readWithPadding srcOff len.toNat := by
  rw [bytesObjectMemory, copyZeroMemory_read_payload _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hsrc (.inl hbefore)]

theorem bytesObjectMemory_view (mem data : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (hsrc : srcOff+len.toNat ≤ mem.size) (hbefore : srcOff+len.toNat ≤ ptr.toNat)
    (hsize : data.size = len.toNat) (hread : mem.readWithPadding srcOff len.toNat = data) :
    BytesObjectView (bytesObjectMemory mem srcOff ptr len) ptr data := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bytesObjectMemory_length _ _ _ _ hsrc, hsize, u256_ofNat_toNat]
  · rw [hsize, bytesObjectMemory_payload _ _ _ _ hsrc hbefore, hread]
  · rw [hsize, bytesObjectMemory_size _ _ _ _ hsrc]; omega

theorem bytesObjectMemory_load_before (mem : ByteArray) (srcOff : Nat) (ptr len read : UInt256)
    (hsrc : srcOff+len.toNat ≤ mem.size) (hin : read.toNat+32 ≤ mem.size)
    (hbefore : read.toNat+32 ≤ ptr.toNat) :
    memLoad read (bytesObjectMemory mem srcOff ptr len) = memLoad read mem := by
  rw [bytesObjectMemory, copyZeroMemory_load_before _ _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_load_before _ _ _ _ hin hbefore]

end Benchmarks.UniswapV4PoolManager
