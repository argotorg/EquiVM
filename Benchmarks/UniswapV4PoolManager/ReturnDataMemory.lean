import Benchmarks.UniswapV4PoolManager.BytesObjectMemory
import Benchmarks.UniswapV4PoolManager.MemorySlice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.solcReturnDataMem_size to a sparse length-word store.
theorem returnDataMemory_size (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hmem : 96 ≤ mem.size) (hfit : ptr.toNat+32 < UInt256.size) :
    (solcReturnDataMem mem ptr out).size = max mem.size (ptr.toNat+32+out.size) := by
  have h32 : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hfit
  change (out.write 0 (writeWord (solcReturnDataPtrMem mem ptr out) ptr.toNat
    (UInt256.ofNat out.size)) (ptr+⟨32⟩).toNat out.size).size = _
  rw [h32, byteArray_write_all_size _ _ _ (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_size, solcReturnDataPtrMem_size _ _ hmem]
  omega

-- GENERALIZES Reasoning.Theory.solcReturnDataMem_read_size to a sparse allocation.
theorem returnDataMemory_length (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hfit : ptr.toNat+32 < UInt256.size) :
    memLoad ptr (solcReturnDataMem mem ptr out) = UInt256.ofNat out.size := by
  have h32 : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hfit
  let base := writeWord (solcReturnDataPtrMem mem ptr out) ptr.toNat (UInt256.ofNat out.size)
  have hb : ptr.toNat+32 ≤ base.size := by dsimp only [base]; rw [writeWord_sparse_size]; omega
  change memLoad ptr (out.write 0 base (ptr+⟨32⟩).toNat out.size) = _
  rw [h32]
  apply mloadWordValue_of_readWithPadding
  · rw [byteArray_write_all_size _ _ _ hb]; omega
  · rw [copyWindow_read_preserved_any _ _ _ _ _ _ _ (by omega) hb hb (.inl (le_refl _))]
    exact writeWord_sparse_read_back _ _ _

-- LIBRARY CANDIDATE: the returned bytes form a Solidity bytes object after the copy.
theorem returnDataMemory_view (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hmem : 96 ≤ mem.size) (hfit : ptr.toNat+32 < UInt256.size) :
    BytesObjectView (solcReturnDataMem mem ptr out) ptr out := by
  refine ⟨returnDataMemory_length _ _ _ hfit, ?_, ?_⟩
  · have h32 : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hfit
    change (out.write 0 (writeWord (solcReturnDataPtrMem mem ptr out) ptr.toNat
      (UInt256.ofNat out.size)) (ptr+⟨32⟩).toNat out.size).readWithPadding (ptr.toNat+32) out.size = out
    rw [h32]
    have hc := copyWindow_read_any out (writeWord (solcReturnDataPtrMem mem ptr out) ptr.toNat
      (UInt256.ofNat out.size)) 0 (ptr.toNat+32) out.size 0 out.size (by omega)
      (by rw [writeWord_sparse_size]; omega) (by omega)
    simpa only [Nat.add_zero, Nat.zero_add, readWithPadding_eq_extract_any out 0 out.size (by omega),
      ByteArray.extract_zero_size] using hc
  · rw [returnDataMemory_size _ _ _ hmem hfit]; omega

-- LIBRARY CANDIDATE: disjoint data between the free-pointer slot and the allocation is preserved.
theorem returnDataMemory_read_before (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (read count : Nat) (hin : read+count ≤ mem.size) (hlo : 96 ≤ read)
    (hbefore : read+count ≤ ptr.toNat) (hfit : ptr.toNat+32 < UInt256.size) :
    (solcReturnDataMem mem ptr out).readWithPadding read count = mem.readWithPadding read count := by
  have h32 : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hfit
  change (out.write 0 (writeWord (writeWord mem 64 _) ptr.toNat _) (ptr+⟨32⟩).toNat
    out.size).readWithPadding read count = _
  rw [h32, copyWindow_read_preserved_any _ _ _ _ _ _ _ (by omega)
      (by rw [writeWord_sparse_size]; omega)
      (by rw [writeWord_sparse_size, writeWord_sparse_size]; omega) (.inl (by omega)),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (.inl hbefore),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inr hlo)]

theorem returnDataMemory_free (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hlo : 96 ≤ ptr.toNat) (hfit : ptr.toNat+32 < UInt256.size) :
    memLoad ⟨64⟩ (solcReturnDataMem mem ptr out) =
      ptr+UInt256.land (UInt256.ofNat out.size+⟨63⟩) (UInt256.lnot ⟨31⟩) := by
  have h32 : (ptr+⟨32⟩).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat ptr 32 hfit
  change memLoad ⟨64⟩ (out.write 0 (writeWord (writeWord mem 64 _) ptr.toNat _)
    (ptr+⟨32⟩).toNat out.size) = _
  rw [h32]
  apply mloadWordValue_of_readWithPadding
  · rw [byteArray_write_all_size _ _ _ (by rw [writeWord_sparse_size]; omega),
      writeWord_sparse_size, writeWord_sparse_size]; change 64 < _; omega
  · rw [copyWindow_read_preserved_any _ _ _ _ _ _ _ (by omega)
        (by rw [writeWord_sparse_size]; omega)
        (by rw [writeWord_sparse_size, writeWord_sparse_size]; change 64+32 ≤ _; omega)
        (.inl (by change 64+32 ≤ _; omega)),
      writeWord_sparse_read_preserved_unbounded _ _ _ _ _
        (by rw [writeWord_sparse_size]; change 64+32 ≤ _; omega) (.inl hlo)]
    exact writeWord_sparse_read_back _ _ _

-- LIBRARY CANDIDATE: preserve any disjoint memory slice across return-data allocation.
theorem MemorySlice.returnData {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (ptr : UInt256) (out : ByteArray)
    (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat) (hf : ptr.toNat+32 < UInt256.size) :
    MemorySlice (solcReturnDataMem mem ptr out) base data := by
  refine ⟨?_, ?_⟩
  · rw [returnDataMemory_read_before _ _ _ _ _ h.inBounds hlo hb hf]
    exact h.bytes
  · rw [returnDataMemory_size _ _ _ (by have := h.inBounds; omega) hf]
    have := h.inBounds
    omega

end Benchmarks.UniswapV4PoolManager
