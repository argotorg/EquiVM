import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Reasoning.HeapMemory

/-! Memory contents of the singleton arrays constructed for Morpho's `extSloads` calls. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: copying beyond the source clears only existing destination bytes.
theorem writeOutsideSource_size (src mem : ByteArray) (source dest len : Nat)
    (hsource : src.size ≤ source) :
    (src.write source mem dest len).size = mem.size := by
  by_cases hlen : len = 0
  · simp only [hlen, byteArray_write_len_zero]
  · simp only [ByteArray.write, hlen, ↓reduceIte, ge_iff_le, hsource]
    change (ByteArray.copySlice _ _ _ _ _).data.size = mem.data.size
    simp only [ByteArray.data_copySlice, Array.size_append, Array.size_extract,
      Nat.sub_zero, ← ByteArray.size_data]
    omega

-- LIBRARY CANDIDATE: source-exhausted copying preserves words below its destination.
theorem writeOutsideSource_read (src mem : ByteArray) (source dest len read : Nat)
    (hsource : src.size ≤ source) (hin : read + 32 ≤ mem.size)
    (hbelow : read + 32 ≤ dest) :
    (src.write source mem dest len).readWithPadding read 32 = mem.readWithPadding read 32 := by
  by_cases hlen : len = 0
  · simp only [hlen, byteArray_write_len_zero]
  rw [readWithPadding_eq_extract _ _ (by rw [writeOutsideSource_size _ _ _ _ _ hsource]; omega),
    readWithPadding_eq_extract _ _ hin]
  simp only [ByteArray.write, hlen, ↓reduceIte, ge_iff_le, hsource]
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_copySlice]
  rw [Array.extract_append_of_stop_le_size_left (by
      simp only [Array.size_append, Array.size_extract, Nat.sub_zero]
      change read + 32 ≤ min (min dest mem.size) mem.size + _
      omega),
    Array.extract_append_of_stop_le_size_left (by
      simp only [Array.size_extract, Nat.sub_zero]
      change read + 32 ≤ min (min dest mem.size) mem.size
      omega), Array.extract_extract]
  congr 1 <;> omega

def morphoArrayInitMem (mem calldata : ByteArray) (ptr : UInt256) : ByteArray :=
  calldata.write calldata.size (writeWord (writeWord mem 64 (ptr + ⟨64⟩)) ptr.toNat ⟨1⟩)
    (ptr + ⟨32⟩).toNat 32

def morphoArrayMem (mem calldata : ByteArray) (ptr value : UInt256) : ByteArray :=
  writeWord (morphoArrayInitMem mem calldata ptr) (ptr + ⟨32⟩).toNat value

theorem morphoArrayInitMem_size (mem calldata : ByteArray) (ptr : UInt256) :
    (morphoArrayInitMem mem calldata ptr).size = max (max mem.size 96) (ptr.toNat + 32) := by
  rw [morphoArrayInitMem, writeOutsideSource_size _ _ _ _ _ (le_refl _),
    writeWord_sparse_size, writeWord_sparse_size]

theorem morphoArrayInitMem_readLength (mem calldata : ByteArray) (ptr : UInt256)
    (hfit : ptr.toNat + 32 < UInt256.size) :
    (morphoArrayInitMem mem calldata ptr).readWithPadding ptr.toNat 32 =
      (⟨1⟩ : UInt256).toByteArray := by
  have hptr : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  rw [morphoArrayInitMem, writeOutsideSource_read _ _ _ _ _ _ (le_refl _)
    (by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _)
    (by rw [hptr])]
  exact writeWord_sparse_read_back _ _ _

theorem morphoArrayInitMem_length (mem calldata : ByteArray) (ptr : UInt256)
    (hfit : ptr.toNat + 32 < UInt256.size) :
    memLoad ptr (morphoArrayInitMem mem calldata ptr) = ⟨1⟩ := by
  apply loadedWord_of_read
  · rw [morphoArrayInitMem_size]
    exact Nat.le_max_right _ _
  · exact morphoArrayInitMem_readLength mem calldata ptr hfit

theorem morphoArrayMem_size (mem calldata : ByteArray) (ptr value : UInt256)
    (hfit : ptr.toNat + 32 < UInt256.size) :
    (morphoArrayMem mem calldata ptr value).size =
      max (max mem.size 96) (ptr.toNat + 64) := by
  have hptr : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  rw [morphoArrayMem, writeWord_sparse_size, morphoArrayInitMem_size, hptr]
  omega

theorem morphoArrayMem_value (mem calldata : ByteArray) (ptr value : UInt256) :
    (morphoArrayMem mem calldata ptr value).readWithPadding (ptr + ⟨32⟩).toNat 32 =
      value.toByteArray :=
  writeWord_sparse_read_back _ _ _

theorem morphoArrayMem_length (mem calldata : ByteArray) (ptr value : UInt256)
    (hfit : ptr.toNat + 32 < UInt256.size) :
    (morphoArrayMem mem calldata ptr value).readWithPadding ptr.toNat 32 =
      (⟨1⟩ : UInt256).toByteArray := by
  have hptr : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  rw [morphoArrayMem, writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨by rw [hptr], by rw [morphoArrayInitMem_size]; exact Nat.le_max_right _ _⟩)]
  exact morphoArrayInitMem_readLength mem calldata ptr hfit

theorem morphoArrayMem_free (mem calldata : ByteArray) (ptr value : UInt256)
    (hlower : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 32 < UInt256.size) :
    (morphoArrayMem mem calldata ptr value).readWithPadding 64 32 =
      (ptr + ⟨64⟩).toByteArray := by
  have hptr : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  rw [morphoArrayMem, writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨by rw [hptr]; omega, by rw [morphoArrayInitMem_size]; omega⟩)]
  rw [morphoArrayInitMem, writeOutsideSource_read _ _ _ _ _ _ (le_refl _)
    (by rw [writeWord_sparse_size, writeWord_sparse_size]; omega) (by rw [hptr]; omega)]
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨hlower, by rw [writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem morphoArrayMem_prefix (mem calldata : ByteArray) (ptr value : UInt256)
    (hfit : ptr.toNat + 32 < UInt256.size) :
    MemoryPrefix mem (morphoArrayMem mem calldata ptr value) ptr.toNat := by
  have hptr : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  refine ⟨by rw [morphoArrayMem_size _ _ _ _ hfit]; omega, ?_⟩
  intro read hlo hhi hin
  rw [morphoArrayMem, writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨by rw [hptr]; omega, by rw [morphoArrayInitMem_size]; omega⟩)]
  rw [morphoArrayInitMem, writeOutsideSource_read _ _ _ _ _ _ (le_refl _)
    (by rw [writeWord_sparse_size, writeWord_sparse_size]; omega) (by rw [hptr]; omega)]
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl
    ⟨hhi, by rw [writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨hlo, hin⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
