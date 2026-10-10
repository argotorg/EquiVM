import Benchmarks.Morpho.MetaMorphoV1_1.MemoryArrayData
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayAllocationSource
import Benchmarks.EAS.Attester.WordArrayMemory

/-! Sparse memory after creating a zero-filled one-word array. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

-- GENERALIZES Reasoning.Memory.zeroes32_extract_zeroes to arbitrary zero-filled windows.
theorem zeroes_extract_window (n off len : Nat) (hfit : off + len ≤ n) :
    (ByteArray.zeroes n).extract off (off + len) = ByteArray.zeroes len := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [byteArray_zeroes_toList, byteArray_zeroes_toList]
  rw [List.extract_eq_take_drop, List.drop_replicate, List.take_replicate]
  congr 1
  omega

-- GENERALIZES Reasoning.Memory.writeWord_read_gap32 to a window anywhere in a sparse gap.
theorem writeWord_read_zero_gap (mem : ByteArray) (off read : Nat) (word : UInt256)
    (hlo : mem.size ≤ read) (hhi : read + 32 ≤ off) :
    (writeWord mem off word).readWithPadding read 32 = (⟨0⟩ : UInt256).toByteArray := by
  rw [writeWord_sparse_eq mem off word (by omega)]
  rw [readWithPadding_eq_extract _ _ (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega), extract_append_right_window _ _ _ _ hlo]
  rw [show read + 32 - mem.size = read - mem.size + 32 by omega,
    zeroes_extract_window _ _ _ (by omega)]
  exact zero_toByteArray_eq_zeroes32.symm

-- LIBRARY CANDIDATE: an exhausted-source copy above the current memory does not extend it.
theorem writeOutsideSource_eq_of_dest (src mem : ByteArray) (source dest len : Nat)
    (hsource : src.size ≤ source) (hdest : mem.size ≤ dest) :
    src.write source mem dest len = mem := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_write_len_zero]
  simp only [ByteArray.write, hz, ↓reduceIte, ge_iff_le, hsource]
  apply ByteArray.ext
  simp only [ByteArray.data_copySlice, Nat.sub_zero]
  simp only [Nat.min_eq_right hdest, Nat.sub_eq_zero_of_le hdest, Nat.min_zero,
    Nat.zero_add, zeroes_zero rfl]
  change mem.data.extract 0 mem.data.size ++ #[] ++ mem.data.extract mem.data.size = _
  simp

def wordArrayInitMemory (mem : ByteArray) (ptr : UInt256) (n : Nat) : ByteArray :=
  writeWord (writeWord mem 64 (UInt256.ofNat (ptr.toNat + 32 + 32 * n)))
    ptr.toNat (UInt256.ofNat n)

theorem wordArrayInitMemory_eq_header (mem : ByteArray) (ptr : UInt256) (n : Nat) :
    wordArrayInitMemory mem ptr n =
      Benchmarks.EAS.Attester.wordArrayHeaderMemory mem ptr.toNat n := by
  unfold wordArrayInitMemory Benchmarks.EAS.Attester.wordArrayHeaderMemory
  rw [show ptr.toNat + 32 + 32 * n = ptr.toNat + 32 * (n + 1) by omega]

theorem wordArrayInitMemory_size (mem : ByteArray) (ptr : UInt256) (n : Nat)
    (hmem : mem.size ≤ ptr.toNat) (hptr : 96 ≤ ptr.toNat) :
    (wordArrayInitMemory mem ptr n).size = ptr.toNat + 32 := by
  rw [wordArrayInitMemory_eq_header,
    Benchmarks.EAS.Attester.wordArrayHeaderMemory_size _ _ _ hptr]
  omega

theorem wordArrayInitMemory_prefix (mem : ByteArray) (ptr : UInt256) (n : Nat) :
    MemoryPrefix mem (wordArrayInitMemory mem ptr n) ptr.toNat := by
  rw [wordArrayInitMemory_eq_header]
  exact Benchmarks.EAS.Attester.wordArrayHeaderMemory_prefix _ _ _

theorem wordArrayInitMemory_zeroCopy (mem cd : ByteArray) (ptr : UInt256) (n : Nat)
    (hmem : mem.size ≤ ptr.toNat) (hptr : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 32 < UInt256.size) :
    cd.write cd.size (wordArrayInitMemory mem ptr n) (ptr + ⟨32⟩).toNat (32 * n) =
      wordArrayInitMemory mem ptr n := by
  apply writeOutsideSource_eq_of_dest _ _ _ _ _ (le_refl _)
  rw [wordArrayInitMemory_size _ _ _ hmem hptr]
  change ptr.toNat + 32 ≤ (ptr + UInt256.ofNat 32).toNat
  rw [uadd_word_ofNat_toNat ptr 32 hfit]

theorem wordArrayInitMemory_length (mem : ByteArray) (ptr : UInt256) (n : Nat) :
    memLoad ptr (wordArrayInitMemory mem ptr n) = UInt256.ofNat n := by
  simpa only [← wordArrayInitMemory_eq_header, u256_ofNat_toNat] using
    Benchmarks.EAS.Attester.wordArrayHeaderMemory_length mem ptr.toNat n ptr.val.isLt

theorem wordArrayInitMemory_free (mem : ByteArray) (ptr : UInt256) (n : Nat)
    (hptr : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (wordArrayInitMemory mem ptr n) =
      UInt256.ofNat (ptr.toNat + 32 + 32 * n) := by
  change memLoad (UInt256.ofNat 64) _ = _
  rw [wordArrayInitMemory_eq_header,
    Benchmarks.EAS.Attester.wordArrayHeaderMemory_freePtr _ _ _ hptr]
  congr 1
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
