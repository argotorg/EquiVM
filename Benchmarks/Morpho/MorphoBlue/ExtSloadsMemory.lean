import Benchmarks.Morpho.MorphoBlue.Allocation
import Benchmarks.EAS.Attester.WordArrayABI
import Benchmarks.EAS.Attester.StructAllocMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: a padded zero copy beyond both buffers preserves the concrete memory.
theorem byteArray_write_zero_at_end (src mem : ByteArray) (len : Nat) :
    src.write src.size mem mem.size len = mem := by
  unfold ByteArray.write
  split
  · rfl
  · simp only [ge_iff_le, le_refl, if_true, Nat.sub_self, Nat.min_zero, Nat.min_self]
    apply ByteArray.ext
    simp only [ByteArray.data_copySlice, Nat.zero_min, Nat.add_zero,
      Array.extract_empty_of_stop_le_start (le_refl 0), Array.append_empty]
    change mem.data.extract 0 mem.data.size ++ mem.data.extract mem.data.size = mem.data
    rw [Array.extract_size, Array.extract_size_left, Array.append_empty]

-- GENERALIZES wordArrayDataMemory_load from generated word sequences to arbitrary lists.
theorem wordSequenceMemory_getElem {mem : ByteArray} {off : Nat} (words : List UInt256)
    {i : Nat} (hi : i < words.length) (hfit : off + 32 * words.length < UInt256.size) :
    memLoad (UInt256.ofNat (off + 32 * i)) (wordSequenceMemory mem off words) = words[i] := by
  induction words generalizing mem off i with
  | nil => simp at hi
  | cons word words ih =>
      cases i with
      | zero =>
          simp only [wordSequenceMemory, Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
          rw [wordSequenceMemory_load_below _ (by rw [writeWord_sparse_size]; omega)
            (le_refl _) (by simp only [List.length_cons] at hfit; omega)]
          exact memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt (by
            simp only [List.length_cons] at hfit; omega))
      | succ i =>
          simp only [wordSequenceMemory, List.getElem_cons_succ]
          rw [show off + 32 * (i + 1) = off + 32 + 32 * i by omega]
          exact ih (by simp only [List.length_cons] at hi; omega) (by
            simp only [List.length_cons] at hfit; omega)

def extSloadsHeaderMem (n : Nat) : ByteArray :=
  writeWord (writeWord solcFreePtrMem 64 (UInt256.ofNat (160 + 32 * n))) 128 (UInt256.ofNat n)

theorem extSloadsHeader_size (n : Nat) : (extSloadsHeaderMem n).size = 160 := by
  simp only [extSloadsHeaderMem, writeWord_sparse_size, solcFreePtrMem_size]
  rfl

theorem extSloadsHeader_free (n : Nat) :
    memLoad (UInt256.ofNat 64) (extSloadsHeaderMem n) = UInt256.ofNat (160 + 32 * n) := by
  unfold extSloadsHeaderMem Reasoning.Theory.writeWord
  rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size, solcFreePtrMem_size]; decide)
    (.inl (by decide))]
  exact memLoad_write_same _ _ _ _ rfl

theorem extSloadsHeader_length (n : Nat) :
    memLoad (UInt256.ofNat 128) (extSloadsHeaderMem n) = UInt256.ofNat n :=
  memLoad_write_same _ _ _ _ rfl

end Benchmarks.Morpho.MorphoBlue
