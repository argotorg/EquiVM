import Benchmarks.EAS.Attester.PairAllocMemory
import Benchmarks.EAS.Attester.UnboundedMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: sequential ABI word stores, with unbounded byte-array reads.
def wordSequenceMemory (mem : ByteArray) (off : Nat) : List UInt256 → ByteArray
  | [] => mem
  | word :: words => wordSequenceMemory (writeWord mem off word) (off + 32) words

theorem wordSequenceMemory_prefix (mem : ByteArray) (off : Nat) (words : List UInt256) :
    MemoryPrefix mem (wordSequenceMemory mem off words) off := by
  induction words generalizing mem off with
  | nil => exact .refl _ _
  | cons word words ih =>
      exact (memoryPrefix_sparse_writeWord mem off off word (.inl (le_refl _))).trans
        ((ih _ _).mono (by omega))

theorem wordSequenceMemory_size {mem : ByteArray} {off : Nat} (words : List UInt256)
    (hoff : off ≤ mem.size) :
    (wordSequenceMemory mem off words).size = max mem.size (off + 32 * words.length) := by
  induction words generalizing mem off with
  | nil => simp only [wordSequenceMemory, List.length_nil, Nat.mul_zero, Nat.add_zero]; omega
  | cons word words ih =>
      rw [wordSequenceMemory, ih (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
      simp only [List.length_cons]; omega

theorem wordSequenceMemory_read_below (mem : ByteArray) (off : Nat) (words : List UInt256)
    (read : Nat) (hin : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off) :
    (wordSequenceMemory mem off words).readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction words generalizing mem off with
  | nil => rfl
  | cons word words ih =>
      rw [wordSequenceMemory, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
      exact writeWord_sparse_read_preserved mem off read word (.inl ⟨hbelow, hin⟩)

theorem wordSequenceMemory_read (mem : ByteArray) (off : Nat) (words : List UInt256)
    :
    (wordSequenceMemory mem off words).readWithPadding off (32 * words.length) = wordBytes words :=
        by
  induction words generalizing mem off with
  | nil => simp only [wordSequenceMemory, List.length_nil, Nat.mul_zero,
      byteArray_readWithPadding_zero, wordBytes]
  | cons word words ih =>
      have hext : off + 32 ≤ (writeWord mem off word).size := by rw [writeWord_sparse_size]; omega
      have hspan : off + 32 + 32 * words.length ≤
          (wordSequenceMemory (writeWord mem off word) (off + 32) words).size := by
        rw [wordSequenceMemory_size words hext]
        exact Nat.le_max_right _ _
      rw [wordSequenceMemory, List.length_cons,
        show 32 * (words.length + 1) = 32 + 32 * words.length by omega,
        readWithPadding_split _ _ _ _ hspan,
        wordSequenceMemory_read_below _ _ _ _ hext (le_refl _), writeWord_sparse_read_back,
        ih _ _]
      rfl

theorem wordSequenceMemory_read_below_unbounded (mem : ByteArray) (off : Nat)
    (words : List UInt256) (read len : Nat) (hin : read + len ≤ mem.size)
    (hbelow : read + len ≤ off) :
    (wordSequenceMemory mem off words).readWithPadding read len = mem.readWithPadding read len := by
  induction words generalizing mem off with
  | nil => rfl
  | cons word words ih =>
      rw [wordSequenceMemory, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
      exact writeWord_sparse_read_preserved_unbounded mem off read len word hin (.inl hbelow)

def pairSequenceWords (values : Nat → UInt256 × UInt256) (i : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => (values i).1 :: (values i).2 :: pairSequenceWords values (i + 1) n

theorem pairSequenceWords_length (values : Nat → UInt256 × UInt256) (i n : Nat) :
    (pairSequenceWords values i n).length = 2 * n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [pairSequenceWords, List.length_cons, ih]; omega

end Reasoning.Theory
