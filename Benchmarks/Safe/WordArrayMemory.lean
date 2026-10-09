import Benchmarks.Safe.PaddedWordMemory
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a word array may include implicit zero bytes past stored memory.
def WordArrayMemory (mem : ByteArray) (base : Nat) (words : List UInt256) : Prop :=
  ∀ i (hi : i < words.length), mem.readWithPadding (base + 32 * i) 32 = words[i].toByteArray

theorem WordArrayMemory.cons {mem base word words}
    (hh : mem.readWithPadding base 32 = word.toByteArray)
    (ht : WordArrayMemory mem (base + 32) words) : WordArrayMemory mem base (word :: words) := by
  intro i hi
  cases i with
  | zero => simpa using hh
  | succ i =>
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (ht i (by simpa using hi))

theorem WordArrayMemory.appendLeft {mem base words tail}
    (h : WordArrayMemory mem base (words ++ tail)) : WordArrayMemory mem base words := by
  intro i hi
  have hr := h i (by simp; omega)
  rw [List.getElem_append_left hi] at hr
  exact hr

theorem WordArrayMemory.zeroes (mem : ByteArray) (base n : Nat) (hm : mem.size ≤ base) :
    WordArrayMemory mem base (List.replicate n ⟨0⟩) := by
  intro i hi
  rw [List.getElem_replicate, readPastMemory _ _ _ (by omega)]
  decide +kernel

theorem WordArrayMemory.write (mem : ByteArray) (base : Nat) (words : List UInt256)
    (h : WordArrayMemory mem base words) (hm : mem.size % 32 = 0)
    (hb : base % 32 = 0) (i : Nat) (value : UInt256) (hi : i < words.length) :
    WordArrayMemory (writeWord mem (base + 32 * i) value) base (words.set i value) := by
  intro j hj
  have hj' : j < words.length := by simpa only [List.length_set] using hj
  by_cases hij : i = j
  · subst j
    rw [List.getElem_set_self]
    exact writeWord_sparse_read_back _ _ _
  · rw [List.getElem_set_ne hij]
    rw [writeWord_read_disjoint_padded _ _ _ value
      (alignedReadBounds _ _ hm (by omega)) (by omega)]
    exact h j hj'

theorem WordArrayMemory.writeDisjoint (mem : ByteArray) (base : Nat) (words : List UInt256)
    (h : WordArrayMemory mem base words) (hm : mem.size % 32 = 0)
    (hb : base % 32 = 0) (off : Nat) (value : UInt256)
    (hd : off + 32 ≤ base ∨ base + 32 * words.length ≤ off) :
    WordArrayMemory (writeWord mem off value) base words := by
  intro j hj
  rw [writeWord_read_disjoint_padded _ _ _ value
    (alignedReadBounds _ _ hm (by omega)) (by omega)]
  exact h j hj

theorem WordArrayMemory.scratch (mem : ByteArray) (base : Nat) (words : List UInt256)
    (h : WordArrayMemory mem base words) (hm : 64 ≤ mem.size) (halign : mem.size % 32 = 0)
    (hb : 64 ≤ base) (hbase : base % 32 = 0) (key slot : UInt256) :
    WordArrayMemory (twoWordHashMem key slot mem) base words := by
  intro j hj
  rw [twoWordHashMem_read_padded mem key slot _ hm halign (by omega) (by omega)]
  exact h j hj

theorem WordArrayMemory.tail (mem : ByteArray) (base : Nat) (word : UInt256)
    (words : List UInt256) (h : WordArrayMemory mem base (word :: words)) :
    WordArrayMemory mem (base + 32) words := by
  intro j hj
  have he : base + 32 + 32 * j = base + 32 * (j + 1) := by omega
  rw [he]
  exact h (j + 1) (by simp; omega)

-- LIBRARY CANDIDATE: an in-memory array survives writes after its last element.
theorem WordArrayMemory.writeAfter (mem : ByteArray) (base : Nat) (words : List UInt256)
    (h : WordArrayMemory mem base words) (hin : base + 32 * words.length ≤ mem.size)
    (off : Nat) (value : UInt256) (hafter : base + 32 * words.length ≤ off) :
    WordArrayMemory (writeWord mem off value) base words := by
  intro j hj
  rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by omega⟩)]
  exact h j hj

theorem WordArrayMemory.writeBefore (mem : ByteArray) (base : Nat) (words : List UInt256)
    (h : WordArrayMemory mem base words) (hin : base + 32 * words.length ≤ mem.size)
    (off : Nat) (value : UInt256) (hbefore : off + 32 ≤ base) :
    WordArrayMemory (writeWord mem off value) base words := by
  intro j hj
  rw [writeWord_sparse_read_preserved _ _ _ _ (.inr ⟨by omega, by omega⟩)]
  exact h j hj

-- GENERALIZES ABI array reads to all lengths, using the unbounded memory reader.
theorem WordArrayMemory.read (mem : ByteArray) (base : Nat) (words : List UInt256)
    (h : WordArrayMemory mem base words) (hin : base + 32 * words.length ≤ mem.size) :
    mem.readWithPadding base (32 * words.length) = wordBytes words := by
  induction words generalizing base with
  | nil => exact byteArray_readWithPadding_zero mem base
  | cons w ws ih =>
      have hh : mem.readWithPadding base 32 = w.toByteArray := by
        simpa using h 0 (by simp)
      have ht := ih (base + 32) (h.tail mem base w ws)
        (by simp only [List.length_cons] at hin; omega)
      cases ws with
      | nil => simpa [wordBytes] using hh
      | cons w' ws =>
          have he : 32 * (w :: w' :: ws).length = 32 + 32 * (w' :: ws).length := by
            simp only [List.length_cons]
            omega
          rw [he, byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide)
            (by simp) (by simp only [List.length_cons] at hin ⊢; omega), hh, ht]
          rfl

end Benchmarks.Safe
