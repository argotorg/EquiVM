import Benchmarks.UniswapV3.Pool.DynamicWordArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: extend the initialized prefix of a memory array by one word.
theorem WordArrayMemory.push {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p ws) (value : UInt256) :
    WordArrayMemory (writeWord mem (p.toNat + 32 * ws.length) value) p (ws ++ [value]) := by
  refine ⟨?_, fun j hj ↦ ?_⟩
  · rw [List.length_append, List.length_singleton, writeWord_sparse_size]
    omega
  · by_cases hi : j < ws.length
    · rw [List.getElem_append_left hi, writeWord_sparse_read_preserved _ _ _ _
        (Or.inl ⟨by omega, by have h := hm.size; omega⟩), hm.read j hi]
    · have he : j = ws.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      subst j
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero,
        writeWord_sparse_read_back]

theorem WordArrayMemory.take {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p ws) (n : Nat) : WordArrayMemory mem p (ws.take n) := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · simp only [List.length_take]; have h := hm.size; omega
  · simpa only [List.getElem_take] using hm.read i (by simp only [List.length_take] at hi; omega)

-- LIBRARY CANDIDATE: reserve a full array but track only the prefix already assigned.
abbrev PartialWordArrayMemory (mem : ByteArray) (p : UInt256) (ws : List UInt256) (n : Nat) : Prop :=
  WordArrayMemory mem p (UInt256.ofNat ws.length :: ws.take n)

theorem DynamicWordArrayMemory.partial {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : DynamicWordArrayMemory mem p ws) (n : Nat) : PartialWordArrayMemory mem p ws n :=
  hm.take (n + 1)

theorem PartialWordArrayMemory.complete {mem : ByteArray} {p : UInt256} {ws : List UInt256} {n : Nat}
    (hm : PartialWordArrayMemory mem p ws n) (hn : ws.length ≤ n) : DynamicWordArrayMemory mem p ws := by
  simpa only [PartialWordArrayMemory, List.take_of_length_le hn] using hm

theorem PartialWordArrayMemory.header {mem : ByteArray} {p : UInt256} {ws : List UInt256} {n : Nat}
    (hm : PartialWordArrayMemory mem p ws n)
    (hb : p.toNat + 32 * (ws.length + 1) < UInt256.size) :
    memLoad p mem = UInt256.ofNat ws.length := by
  have h := hm.load 0 (by simp)
    (by simp only [List.length_cons, List.length_take]; omega)
  change memLoad (p + (⟨0⟩ : UInt256)) mem = UInt256.ofNat ws.length at h
  simpa only [u256_add_zero] using h

theorem PartialWordArrayMemory.push {mem : ByteArray} {p : UInt256} {ws : List UInt256} {n : Nat}
    (hm : PartialWordArrayMemory mem p ws n) (value : UInt256) (hn : n < ws.length) :
    PartialWordArrayMemory (writeWord mem (p.toNat + 32 * (n + 1)) value) p (ws.set n value) (n + 1) := by
  have htake : (ws.set n value).take (n + 1) = ws.take n ++ [value] := by
    rw [List.take_succ_eq_append_getElem (by simpa only [List.length_set] using hn),
      List.getElem_set_self, List.take_set, List.set_eq_of_length_le]
    simp only [List.length_take]; omega
  have h := WordArrayMemory.push hm value
  simpa only [PartialWordArrayMemory, List.length_cons, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hn), List.length_set, htake, List.cons_append] using h

-- GENERALIZES Reasoning.HeapMemory.MemoryCursor.writeAbove to any non-header write.
theorem MemoryCursor.writeWord {mem : ByteArray} {aw free : UInt256}
    (hm : MemoryCursor mem aw free) (off : Nat) (value : UInt256) (hl : 96 ≤ off) :
    MemoryCursor (writeWord mem off value) aw free := by
  refine ⟨?_, ?_, hm.lower, hm.active⟩
  · rw [writeWord_sparse_size]; have h := hm.size; omega
  · rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hl, hm.size⟩), hm.free]

end Benchmarks.UniswapV3.Pool
