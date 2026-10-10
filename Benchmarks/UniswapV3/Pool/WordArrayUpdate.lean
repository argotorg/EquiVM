import Benchmarks.UniswapV3.Pool.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: update one word in an existing array region.
theorem WordArrayMemory.write {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p ws) (i : Nat) (value : UInt256) :
    WordArrayMemory (writeWord mem (p.toNat + 32 * i) value) p (ws.set i value) := by
  refine ⟨?_, ?_⟩
  · rw [List.length_set, writeWord_sparse_size]
    exact le_trans hm.size (Nat.le_max_left _ _)
  · intro j hj
    have hj' : j < ws.length := by simpa only [List.length_set] using hj
    by_cases he : i = j
    · subst j
      rw [List.getElem_set_self hj, writeWord_sparse_read_back]
    · rw [List.getElem_set_ne he hj, writeWord_sparse_read_preserved _ _ _ _]
      · exact hm.read j hj'
      · rcases Nat.lt_or_gt_of_ne he with hlt | hgt
        · exact Or.inr ⟨by omega, by have hs := hm.size; omega⟩
        · exact Or.inl ⟨by omega, by have hs := hm.size; omega⟩

theorem WordArrayMemory.write_disjoint {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p ws) (off : Nat) (value : UInt256)
    (hd : off + 32 ≤ p.toNat ∨ p.toNat + 32 * ws.length ≤ off) :
    WordArrayMemory (writeWord mem off value) p ws := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans hm.size (Nat.le_max_left _ _)
  · rw [writeWord_sparse_read_preserved _ _ _ _, hm.read i hi]
    rcases hd with hbefore | hafter
    · exact Or.inr ⟨by omega, by have hs := hm.size; omega⟩
    · exact Or.inl ⟨by omega, by have hs := hm.size; omega⟩

-- LIBRARY CANDIDATE: an in-place heap write leaves its allocation cursor unchanged.
theorem HeapMemory.writeWithin {mem : ByteArray} {aw free : UInt256}
    (hm : HeapMemory mem aw free) (off : Nat) (value : UInt256)
    (hl : 96 ≤ off) (hin : off + 32 ≤ mem.size) :
    HeapMemory (writeWord mem off value) aw free := by
  have hsize : (writeWord mem off value).size = mem.size := by
    rw [writeWord_sparse_size, Nat.max_eq_left hin]
  refine ⟨by rw [hsize]; exact hm.size, ?_, hm.lower, by rw [hsize]; exact hm.gap, hm.active⟩
  rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hl, hm.size⟩), hm.free]

end Benchmarks.UniswapV3.Pool
