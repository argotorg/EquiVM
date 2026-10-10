import Benchmarks.UniswapV3.Pool.WordArrayBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATES: append words to a memory region and preserve disjoint regions.
theorem WordArrayMemory.extend {mem : ByteArray} {p : UInt256} {xs : List UInt256}
    (hm : WordArrayMemory mem p xs) (ys : List UInt256) :
    WordArrayMemory (writeWordArray mem (p.toNat + 32 * xs.length) ys) p (xs ++ ys) := by
  induction ys generalizing mem xs with
  | nil => simpa only [writeWordArray, List.append_nil] using hm
  | cons y ys ih =>
      have h := ih (hm.push y)
      simpa only [writeWordArray, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, show p.toNat + 32 * (xs.length + 1) = p.toNat + 32 * xs.length + 32 by omega]
        using h

theorem WordArrayMemory.writeWordArray_disjoint {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p ws) (off : Nat) (values : List UInt256)
    (hd : off + 32 * values.length ≤ p.toNat ∨ p.toNat + 32 * ws.length ≤ off) :
    WordArrayMemory (writeWordArray mem off values) p ws := by
  induction values generalizing mem off with
  | nil => exact hm
  | cons w values ih =>
      simp only [List.length_cons] at hd
      exact ih (hm.write_disjoint off w (by rcases hd with h | h <;> omega)) (off + 32)
        (by rcases hd with h | h <;> omega)

theorem writeWord_singleton (mem : ByteArray) (p w : UInt256) :
    WordArrayMemory (writeWord mem p.toNat w) p [w] := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [writeWord_sparse_size]; simp only [List.length_singleton]; omega
  · have hz : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, writeWord_sparse_read_back]

-- LIBRARY CANDIDATE: a word-copy region preserves the free-memory header.
theorem MemoryCursor.writeWordArray {mem : ByteArray} {aw p : UInt256}
    (hm : MemoryCursor mem aw p) (off : Nat) (ws : List UInt256) (hlo : 96 ≤ off) :
    MemoryCursor (writeWordArray mem off ws) aw p := by
  induction ws generalizing mem off with
  | nil => exact hm
  | cons w ws ih =>
      exact ih (MemoryCursor.writeWord hm off w hlo) (off + 32) (by omega)

end Benchmarks.UniswapV3.Pool
