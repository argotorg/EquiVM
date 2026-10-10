import Benchmarks.UniswapV3.Pool.WordArrayPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATES: array slices and their contiguous byte representation.
def wordArrayBytes (ws : List UInt256) : ByteArray :=
  (ws.flatMap EVM.Word.toBytesBE).toByteArray

theorem wordArrayBytes_nil : wordArrayBytes [] = ByteArray.empty := rfl

theorem wordArrayBytes_cons (w : UInt256) (ws : List UInt256) :
    wordArrayBytes (w :: ws) = w.toByteArray ++ wordArrayBytes ws := by
  simp only [wordArrayBytes, List.flatMap_cons, List.toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem wordArrayBytes_append (xs ys : List UInt256) :
    wordArrayBytes (xs ++ ys) = wordArrayBytes xs ++ wordArrayBytes ys := by
  simp only [wordArrayBytes, List.flatMap_append, List.toByteArray_append]

theorem wordArrayBytes_length (ws : List UInt256) :
    (ws.flatMap EVM.Word.toBytesBE).length = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.flatMap_cons, List.length_append, word_toBytesBE_length_32,
        List.length_cons, ih]
      omega

theorem WordArrayMemory.tail {mem : ByteArray} {p w : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p (w :: ws)) (hb : p.toNat + 32 < UInt256.size) :
    WordArrayMemory mem (p + UInt256.ofNat 32) ws := by
  have hp := uadd_word_ofNat_toNat p 32 hb
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [hp]; have hs := hm.size; simp only [List.length_cons] at hs; omega
  · have h := hm.read (i + 1) (by simp only [List.length_cons]; omega)
    rw [List.getElem_cons_succ] at h
    rw [hp, show p.toNat + 32 + 32 * i = p.toNat + 32 * (i + 1) by omega]
    exact h

theorem WordArrayMemory.bytes {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p ws) (hb : p.toNat + 32 * ws.length < UInt256.size) :
    mem.readWithPadding p.toNat (32 * ws.length) = wordArrayBytes ws := by
  induction ws generalizing p with
  | nil => simp only [List.length_nil, Nat.mul_zero, byteArray_readWithPadding_zero, wordArrayBytes_nil]
  | cons w ws ih =>
      have hr : mem.readWithPadding p.toNat 32 = w.toByteArray := by
        simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using hm.read 0 (by simp)
      cases ws with
      | nil =>
          simpa only [List.length_cons, List.length_nil, wordArrayBytes_cons,
            wordArrayBytes_nil, ByteArray.append_empty] using hr
      | cons x xs =>
          have hp := uadd_word_ofNat_toNat p 32 (by simp only [List.length_cons] at hb; omega)
          have ht := ih (hm.tail (by simp only [List.length_cons] at hb; omega))
            (by rw [hp]; simp only [List.length_cons] at hb ⊢; omega)
          rw [hp] at ht
          rw [List.length_cons, show 32 * ((x :: xs).length + 1) = 32 + 32 * (x :: xs).length by omega,
            byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide)
              (by simp only [List.length_cons]; omega)
              (by have hs := hm.size; simp only [List.length_cons] at hs ⊢; omega),
            hr, ht, wordArrayBytes_cons]
          rw [wordArrayBytes_cons, wordArrayBytes_cons]

theorem WordArrayMemory.append {mem : ByteArray} {p q : UInt256} {xs ys : List UInt256}
    (hx : WordArrayMemory mem p xs) (hy : WordArrayMemory mem q ys)
    (hq : q.toNat = p.toNat + 32 * xs.length) : WordArrayMemory mem p (xs ++ ys) := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have hs := hy.size; rw [hq] at hs; rw [List.length_append]; omega
  · by_cases hil : i < xs.length
    · rw [List.getElem_append_left hil]; exact hx.read i hil
    · have hir : i - xs.length < ys.length := by simp only [List.length_append] at hi; omega
      rw [List.getElem_append_right (by omega)]
      have h := hy.read (i - xs.length) hir
      rw [hq, show p.toNat + 32 * xs.length + 32 * (i - xs.length) = p.toNat + 32 * i by omega] at h
      exact h

theorem writeWordArray_region (mem : ByteArray) (p : UInt256) (ws : List UInt256)
    (hp : p.toNat ≤ mem.size) : WordArrayMemory (writeWordArray mem p.toNat ws) p ws := by
  refine ⟨?_, writeWordArray_read _ _ _⟩
  by_cases hn : ws = []
  · subst ws; exact hp
  · rw [writeWordArray_size _ _ _ hn]; exact Nat.le_max_right _ _

end Benchmarks.UniswapV3.Pool
