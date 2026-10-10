import Benchmarks.UniswapV3.Pool.WordArrayExtend

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def observeEncodeFirstHead (mem : ByteArray) (p : UInt256) (n : Nat) : ByteArray :=
  writeWord (writeWord mem p.toNat (UInt256.ofNat 64)) (p.toNat + 64) (UInt256.ofNat n)
def observeEncodeFirstMem (mem : ByteArray) (p : UInt256) (xs : List UInt256) : ByteArray :=
  writeWordArray (observeEncodeFirstHead mem p xs.length) (p.toNat + 96) xs
def observeEncodeSecondHead (mem : ByteArray) (p : UInt256) (n m : Nat) : ByteArray :=
  writeWord (writeWord mem (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)))
    (p.toNat + 96 + 32 * n) (UInt256.ofNat m)
def observeEncodeMem (mem : ByteArray) (p : UInt256) (xs ys : List UInt256) : ByteArray :=
  writeWordArray (observeEncodeSecondHead (observeEncodeFirstMem mem p xs) p xs.length ys.length)
    (p.toNat + 128 + 32 * xs.length) ys
def observeEncodeWords (xs ys : List UInt256) : List UInt256 :=
  [UInt256.ofNat 64, UInt256.ofNat (96 + 32 * xs.length), UInt256.ofNat xs.length] ++
    xs ++ [UInt256.ofNat ys.length] ++ ys

theorem observeEncodeFirstPrefix (mem : ByteArray) (p : UInt256) (xs : List UInt256) :
    MemoryPrefix mem (observeEncodeFirstMem mem p xs) p.toNat :=
  ((memoryPrefix_sparse_writeWord mem p.toNat p.toNat _ (Or.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ (p.toNat + 64) p.toNat _ (Or.inl (by omega)))).trans
      (writeWordArray_prefix _ _ _ xs (by omega))

theorem observeEncodeSecondPrefix (mem : ByteArray) (p : UInt256) (n m : Nat) :
    MemoryPrefix mem (observeEncodeSecondHead mem p n m) p.toNat :=
  (memoryPrefix_sparse_writeWord mem (p.toNat + 32) p.toNat _ (Or.inl (by omega))).trans
    (memoryPrefix_sparse_writeWord _ (p.toNat + 96 + 32 * n) p.toNat _ (Or.inl (by omega)))

theorem observeEncodePrefix (mem : ByteArray) (p : UInt256) (xs ys : List UInt256) :
    MemoryPrefix mem (observeEncodeMem mem p xs ys) p.toNat :=
  ((observeEncodeFirstPrefix mem p xs).trans (observeEncodeSecondPrefix _ p _ _)).trans
    (writeWordArray_prefix _ _ _ ys (by omega))

theorem observeEncodeCursor {mem : ByteArray} {aw p : UInt256} (hm : MemoryCursor mem aw p)
    (xs ys : List UInt256) : MemoryCursor (observeEncodeMem mem p xs ys) aw p := by
  have hp := hm.lower
  have h1 := MemoryCursor.writeWord hm p.toNat (UInt256.ofNat 64) (by omega)
  have h2 := MemoryCursor.writeWord h1 (p.toNat + 64) (UInt256.ofNat xs.length) (by omega)
  have h3 := MemoryCursor.writeWordArray h2 (p.toNat + 96) xs (by omega)
  have h4 := MemoryCursor.writeWord h3 (p.toNat + 32) (UInt256.ofNat (96 + 32 * xs.length)) (by omega)
  have h5 := MemoryCursor.writeWord h4 (p.toNat + 96 + 32 * xs.length) (UInt256.ofNat ys.length) (by omega)
  exact MemoryCursor.writeWordArray h5 (p.toNat + 128 + 32 * xs.length) ys (by omega)

theorem observeEncodeMemory (mem : ByteArray) (p : UInt256) (xs ys : List UInt256)
    (hb : p.toNat + 128 + 32 * (xs.length + ys.length) < UInt256.size) :
    WordArrayMemory (observeEncodeMem mem p xs ys) p (observeEncodeWords xs ys) := by
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hpS : (p + UInt256.ofNat (96 + 32 * xs.length)).toNat =
      p.toNat + 96 + 32 * xs.length := by
    rw [uadd_word_ofNat_toNat _ _ (by omega)]; omega
  have hfirst : WordArrayMemory (observeEncodeFirstMem mem p xs) p [UInt256.ofNat 64] := by
    have h := (writeWord_singleton mem p (UInt256.ofNat 64)).write_disjoint
      (p.toNat + 64) (UInt256.ofNat xs.length) (Or.inr (by simp))
    exact h.writeWordArray_disjoint (p.toNat + 96) xs (Or.inr (by simp))
  have ht : WordArrayMemory (observeEncodeFirstMem mem p xs)
      (p + UInt256.ofNat 64) (UInt256.ofNat xs.length :: xs) := by
    have h := writeWord_singleton (writeWord mem p.toNat (UInt256.ofNat 64))
      (p + UInt256.ofNat 64) (UInt256.ofNat xs.length)
    have he := h.extend xs
    simpa only [hp64, List.length_singleton, List.singleton_append,
      show p.toNat + 64 + 32 * 1 = p.toNat + 96 by omega] using he
  have hh := hfirst.push (UInt256.ofNat (96 + 32 * xs.length))
  have hh' : WordArrayMemory
      (observeEncodeSecondHead (observeEncodeFirstMem mem p xs) p xs.length ys.length) p
      [UInt256.ofNat 64, UInt256.ofNat (96 + 32 * xs.length)] := by
    exact hh.write_disjoint (p.toNat + 96 + 32 * xs.length) (UInt256.ofNat ys.length)
      (Or.inr (by simp; omega))
  have ht' := (ht.write_disjoint (p.toNat + 32) (UInt256.ofNat (96 + 32 * xs.length))
    (Or.inl (by rw [hp64]))).write_disjoint (p.toNat + 96 + 32 * xs.length)
    (UInt256.ofNat ys.length) (Or.inr (by rw [hp64]; simp only [List.length_cons]; omega))
  have hhFinal := hh'.writeWordArray_disjoint (p.toNat + 128 + 32 * xs.length) ys
    (Or.inr (by simp; omega))
  have htFinal := ht'.writeWordArray_disjoint (p.toNat + 128 + 32 * xs.length) ys
    (Or.inr (by rw [hp64]; simp only [List.length_cons]; omega))
  have hsFinal : WordArrayMemory (observeEncodeMem mem p xs ys)
      (p + UInt256.ofNat (96 + 32 * xs.length)) (UInt256.ofNat ys.length :: ys) := by
    have h := (writeWord_singleton
      (writeWord (observeEncodeFirstMem mem p xs) (p.toNat + 32)
        (UInt256.ofNat (96 + 32 * xs.length)))
      (p + UInt256.ofNat (96 + 32 * xs.length)) (UInt256.ofNat ys.length)).extend ys
    simpa only [hpS, List.length_singleton, List.singleton_append,
      show p.toNat + 96 + 32 * xs.length + 32 * 1 = p.toNat + 128 + 32 * xs.length by omega] using h
  have htogether := hhFinal.append htFinal (by rw [hp64]; simp)
  have hall := htogether.append hsFinal (by
    rw [hpS]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  simpa only [observeEncodeWords, List.append_assoc, List.cons_append, List.nil_append] using hall

end Benchmarks.UniswapV3.Pool
