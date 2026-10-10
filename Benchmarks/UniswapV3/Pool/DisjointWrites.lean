import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: one-byte reads determine a byte array of known size.
theorem byteArray_eq_of_read_one (a b : ByteArray) (hs : a.size = b.size)
    (hr : ∀ i, i < a.size → a.readWithPadding i 1 = b.readWithPadding i 1) : a = b := by
  apply ByteArray.ext_getElem hs
  intro i hi hj
  have hh := hr i hi
  rw [readWithPadding_eq_extract_unbounded _ _ 1 (by decide) (by omega),
    readWithPadding_eq_extract_unbounded _ _ 1 (by decide) (by omega)] at hh
  have he := congrArg (fun v : ByteArray ↦ v.get? 0) hh
  have ha : 0 < (a.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  have hb : 0 < (b.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  simp only [ByteArray.get?, dif_pos ha, dif_pos hb, Option.some.injEq] at he
  simpa only [ByteArray.get, ByteArray.data_extract, Array.getElem_extract, Nat.add_zero] using he

-- LIBRARY CANDIDATE: a contained word write only changes the bytes of its own window.
theorem writeWord_read_one (mem : ByteArray) (off i : Nat) (word : UInt256)
    (hoff : off + 32 ≤ mem.size) (hi : i < mem.size) :
    (writeWord mem off word).readWithPadding i 1 =
      if off ≤ i ∧ i < off + 32 then word.toByteArray.extract (i - off) (i - off + 1)
      else mem.readWithPadding i 1 := by
  have hgap : off - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]
    exact USize.size_pos
  split
  · rename_i h
    have hw := writeWord_read_window mem off (i - off) 1 word (by omega) (by decide)
      (by decide) hgap
    simpa only [Nat.add_sub_of_le h.1] using hw
  · rename_i h
    apply writeWord_read_preserved_len mem off i 1 word hgap _ (by decide) (by decide)
    by_cases hlo : i < off
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩

-- LIBRARY CANDIDATE: contained writes to disjoint word windows commute.
theorem writeWord_comm_of_disjoint (mem : ByteArray) (a b : Nat) (x y : UInt256)
    (ha : a + 32 ≤ mem.size) (hb : b + 32 ≤ mem.size)
    (hd : a + 32 ≤ b ∨ b + 32 ≤ a) :
    writeWord (writeWord mem a x) b y = writeWord (writeWord mem b y) a x := by
  have hsa : (writeWord mem a x).size = mem.size := by
    rw [writeWord_sparse_size, max_eq_left ha]
  have hsb : (writeWord mem b y).size = mem.size := by
    rw [writeWord_sparse_size, max_eq_left hb]
  have hsab : (writeWord (writeWord mem a x) b y).size = mem.size := by
    rw [writeWord_sparse_size, hsa, max_eq_left hb]
  have hsba : (writeWord (writeWord mem b y) a x).size = mem.size := by
    rw [writeWord_sparse_size, hsb, max_eq_left ha]
  apply byteArray_eq_of_read_one _ _ (hsab.trans hsba.symm)
  intro i hi
  rw [hsab] at hi
  rw [writeWord_read_one (writeWord mem a x) b i y (by rw [hsa]; exact hb) (by rwa [hsa]),
    writeWord_read_one (writeWord mem b y) a i x (by rw [hsb]; exact ha) (by rwa [hsb]),
    writeWord_read_one mem a i x ha hi, writeWord_read_one mem b i y hb hi]
  by_cases hia : a ≤ i ∧ i < a + 32
  · have hib : ¬ (b ≤ i ∧ i < b + 32) := by omega
    simp only [if_pos hia, if_neg hib]
  · simp only [if_neg hia]

-- LIBRARY CANDIDATE: reordering distinct contained word writes preserves the result.
theorem writeCascade_perm (mem : ByteArray) {left right : List (Nat × UInt256)}
    (hp : left.Perm right)
    (hb : ∀ w ∈ left, w.1 + 32 ≤ mem.size)
    (hd : ∀ x ∈ left, ∀ y ∈ left, x ≠ y → x.1 + 32 ≤ y.1 ∨ y.1 + 32 ≤ x.1) :
    writeCascade mem left = writeCascade mem right := by
  induction hp generalizing mem with
  | nil => rfl
  | @cons x l r hp ih =>
    change writeCascade (writeWord mem x.1 x.2) l = writeCascade (writeWord mem x.1 x.2) r
    apply ih
    · intro w hw
      rw [writeWord_sparse_size, max_eq_left (hb x List.mem_cons_self)]
      exact hb w (List.mem_cons_of_mem x hw)
    · intro a ha b hb' hn
      exact hd a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb') hn
  | swap x y l =>
    change writeCascade (writeWord (writeWord mem y.1 y.2) x.1 x.2) l =
      writeCascade (writeWord (writeWord mem x.1 x.2) y.1 y.2) l
    by_cases he : x = y
    · rw [he]
    · rw [writeWord_comm_of_disjoint mem y.1 x.1 y.2 x.2
        (hb y (by simp)) (hb x (by simp)) (hd y (by simp) x (by simp) (Ne.symm he))]
  | @trans l m r hp hq ihp ihq =>
    apply (ihp mem hb hd).trans
    apply ihq
    · intro w hw
      exact hb w (hp.mem_iff.mpr hw)
    · intro a ha b hb' hn
      exact hd a (hp.mem_iff.mpr ha) b (hp.mem_iff.mpr hb') hn

end Benchmarks.UniswapV3.Pool
