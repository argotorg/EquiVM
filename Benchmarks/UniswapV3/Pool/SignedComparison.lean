import Benchmarks.UniswapV3.Pool.SignedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: signed comparisons of words represented by bounded integers.
theorem slt_of_signed_values {a b : UInt256} {i j : Int}
    (ha : i = if a.toNat < 2 ^ 255 then Int.ofNat a.toNat else Int.ofNat a.toNat - 2 ^ 256)
    (hb : j = if b.toNat < 2 ^ 255 then Int.ofNat b.toNat else Int.ofNat b.toNat - 2 ^ 256) :
    UInt256.slt a b = if i < j then ⟨1⟩ else ⟨0⟩ := by
  have hab : a.toNat < 2 ^ 256 := a.val.isLt
  have hbb : b.toNat < 2 ^ 256 := b.val.isLt
  have hbool : UInt256.sltBool a b = decide (i < j) := by
    rw [ha, hb]
    unfold UInt256.sltBool
    have hcmp : decide (a < b) = decide (a.toNat < b.toNat) := rfl
    simp only [hcmp, ge_iff_le, ← Nat.not_lt]
    by_cases ha' : a.toNat < 2 ^ 255 <;> by_cases hb' : b.toNat < 2 ^ 255
    all_goals simp only [ha', hb', ↓reduceIte, not_true_eq_false, not_false_eq_true]
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [decide_eq_true_eq, Bool.false_eq_true, Int.ofNat_eq_natCast]
    all_goals try simp only [false_iff, true_iff]
    all_goals omega
  rw [UInt256.slt, hbool]
  by_cases h : i < j <;> simp only [h, decide_true, decide_false, ↓reduceIte, UInt256.fromBool, Bool.toUInt256] <;> rfl



-- LIBRARY CANDIDATE: decoding the two's-complement word of a bounded integer.
theorem wordOfInt_signed_value (i : Int) (hlo : -(2 ^ 255 : Int) ≤ i) (hhi : i < 2 ^ 255) :
    i = if (EVM.wordOfInt i).toNat < 2 ^ 255 then Int.ofNat (EVM.wordOfInt i).toNat
      else Int.ofNat (EVM.wordOfInt i).toNat - 2 ^ 256 := by
  by_cases hn : i < 0
  · have hbound : i.natAbs < UInt256.size := by
      have hi : (i.natAbs : Int) = -i := by rw [Int.natCast_natAbs, abs_of_neg hn]
      change i.natAbs < 2 ^ 256
      omega
    rw [wordOfInt_toNat_of_neg_of_abs_lt i hn hbound]
    have hi : (i.natAbs : Int) = -i := by rw [Int.natCast_natAbs, abs_of_neg hn]
    change i = if 2 ^ 256 - i.natAbs < 2 ^ 255 then
      Int.ofNat (2 ^ 256 - i.natAbs) else Int.ofNat (2 ^ 256 - i.natAbs) - 2 ^ 256
    rw [if_neg (by omega)]
    simp only [Int.ofNat_eq_natCast]
    omega
  · have hnonneg : 0 ≤ i := by omega
    have hi : (i.toNat : Int) = i := Int.toNat_of_nonneg hnonneg
    have hword : (EVM.wordOfInt i).toNat = i.toNat := by
      rw [wordOfInt_nonneg i hnonneg]
      change i.toNat % UInt256.size = i.toNat
      exact Nat.mod_eq_of_lt (by change i.toNat < 2 ^ 256; omega)
    rw [hword, if_pos (by omega)]
    exact hi.symm

theorem slt_wordOfInt (i j : Int)
    (hilo : -(2 ^ 255 : Int) ≤ i) (hihi : i < 2 ^ 255)
    (hjlo : -(2 ^ 255 : Int) ≤ j) (hjhi : j < 2 ^ 255) :
    UInt256.slt (EVM.wordOfInt i) (EVM.wordOfInt j) = if i < j then ⟨1⟩ else ⟨0⟩ :=
  slt_of_signed_values (wordOfInt_signed_value i hilo hihi) (wordOfInt_signed_value j hjlo hjhi)

theorem sgt_eq_slt_swap (a b : UInt256) : UInt256.sgt a b = UInt256.slt b a := by
  unfold UInt256.sgt UInt256.slt UInt256.sgtBool UInt256.sltBool
  by_cases ha : a.toNat ≥ 2 ^ 255 <;> by_cases hb : b.toNat ≥ 2 ^ 255 <;> simp only [ha, hb, ↓reduceIte]

end Benchmarks.UniswapV3.Pool
