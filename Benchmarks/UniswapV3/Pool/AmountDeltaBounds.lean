import Benchmarks.UniswapV3.Pool.AmountDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem amountDeltaSort (a : AmountDeltaArgs) (hfit : a.Fits) :
    (amountDeltaLower a).toNat ≤ (amountDeltaUpper a).toNat ∧
      (amountDeltaLower a).toNat < 2 ^ 160 ∧ (amountDeltaUpper a).toNat < 2 ^ 160 := by
  by_cases hs : a.sqrtB.toNat < a.sqrtA.toNat
  · simp only [amountDeltaLower, amountDeltaUpper, if_pos hs]
    exact ⟨Nat.le_of_lt hs, hfit.2.1, hfit.1⟩
  · simp only [amountDeltaLower, amountDeltaUpper, if_neg hs]
    exact ⟨Nat.le_of_not_gt hs, hfit.1, hfit.2.1⟩

theorem amountDeltaDifference_toNat (a : AmountDeltaArgs) (hfit : a.Fits) :
    (amountDeltaDifference a).toNat = (amountDeltaUpper a).toNat - (amountDeltaLower a).toNat := by
  have hs := amountDeltaSort a hfit
  have hc : UInt256.land (UInt256.sub (amountDeltaUpper a) (amountDeltaLower a))
      (UInt256.ofNat (2 ^ 160 - 1)) = UInt256.sub (amountDeltaUpper a) (amountDeltaLower a) := by
    apply u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide)
    change (UInt256.sub (amountDeltaUpper a) (amountDeltaLower a)).toNat < 2 ^ 160
    rw [usub_toNat hs.1]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hs.2.2
  rw [amountDeltaDifference, hc, usub_toNat hs.1]

theorem amountDeltaNumerator_toNat (a : AmountDeltaArgs) (hfit : a.Fits) :
    (amountDeltaNumerator a).toNat = a.liquidity.toNat * 2 ^ 96 :=
  shiftLeft96_toNat_of_lt_160 _ (by have h := hfit.2.2; omega)

theorem amountDeltaNumerator_lt (a : AmountDeltaArgs) (hfit : a.Fits) :
    (amountDeltaNumerator a).toNat < 2 ^ 224 := by
  rw [amountDeltaNumerator_toNat a hfit]
  calc
    a.liquidity.toNat * 2 ^ 96 < 2 ^ 128 * 2 ^ 96 :=
      Nat.mul_lt_mul_of_pos_right hfit.2.2 (by decide)
    _ = 2 ^ 224 := by norm_num

def amountDeltaBound (second : Bool) (a : AmountDeltaArgs) : Nat :=
  if second then 2 ^ 192 else (amountDeltaNumerator a).toNat

theorem amountDeltaInputsBound (second : Bool) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid second a) :
    0 < (amountDeltaDenominator second a).toNat ∧ amountDeltaBound second a < UInt256.size ∧
      fullMathProduct (amountDeltaFactor second a) (amountDeltaDifference a) ≤
        amountDeltaBound second a * (amountDeltaDenominator second a).toNat := by
  have hs := amountDeltaSort a hfit
  cases second
  · have hlo : 0 < (amountDeltaLower a).toNat := hv.resolve_left (by decide)
    refine ⟨by change 0 < (amountDeltaUpper a).toNat; omega, ?_, ?_⟩
    · change (amountDeltaNumerator a).toNat < 2 ^ 256
      have hn := amountDeltaNumerator_lt a hfit
      omega
    · change (amountDeltaNumerator a).toNat * (amountDeltaDifference a).toNat ≤
        (amountDeltaNumerator a).toNat * (amountDeltaUpper a).toNat
      rw [amountDeltaDifference_toNat a hfit]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  · refine ⟨by change 0 < (UInt256.ofNat (2 ^ 96)).toNat; decide,
      by change 2 ^ 192 < UInt256.size; decide, ?_⟩
    simp only [amountDeltaFactor, amountDeltaDenominator, amountDeltaBound, if_true, fullMathProduct]
    rw [show (UInt256.ofNat (2 ^ 96)).toNat = 2 ^ 96 from by decide,
      show (2 ^ 192 : Nat) * 2 ^ 96 = 2 ^ 128 * 2 ^ 160 from by norm_num]
    rw [amountDeltaDifference_toNat a hfit]
    exact Nat.mul_le_mul (Nat.le_of_lt hfit.2.2)
      (le_trans (Nat.sub_le _ _) (Nat.le_of_lt hs.2.2))

theorem amountDeltaMulValid (second : Bool) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid second a) :
    fullMathRoundValid (amountDeltaFactor second a) (amountDeltaDifference a)
      (amountDeltaDenominator second a) := by
  obtain ⟨hd, hb, hp⟩ := amountDeltaInputsBound second a hfit hv
  exact fullMathRoundValid_of_product_le _ _ _ _ hd hb hp

theorem amountDeltaMulResult_le (second : Bool) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid second a) :
    (amountDeltaMulResult second a).toNat ≤ amountDeltaBound second a := by
  obtain ⟨hd, hb, hp⟩ := amountDeltaInputsBound second a hfit hv
  unfold amountDeltaMulResult
  split_ifs
  · exact fullMathRoundResult_le_bound _ _ _ _ hd hb hp
  · exact fullMathResult_le_bound _ _ _ _ hd hb hp

theorem amountDeltaResult_lt255 (second : Bool) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid second a) :
    (amountDeltaResult second a).toNat < 2 ^ 255 := by
  have hb : amountDeltaBound second a < 2 ^ 255 := by
    cases second
    · change (amountDeltaNumerator a).toNat < 2 ^ 255
      have hn := amountDeltaNumerator_lt a hfit
      omega
    · change 2 ^ 192 < 2 ^ 255
      decide
  have hm := lt_of_le_of_lt (amountDeltaMulResult_le second a hfit hv) hb
  cases second
  · simp only [amountDeltaResult, Bool.false_eq_true, if_false]
    split_ifs
    · rw [unsafeDivRoundResult_toNat]
      exact lt_of_le_of_lt (unsafeDivRoundNat_le _ _) hm
    · rw [udiv_toNat]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hm
  · simpa only [amountDeltaResult, if_true] using hm

end Benchmarks.UniswapV3.Pool
