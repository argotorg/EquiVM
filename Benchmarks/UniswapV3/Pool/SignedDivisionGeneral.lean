import Benchmarks.UniswapV3.Pool.SignedDivision

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: negate the quotient when the divisor has a negative signed encoding.
theorem sdiv_negative_denominator (a b : UInt256) (hb : 2 ^ 255 ≤ b.toNat)
    (habs : (UInt256.abs b).toNat < 2 ^ 255) :
    UInt256.sdiv a b = UInt256.sub ⟨0⟩ (UInt256.sdiv a (UInt256.abs b)) := by
  by_cases ha : 2 ^ 255 ≤ a.toNat
  · simp only [UInt256.sdiv, if_pos ha, if_pos hb, if_neg (Nat.not_le.mpr habs)]
    simp [UInt256.sub]
  · simp only [UInt256.sdiv, if_neg ha, if_pos hb, if_neg (Nat.not_le.mpr habs)]
    simp [UInt256.sub]

-- GENERALIZES wordOfInt_sdiv_nat to a divisor of either sign, excluding signed MIN.
theorem wordOfInt_sdiv (i j : Int)
    (hilo : -(2 ^ 255 : Int) ≤ i) (hihi : i < (2 ^ 255 : Int))
    (hjlo : -(2 ^ 255 : Int) < j) (hjhi : j < (2 ^ 255 : Int)) :
    UInt256.sdiv (EVM.wordOfInt i) (EVM.wordOfInt j) = EVM.wordOfInt (i.tdiv j) := by
  by_cases hj : j < 0
  · have hn : j.natAbs < 2 ^ 255 := by omega
    have hw := wordOfInt_toNat_of_neg_of_abs_lt j hj
      (show j.natAbs < EVM.wordModulus by change _ < 2 ^ 256; omega)
    have hhigh : 2 ^ 255 ≤ (EVM.wordOfInt j).toNat := by
      rw [hw]
      change 2 ^ 255 ≤ 2 ^ 256 - j.natAbs
      omega
    have ha : (UInt256.abs (EVM.wordOfInt j)).toNat = j.natAbs := by
      rw [u256_abs_high_toNat hhigh (by omega), hw]
      change 2 ^ 256 - (2 ^ 256 - j.natAbs) = j.natAbs
      omega
    have hc : Int.ofNat (UInt256.abs (EVM.wordOfInt j)).toNat = -j := by
      rw [ha]
      have hjabs := Int.eq_neg_natAbs_of_nonpos (le_of_lt hj)
      simpa only [neg_neg] using (congrArg (fun z : Int ↦ -z) hjabs).symm
    rw [sdiv_negative_denominator _ _ hhigh (by rw [ha]; exact hn),
      wordOfInt_sdiv_nat i _ hilo hihi (by rw [ha]; exact hn), hc, Int.tdiv_neg]
    rw [show (⟨0⟩ : UInt256) = EVM.wordOfInt 0 from rfl, ← wordOfInt_sub]
    simp only [Int.zero_sub, Int.neg_neg]
  · have hj0 : 0 ≤ j := by omega
    have hw : (EVM.wordOfInt j).toNat = j.toNat := by
      rw [wordOfInt_nonneg j hj0]
      exact ulit_toNat' _ (by change _ < 2 ^ 256; omega)
    have hd := wordOfInt_sdiv_nat i (EVM.wordOfInt j) hilo hihi (by rw [hw]; omega)
    rw [hw, show Int.ofNat j.toNat = j from Int.toNat_of_nonneg hj0] at hd
    exact hd

end Benchmarks.UniswapV3.Pool
