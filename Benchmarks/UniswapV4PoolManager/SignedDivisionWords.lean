import Benchmarks.UniswapV4PoolManager.SignedArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: express a negative word using its unsigned absolute value.
theorem signed_eq_neg_abs {w : UInt256} (h : 2^255 ≤ w.toNat) :
    EVM.signed w = -Int.ofNat (UInt256.abs w).toNat := by
  rw [u256_abs_high_toNat h (by omega)]
  have hw := w.val.isLt
  change w.toNat < 2^256 at hw
  change (if w.toNat < 2^255 then Int.ofNat w.toNat else Int.ofNat w.toNat-Int.ofNat (2^256)) = _
  rw [if_neg (by omega)]
  change _ = -Int.ofNat (2^256-w.toNat)
  simp only [Int.ofNat_eq_natCast]
  omega

-- LIBRARY CANDIDATE: signed EVM division encodes truncation toward zero, including overflow.
theorem sdiv_signed (a b : UInt256) :
    UInt256.sdiv a b = EVM.wordOfInt ((EVM.signed a).tdiv (EVM.signed b)) := by
  have hlow (w : UInt256) (hw : ¬2^255 ≤ w.toNat) : EVM.signed w = Int.ofNat w.toNat := by
    change (if w.toNat < 2^255 then _ else _) = _
    rw [if_pos (by omega)]
    rfl
  have hneg (w : UInt256) : ({val := w.val * (-1)} : UInt256) = UInt256.sub ⟨0⟩ w := by
    simp only [UInt256.sub, mul_neg_one, zero_sub]
  have hdiv (x y : Nat) : (Int.ofNat x).tdiv (Int.ofNat y) = Int.ofNat (x/y) := rfl
  unfold UInt256.sdiv
  by_cases ha : 2^255 ≤ a.toNat
  · rw [if_pos ha, signed_eq_neg_abs ha]
    by_cases hb : 2^255 ≤ b.toNat
    · rw [if_pos hb, signed_eq_neg_abs hb, Int.neg_tdiv_neg, hdiv,
        ← udiv_toNat, wordOfInt_ofNat_toNat]
      rfl
    · rw [if_neg hb, hlow b hb, Int.neg_tdiv, hdiv,
        ← udiv_toNat, wordOfInt_neg_natCast_eq_sub_zero, hneg]
      rfl
  · rw [if_neg ha, hlow a ha]
    by_cases hb : 2^255 ≤ b.toNat
    · rw [if_pos hb, signed_eq_neg_abs hb, Int.tdiv_neg, hdiv,
        ← udiv_toNat, wordOfInt_neg_natCast_eq_sub_zero, hneg]
      rfl
    · rw [if_neg hb, hlow b hb, hdiv, ← udiv_toNat, wordOfInt_ofNat_toNat]
      rfl

end Benchmarks.UniswapV4PoolManager
