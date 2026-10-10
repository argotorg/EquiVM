import Benchmarks.UniswapV3.Pool.ModularWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: signed EVM division by a word in the nonnegative signed range.
theorem wordOfInt_sdiv_nat (i : Int) (denominator : UInt256)
    (hlo : -(2 ^ 255 : Int) ≤ i) (hhi : i < (2 ^ 255 : Int))
    (hd : denominator.toNat < 2 ^ 255) :
    UInt256.sdiv (EVM.wordOfInt i) denominator =
      EVM.wordOfInt (i.tdiv (Int.ofNat denominator.toNat)) := by
  by_cases hneg : i < 0
  · have hi : i = -(Int.ofNat i.natAbs) := Int.eq_neg_natAbs_of_nonpos (le_of_lt hneg)
    have hn : i.natAbs ≤ 2 ^ 255 := by omega
    have hnpos : 0 < i.natAbs := by omega
    have hw := wordOfInt_toNat_of_neg_of_abs_lt i hneg
      (show i.natAbs < EVM.wordModulus by change _ < 2 ^ 256; omega)
    have hhigh : 2 ^ 255 ≤ (EVM.wordOfInt i).toNat := by
      rw [hw]
      change 2 ^ 255 ≤ 2 ^ 256 - i.natAbs
      omega
    have ha : (UInt256.abs (EVM.wordOfInt i)).toNat = i.natAbs := by
      rw [u256_abs_high_toNat hhigh (by omega), hw]
      change 2 ^ 256 - (2 ^ 256 - i.natAbs) = i.natAbs
      omega
    let q := UInt256.div (UInt256.abs (EVM.wordOfInt i)) denominator
    have hq : q.toNat = i.natAbs / denominator.toNat := by
      dsimp only [q]
      rw [udiv_toNat, ha]
    have hqbound : q.toNat ≤ 2 ^ 255 := by rw [hq]; exact le_trans (Nat.div_le_self _ _) hn
    have hr : EVM.wordOfInt (i.tdiv (Int.ofNat denominator.toNat)) = UInt256.sub ⟨0⟩ q := by
      have hdiv : (Int.ofNat i.natAbs).tdiv (Int.ofNat denominator.toNat) =
          Int.ofNat (i.natAbs / denominator.toNat) := rfl
      conv_lhs => rw [hi, Int.neg_tdiv, hdiv]
      rw [← hq]
      exact wordOfInt_neg_natCast_eq_sub_zero_of_le_sign q hqbound
    rw [u256_sdiv_high_low hhigh hd, hr]
    change ({ val := q.val * (-1 : Fin UInt256.size) } : UInt256) = UInt256.sub ⟨0⟩ q
    simp [UInt256.sub]
  · have hi : i = Int.ofNat i.toNat := (Int.toNat_of_nonneg (by omega)).symm
    have hn : i.toNat < 2 ^ 255 := by omega
    have hw : (UInt256.ofNat i.toNat).toNat = i.toNat :=
      ulit_toNat' _ (by change _ < 2 ^ 256; omega)
    rw [hi, wordOfInt_ofNat_toNat_gen]
    unfold UInt256.sdiv
    rw [if_neg (by rw [hw]; omega), if_neg (by omega)]
    change UInt256.div (UInt256.ofNat i.toNat) denominator =
      EVM.wordOfInt (Int.ofNat (i.toNat / denominator.toNat))
    rw [wordOfInt_ofNat_toNat_gen]
    apply u256_inj
    rw [udiv_toNat, hw, ulit_toNat' _ (by
      have hq := Nat.div_le_self i.toNat denominator.toNat
      change _ < 2 ^ 256
      omega)]

end Benchmarks.UniswapV3.Pool
