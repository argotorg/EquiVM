import Benchmarks.UniswapV3.Pool.ProductLimbs
import Benchmarks.UniswapV3.Pool.DoubleWordArithmetic
import Benchmarks.UniswapV3.Pool.WordInverse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
open scoped Fin.IntCast Fin.CommRing

def fullMathAlgorithm (a b d : UInt256) : UInt256 :=
  let hi := productHigh a b
  let lo := UInt256.mul a b
  let rem := UInt256.mulMod a b d
  let twos := wordLowBit d
  let odd := UInt256.div d twos
  let flip := (⟨1⟩ : UInt256) + UInt256.div (UInt256.sub ⟨0⟩ twos) twos
  UInt256.mul (UInt256.lor (UInt256.div (UInt256.sub lo rem) twos)
    (UInt256.mul (UInt256.sub hi (UInt256.gt rem lo)) flip)) (wordInverse odd)

theorem fullMathAlgorithm_eq (a b d : UInt256) (hv : fullMathValid a b d) :
    fullMathAlgorithm a b d = fullMathResult a b d := by
  have hd := fullMath_denominator_pos hv
  obtain ⟨k, m, hk, hm, hfac, ht⟩ := wordLowBit_factor d hd
  have htwos : wordLowBit d = UInt256.ofNat (2 ^ k) := by
    apply u256_inj
    rw [ht, UInt256.toNat_ofNat_of_lt (pow_lt_size hk)]
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have hodd : (UInt256.div d (wordLowBit d)).toNat = m := by
    rw [udiv_toNat, ht, hfac, Nat.mul_div_right _ hp]
  have hrem : (UInt256.mulMod a b d).toNat = fullMathProduct a b % d.toNat :=
    mulMod_toNat a b d hd
  have hprod : (UInt256.mul a b).toNat + UInt256.size * (productHigh a b).toNat =
      fullMathProduct a b := by
    rw [productHigh_toNat, u256_mul_toNat]
    exact Nat.mod_add_div _ _
  have hpair := wordPair_sub (productHigh a b) (UInt256.mul a b) (UInt256.mulMod a b d)
    (by rw [hprod, hrem]; exact Nat.mod_le _ _)
  rw [hprod, hrem] at hpair
  have hjoin := wordPair_div_pow_two
    (UInt256.sub (productHigh a b) (UInt256.gt (UInt256.mulMod a b d) (UInt256.mul a b)))
    (UInt256.sub (UInt256.mul a b) (UInt256.mulMod a b d)) k hk
  rw [hpair] at hjoin
  have hdiff : fullMathProduct a b - fullMathProduct a b % d.toNat =
      d.toNat * (fullMathProduct a b / d.toNat) := by
    exact Nat.sub_eq_of_eq_add' (Nat.mod_add_div _ _).symm
  rw [hdiff, hfac, Nat.mul_assoc, Nat.mul_div_right _ hp] at hjoin
  rw [← hfac] at hjoin
  have hoddVal : (UInt256.div d (wordLowBit d)).val = (m : Fin UInt256.size) := by
    rw [← hodd]
    exact (Fin.cast_val_eq_self _).symm
  have hinv := congrArg UInt256.val (wordInverse_mul (UInt256.div d (wordLowBit d))
    (by rw [hodd]; exact hm))
  change (UInt256.div d (wordLowBit d)).val *
    (wordInverse (UInt256.div d (wordLowBit d))).val = 1 at hinv
  dsimp only [fullMathAlgorithm]
  rw [htwos, word_pow_two_flip k hk, hjoin]
  rw [← htwos]
  apply u256_inj
  change (((m * (fullMathProduct a b / d.toNat) : Nat) : Fin UInt256.size) *
    (wordInverse (UInt256.div d (wordLowBit d))).val).val = _
  rw [Nat.cast_mul, ← hoddVal]
  rw [mul_comm (UInt256.div d (wordLowBit d)).val
    (((fullMathProduct a b / d.toNat : Nat) : Fin UInt256.size)), mul_assoc, hinv, mul_one]
  rfl

theorem fullMath_small_eq (a b d : UInt256) (hv : fullMathValid a b d)
    (hh : productHigh a b = ⟨0⟩) :
    UInt256.div (UInt256.mul a b) d = fullMathResult a b d := by
  have hp : fullMathProduct a b < UInt256.size := by
    have hh' := productHigh_toNat a b
    rw [hh] at hh'
    have hq : fullMathProduct a b / UInt256.size < 1 := by
      rw [← hh']; decide
    simpa only [Nat.one_mul] using
      (Nat.div_lt_iff_lt_mul (by decide : 0 < UInt256.size)).mp hq
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat]
  change fullMathProduct a b % UInt256.size / d.toNat = _
  rw [Nat.mod_eq_of_lt hp, fullMathResult_toNat hv]

end Benchmarks.UniswapV3.Pool
