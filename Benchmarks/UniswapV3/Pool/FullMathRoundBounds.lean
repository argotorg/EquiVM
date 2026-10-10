import Benchmarks.UniswapV3.Pool.FullMathRoundSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem fullMathRoundResult_toNat {a b d : UInt256} (hv : fullMathRoundValid a b d) :
    (fullMathRoundResult a b d).toNat = fullMathProduct a b / d.toNat +
      if 0 < fullMathProduct a b % d.toNat then 1 else 0 := by
  classical
  unfold fullMathRoundResult
  split_ifs with hr
  · have hbound := hv.2 hr
    rw [fullMathResult_toNat hv.1] at hbound
    rw [uadd_toNat, fullMathResult_toNat hv.1]
    change (fullMathProduct a b / d.toNat + 1) % UInt256.size = _
    apply Nat.mod_eq_of_lt
    calc
      fullMathProduct a b / d.toNat + 1 < (UInt256.size - 1) + 1 :=
        Nat.add_lt_add_right hbound 1
      _ = UInt256.size := Nat.sub_add_cancel (by decide)
  · rw [fullMathResult_toNat hv.1, Nat.add_zero]

-- LIBRARY CANDIDATE: a nonzero remainder makes a bounded quotient strictly smaller.
theorem natDiv_lt_of_mod_pos {n d bound : Nat} (hd : 0 < d)
    (hn : n ≤ bound * d) (hr : 0 < n % d) : n / d < bound := by
  have hne : n ≠ bound * d := by
    intro he
    simpa only [he, Nat.mul_mod_left, Nat.lt_irrefl] using hr
  apply (Nat.div_lt_iff_lt_mul hd).mpr
  omega

-- LIBRARY CANDIDATE: an explicit product bound controls both FullMath variants.
theorem fullMathRoundValid_of_product_le (a b d : UInt256) (bound : Nat)
    (hd : 0 < d.toNat) (hb : bound < UInt256.size)
    (hp : fullMathProduct a b ≤ bound * d.toNat) : fullMathRoundValid a b d := by
  have hv : fullMathValid a b d := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < UInt256.size)).mpr
    exact lt_of_le_of_lt hp (by simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hb hd)
  refine ⟨hv, ?_⟩
  intro hr
  rw [fullMathResult_toNat hv]
  have hlt := natDiv_lt_of_mod_pos hd hp hr
  omega

theorem fullMathResult_le_bound (a b d : UInt256) (bound : Nat)
    (hd : 0 < d.toNat) (hb : bound < UInt256.size)
    (hp : fullMathProduct a b ≤ bound * d.toNat) : (fullMathResult a b d).toNat ≤ bound := by
  rw [fullMathResult_toNat (fullMathRoundValid_of_product_le a b d bound hd hb hp).1]
  have h := Nat.div_le_div_right (c := d.toNat) hp
  simpa only [Nat.mul_div_cancel _ hd] using h

theorem fullMathRoundResult_le_bound (a b d : UInt256) (bound : Nat)
    (hd : 0 < d.toNat) (hb : bound < UInt256.size)
    (hp : fullMathProduct a b ≤ bound * d.toNat) :
    (fullMathRoundResult a b d).toNat ≤ bound := by
  rw [fullMathRoundResult_toNat (fullMathRoundValid_of_product_le a b d bound hd hb hp)]
  split_ifs with hr
  · have hlt := natDiv_lt_of_mod_pos hd hp hr
    omega
  · rw [Nat.add_zero]
    have h := Nat.div_le_div_right (c := d.toNat) hp
    simpa only [Nat.mul_div_cancel _ hd] using h

end Benchmarks.UniswapV3.Pool
