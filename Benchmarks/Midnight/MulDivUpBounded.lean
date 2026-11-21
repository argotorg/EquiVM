import Benchmarks.Midnight.MulDiv
import Benchmarks.Midnight.WordMin

/-! Bounds for rounded-up proportions of packed uint128 balances. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the minimum is bounded by either operand.
theorem wordMin_le_right (x y : UInt256) : (wordMin x y).toNat ≤ y.toNat := by
  unfold wordMin
  split <;> omega

-- LIBRARY CANDIDATE: a proportion at most one cannot overflow packed uint128 arithmetic.
theorem mulDivUpSafe_uint128 {x y d : UInt256}
    (hx : x.toNat < 2^128) (hd : d.toNat < 2^128)
    (hy : y.toNat ≤ d.toNat) (hp : 0 < d.toNat) : MulDivUpSafe x y d := by
  have hb : x.toNat * y.toNat ≤ (2^128 - 1) * (2^128 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hfit : x.toNat * y.toNat < UInt256.size := by change _ < 2^256; omega
  refine ⟨hfit, hp, ?_⟩
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit, usub_toNat (a := d) (b := ⟨1⟩) hp]
  change x.toNat * y.toNat + (d.toNat - 1) < 2^256
  omega

-- LIBRARY CANDIDATE: rounding a proportion upward still cannot exceed the whole balance.
theorem mulDivUp_le_left {x y d : UInt256}
    (hs : MulDivUpSafe x y d) (hy : y.toNat ≤ d.toNat) :
    (mulDivUp x y d).toNat ≤ x.toNat := by
  have hprod : (UInt256.mul x y).toNat = x.toNat * y.toNat :=
    umul_toNat x y hs.1
  have hadd : (UInt256.mul x y + UInt256.sub d ⟨1⟩).toNat =
      (UInt256.mul x y).toNat + (UInt256.sub d ⟨1⟩).toNat := addWord_toNat _ _ hs.2.2
  rw [mulDivUp, udiv_toNat, hadd, hprod, usub_toNat (a := d) (b := ⟨1⟩) hs.2.1]
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hs.2.1).mpr
  have hmul := Nat.mul_le_mul_left x.toNat hy
  rw [Nat.succ_mul]
  change x.toNat * y.toNat + (d.toNat - 1) < x.toNat * d.toNat + d.toNat
  have hp := hs.2.1
  omega

end Benchmarks.Midnight
