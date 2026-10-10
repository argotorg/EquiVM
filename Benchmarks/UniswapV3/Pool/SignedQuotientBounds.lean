import Benchmarks.UniswapV3.Pool.SignedDivisionGeneral

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a non-exact signed division leaves room to decrement its quotient.
theorem tdiv_sub_one_bounds_of_tmod_ne_zero {a b : Int} {bound : Nat}
    (hbound : 0 < bound) (ha : a.natAbs ≤ bound) (hb : b ≠ 0) (hr : a.tmod b ≠ 0) :
    -(bound : Int) ≤ a.tdiv b - 1 ∧ a.tdiv b - 1 < (bound : Int) := by
  have hrem : a.natAbs % b.natAbs ≠ 0 := by
    intro he
    apply hr
    apply Int.natAbs_eq_zero.mp
    rwa [Int.natAbs_tmod]
  have hden : 2 ≤ b.natAbs := by
    have hn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
    by_contra h
    have he : b.natAbs = 1 := by omega
    simp only [he, Nat.mod_one] at hrem
    exact hrem rfl
  have hquot : (a.tdiv b).natAbs < bound := by
    rw [Int.natAbs_tdiv]
    apply (Nat.div_lt_iff_lt_mul (show 0 < b.natAbs by omega)).mpr
    nlinarith
  omega

end Benchmarks.UniswapV3.Pool
