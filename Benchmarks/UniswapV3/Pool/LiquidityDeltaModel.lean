import Benchmarks.UniswapV3.Pool.ModularWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: eliminate an intermediate normalization on a subtrahend.
theorem normalizeInt_sub_right (ty : ABI.IntType) (i j : Int) :
    normalizeInt ty (i - normalizeInt ty j) = normalizeInt ty (i - j) := by
  have hr : (i - normalizeInt ty j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) =
      (i - j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) := by
    rw [Int.sub_emod, normalizeInt_residue, ← Int.sub_emod]
  cases ty with
  | uint width => exact hr
  | sint width => simp only [normalizeInt, IntType.bitWidth] at hr ⊢; rw [hr]

-- LIBRARY CANDIDATE: equal-width signed casts preserve the unsigned residue.
theorem normalizeUInt_sint (width : ABI.BitWidth) (i : Int) :
    normalizeInt (.uint width) (normalizeInt (.sint width) i) =
      normalizeInt (.uint width) i := normalizeInt_residue (.sint width) i

def liquidityDeltaResult (x y : Int) : Int := normalizeInt (.uint ⟨128, by decide⟩) (x + y)

def liquidityDeltaValid (x y : Int) : Prop :=
  if y < 0 then liquidityDeltaResult x y < x else x ≤ liquidityDeltaResult x y

theorem liquidityDeltaSubtract (x y : Int) :
    normalizeInt (.uint ⟨128, by decide⟩)
      (x - normalizeInt (.uint ⟨128, by decide⟩)
        (normalizeInt (.sint ⟨128, by decide⟩) (0 - y))) = liquidityDeltaResult x y := by
  rw [normalizeUInt_sint, normalizeInt_sub_right, zero_sub, sub_neg_eq_add]
  rfl

theorem liquidityDeltaAdd (x y : Int) :
    normalizeInt (.uint ⟨128, by decide⟩)
      (x + normalizeInt (.uint ⟨128, by decide⟩) y) = liquidityDeltaResult x y :=
  normalizeInt_add_right (.uint ⟨128, by decide⟩) x y

theorem liquidityDeltaResult_bounds (x y : Int) :
    0 ≤ liquidityDeltaResult x y ∧ liquidityDeltaResult x y < 2 ^ 128 := by
  change 0 ≤ (x + y) % (2 ^ 128 : Int) ∧ (x + y) % (2 ^ 128 : Int) < 2 ^ 128
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem liquidityDeltaValid_iff (x y : Int)
    (hxlo : 0 ≤ x) (hxhi : x < 2 ^ 128)
    (hylo : -(2 ^ 127 : Int) ≤ y) (hyhi : y < 2 ^ 127) :
    liquidityDeltaValid x y ↔ 0 ≤ x + y ∧ x + y < 2 ^ 128 := by
  unfold liquidityDeltaValid liquidityDeltaResult
  change (if y < 0 then (x + y) % (2 ^ 128 : Int) < x
    else x ≤ (x + y) % (2 ^ 128 : Int)) ↔ _
  split <;> omega

theorem liquidityDeltaResult_of_valid (x y : Int)
    (hxlo : 0 ≤ x) (hxhi : x < 2 ^ 128)
    (hylo : -(2 ^ 127 : Int) ≤ y) (hyhi : y < 2 ^ 127)
    (hv : liquidityDeltaValid x y) : liquidityDeltaResult x y = x + y := by
  obtain ⟨hlo, hhi⟩ := (liquidityDeltaValid_iff x y hxlo hxhi hylo hyhi).mp hv
  exact normalizeInt_uint_eq_self ⟨128, by decide⟩ _ hlo hhi

end Benchmarks.UniswapV3.Pool
