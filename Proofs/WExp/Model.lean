import Examples.WExp.Spec

/-!
# The `wExp` model and its monotonicity

`wExpPos`/`wExp` model `TickLib.wExp` exactly (`Int.tdiv` for Solidity `/`; the `<<` shift as
multiplication by `2^q`). `specWExpPos`/`specWExp` are the spec-level models: identical but the
shift's result is normalized into `uint256`, as `.shl` does in the Stele semantics — they agree
with the unbounded model on the `[-maxInput, maxInput]` range, which is exactly the range the
Certora rules assume.

Theorems below mirror the rules of `certora/specs/TickToPrice.spec` (morpho midnight):
`qIncreasesByZeroOrOne` (`qOf_step`), `expRIsMonotonicWithinSegment` (`poly_step`),
`wExpIsMonotonicOnPositiveRangeWhenQStays`/`WhenQJumps` (`wExpPos_step`),
`wExpIsMonotonicOnNegativeRange` (`wExp_step_neg`).
-/

open Stele

namespace WExp

def LN2 : Int := 693147180559945309
def OFFSET : Int := 322611214989459870
def WAD : Int := 10 ^ 18
def MAXINPUT : Int := 4987541511039073 * 3372  -- LN_ONE_PLUS_DELTA * (MAX_TICK/2)

/-- The Taylor polynomial `1e18 + r + r²/2e18 + (r²/2e18)·r/3e18` as a function of `r`. -/
def poly (r : Int) : Int :=
  let s := (r * r).tdiv (2 * WAD)
  WAD + r + s + (s * r).tdiv (3 * WAD)

/-- `wExp` on the non-negative branch, without the uint256 wrap (shift as multiply by 2^q).
    On the input range used (`x ≤ maxInput`) the result is `< 2^256`, so wrap never triggers. -/
def wExpPos (x : Int) : Int :=
  let q := (x + OFFSET).tdiv LN2
  let r := x - q * LN2
  let secondTerm := (r * r).tdiv (2 * WAD)
  let thirdTerm := (secondTerm * r).tdiv (3 * WAD)
  let e := WAD + r + secondTerm + thirdTerm
  e * 2 ^ q.toNat

def wExp (x : Int) : Int :=
  if x < 0 then (10 ^ 36 : Int).tdiv (wExpPos (-x)) else wExpPos x

def qOf (x : Int) : Int := (x + OFFSET).tdiv LN2
def rOf (x : Int) : Int := x - qOf x * LN2

theorem wExpPos_eq (x : Int) : wExpPos x = poly (rOf x) * 2 ^ (qOf x).toNat := rfl

-- sanity checks

theorem qOf_eq (x : Int) (hx : 0 ≤ x) : qOf x = (x + OFFSET) / LN2 := by
  unfold qOf; rw [Int.tdiv_eq_ediv_of_nonneg (by unfold OFFSET; omega)]

theorem qOf_nonneg {x : Int} (hx : 0 ≤ x) : 0 ≤ qOf x := by
  rw [qOf_eq x hx]
  exact Int.ediv_nonneg (by unfold OFFSET; omega) (by unfold LN2; omega)

/-- Remainder decomposition: `x + OFFSET = qOf x * LN2 + rOf x + OFFSET`,
    with `rOf x + OFFSET = (x+OFFSET) % LN2 ∈ [0, LN2)`. -/
theorem rOf_eq {x : Int} (hx : 0 ≤ x) : rOf x = (x + OFFSET) % LN2 - OFFSET := by
  unfold rOf; rw [qOf_eq x hx]
  have h := Int.mul_ediv_add_emod (x + OFFSET) LN2
  unfold LN2 at h ⊢; omega

theorem rOf_bounds {x : Int} (hx : 0 ≤ x) : -OFFSET ≤ rOf x ∧ rOf x < LN2 - OFFSET := by
  rw [rOf_eq hx]
  have h0 := Int.emod_nonneg (x + OFFSET) (b := LN2) (by unfold LN2; omega)
  have h1 := Int.emod_lt_of_pos (x + OFFSET) (b := LN2) (by decide)
  unfold LN2 OFFSET at *; omega

/-- `qIncreasesByZeroOrOne` -/
theorem qOf_step {x : Int} (hx : 0 ≤ x) : qOf (x + 1) = qOf x ∨ qOf (x + 1) = qOf x + 1 := by
  have h0 := Int.mul_ediv_add_emod (x + OFFSET) LN2
  have h1 := Int.mul_ediv_add_emod (x + 1 + OFFSET) LN2
  have hm0 := Int.emod_nonneg (x + OFFSET) (b := LN2) (by unfold LN2; omega)
  have hm1 := Int.emod_nonneg (x + 1 + OFFSET) (b := LN2) (by unfold LN2; omega)
  have hl0 := Int.emod_lt_of_pos (x + OFFSET) (b := LN2) (by decide)
  have hl1 := Int.emod_lt_of_pos (x + 1 + OFFSET) (b := LN2) (by decide)
  rw [qOf_eq x hx, qOf_eq (x + 1) (by omega)]
  unfold LN2 OFFSET at *; omega

/-- At a `q` jump the input is pinned: `x + OFFSET + 1 = (q+1)*LN2`, so `r` wraps from
    `LN2 - OFFSET - 1` down to `-OFFSET`. -/
theorem qOf_jump {x : Int} (hx : 0 ≤ x) (hj : qOf (x + 1) = qOf x + 1) :
    rOf x = LN2 - OFFSET - 1 ∧ rOf (x + 1) = -OFFSET := by
  have h0 := Int.mul_ediv_add_emod (x + OFFSET) LN2
  have h1 := Int.mul_ediv_add_emod (x + 1 + OFFSET) LN2
  have hm0 := Int.emod_nonneg (x + OFFSET) (b := LN2) (by unfold LN2; omega)
  have hm1 := Int.emod_nonneg (x + 1 + OFFSET) (b := LN2) (by unfold LN2; omega)
  have hl0 := Int.emod_lt_of_pos (x + OFFSET) (b := LN2) (by decide)
  have hl1 := Int.emod_lt_of_pos (x + 1 + OFFSET) (b := LN2) (by decide)
  rw [qOf_eq x hx, qOf_eq (x + 1) (by omega)] at hj
  rw [rOf_eq hx, rOf_eq (by omega : 0 ≤ x + 1)]
  unfold LN2 OFFSET at *; omega


theorem mul_self_nonneg' (r : Int) : 0 ≤ r * r := by
  rcases Int.lt_or_le r 0 with h | h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (Int.le_of_lt h) (Int.le_of_lt h)
  · exact Int.mul_nonneg h h

/-- For a literal denominator, the floor-division gap between two numerators
    differing by less than `d` is at most 1. (Stated for `2·10^18` — the only
    denominator this is used with — so `omega` sees a literal coefficient.) -/
theorem ediv_gap_le_one {a b : Int} {d : Int} (hd : d = 2 * WAD)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (h : a - b < d) : a / d ≤ b / d + 1 := by
  have hd' : d = 2000000000000000000 := by rw [hd]; unfold WAD; decide
  subst hd'
  have h1 := Int.mul_ediv_add_emod a 2000000000000000000
  have h2 := Int.mul_ediv_add_emod b 2000000000000000000
  have hm1 := Int.emod_nonneg a (b := 2000000000000000000) (by decide)
  have hm2 := Int.emod_nonneg b (b := 2000000000000000000) (by decide)
  have ht1 := Int.emod_lt_of_pos a (b := 2000000000000000000) (by decide)
  have ht2 := Int.emod_lt_of_pos b (b := 2000000000000000000) (by decide)
  omega

/-- `sOf r = (r²).tdiv (2*WAD)` — second Taylor term. -/
def sOf (r : Int) : Int := (r * r).tdiv (2 * WAD)
/-- `tOf r = (sOf r · r).tdiv (3*WAD)` — third Taylor term. -/
def tOf (r : Int) : Int := (sOf r * r).tdiv (3 * WAD)

theorem poly_eq (r : Int) : poly r = WAD + r + sOf r + tOf r := rfl

theorem sOf_nonneg (r : Int) : 0 ≤ sOf r :=
  Int.tdiv_nonneg (mul_self_nonneg' r) (by unfold WAD; decide)

/-- For `r ≥ 0` both extra terms are nondecreasing. -/
theorem sOf_mono_nonneg {r : Int} (hr : 0 ≤ r) : sOf r ≤ sOf (r + 1) := by
  unfold sOf
  rw [Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg' r),
      Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg' (r + 1))]
  apply Int.ediv_le_ediv (c := 2 * WAD) (by unfold WAD; decide)
  have : (r + 1) * (r + 1) - r * r = 2 * r + 1 := by grind
  omega

theorem tOf_mono_nonneg {r : Int} (hr : 0 ≤ r) : tOf r ≤ tOf (r + 1) := by
  unfold tOf
  rw [Int.tdiv_eq_ediv_of_nonneg (Int.mul_nonneg (sOf_nonneg r) hr),
      Int.tdiv_eq_ediv_of_nonneg (Int.mul_nonneg (sOf_nonneg (r + 1)) (by omega))]
  apply Int.ediv_le_ediv (c := 3 * WAD) (by unfold WAD; decide)
  have hs := sOf_mono_nonneg hr
  have : sOf (r + 1) * (r + 1) - sOf r * r = r * (sOf (r + 1) - sOf r) + sOf (r + 1) := by grind
  have h1 : 0 ≤ r * (sOf (r + 1) - sOf r) := Int.mul_nonneg hr (by omega)
  have h2 : 0 ≤ sOf (r + 1) := sOf_nonneg _
  omega

/-- For `r < 0`, `sOf` can drop by at most 1 (|2r+1| < 2·10^18 while |r| ≤ OFFSET). -/
theorem sOf_step_neg {r : Int} (hlo : -OFFSET ≤ r) (hr : r < 0) :
    sOf r ≤ sOf (r + 1) + 1 := by
  unfold sOf
  rw [Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg' r),
      Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg' (r + 1))]
  apply ediv_gap_le_one rfl (mul_self_nonneg' r) (mul_self_nonneg' (r + 1))
  have : r * r - (r + 1) * (r + 1) = -(2 * r + 1) := by grind
  unfold WAD OFFSET at *; omega

/-- For `r ≤ -1`, `tOf` is nondecreasing (the numerator's magnitude shrinks). -/
theorem tOf_step_neg {r : Int} (_hlo : -OFFSET ≤ r) (hr : r ≤ -1) :
    tOf r ≤ tOf (r + 1) := by
  unfold tOf
  have hnegr : sOf r * r = -(sOf r * -r) := by grind
  have hnegr1 : sOf (r + 1) * (r + 1) = -(sOf (r + 1) * -(r + 1)) := by grind
  rw [hnegr, hnegr1, Int.neg_tdiv, Int.neg_tdiv]
  have hss : sOf (r + 1) ≤ sOf r := by
    unfold sOf
    rw [Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg' (r + 1)),
        Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg' r)]
    apply Int.ediv_le_ediv (c := 2 * WAD) (by unfold WAD; decide)
    have : (r + 1) * (r + 1) - r * r = 2 * r + 1 := by grind
    omega
  have hm : sOf (r + 1) * -(r + 1) ≤ sOf r * -r := by
    have h1 : sOf (r + 1) * -(r + 1) ≤ sOf (r + 1) * -r :=
      Int.mul_le_mul_of_nonneg_left (by omega) (sOf_nonneg _)
    have h2 : sOf (r + 1) * -r ≤ sOf r * -r :=
      Int.mul_le_mul_of_nonneg_right hss (by omega)
    omega
  rw [Int.tdiv_eq_ediv_of_nonneg (Int.mul_nonneg (sOf_nonneg _) (by omega)),
      Int.tdiv_eq_ediv_of_nonneg (Int.mul_nonneg (sOf_nonneg _) (by omega))]
  have := Int.ediv_le_ediv (c := 3 * WAD) (by unfold WAD; decide) hm
  omega

/-- `expRIsMonotonicWithinSegment`: `poly` steps up throughout `[-OFFSET, LN2-OFFSET)`.
    (For `r ≥ 0` it is increasing everywhere; `-OFFSET ≤ r` is only needed for `r < 0`.) -/
theorem poly_step {r : Int} (hlo : -OFFSET ≤ r) : poly r ≤ poly (r + 1) := by
  rw [poly_eq, poly_eq]
  rcases Int.lt_or_le r 0 with hr | hr
  · have hs := sOf_step_neg hlo hr
    have ht := tOf_step_neg hlo (by omega)
    unfold WAD; omega
  · have hs := sOf_mono_nonneg hr
    have ht := tOf_mono_nonneg hr
    unfold WAD; omega


/-- `wExpIsMonotonicOnPositiveRangeWhenQStays` ∪ `WhenQJumps`: the step lemma
    on the non-negative range. -/
theorem wExpPos_step {x : Int} (hx : 0 ≤ x) : wExpPos x ≤ wExpPos (x + 1) := by
  rw [wExpPos_eq, wExpPos_eq]
  rcases qOf_step hx with hq | hq
  · -- q stays: same shift, r increases by 1, poly is nondecreasing
    have hr : rOf (x + 1) = rOf x + 1 := by
      unfold rOf; rw [hq]; grind
    rw [hr, hq]
    exact Int.mul_le_mul_of_nonneg_right (poly_step (rOf_bounds hx).1)
      (Int.pow_nonneg (n := 2) (by decide))
  · -- q jumps: r is pinned to the segment boundary, where the offset makes
    -- 2·poly(-OFFSET) = poly(LN2-OFFSET-1), so the extra shift exactly covers the drop.
    obtain ⟨hr0, hr1⟩ := qOf_jump hx hq
    rw [hr0, hr1, hq]
    have hq0 : 0 ≤ qOf x := qOf_nonneg hx
    have h2 : (2 : Int) ^ (qOf x + 1).toNat = 2 * 2 ^ (qOf x).toNat := by
      have ht : (qOf x + 1).toNat = (qOf x).toNat + 1 := by
        rw [Int.toNat_add hq0 (by decide)]; omega
      rw [ht, Int.pow_succ']
    rw [h2]
    have hbound : poly (LN2 - OFFSET - 1) ≤ 2 * poly (-OFFSET) := by native_decide
    have h3 : (2 * poly (-OFFSET)) * 2 ^ (qOf x).toNat =
        poly (-OFFSET) * (2 * 2 ^ (qOf x).toNat) := by grind
    calc poly (LN2 - OFFSET - 1) * 2 ^ (qOf x).toNat
        ≤ (2 * poly (-OFFSET)) * 2 ^ (qOf x).toNat :=
          Int.mul_le_mul_of_nonneg_right hbound (Int.pow_nonneg (n := 2) (by decide))
      _ = poly (-OFFSET) * (2 * 2 ^ (qOf x).toNat) := h3

/-- General (non-step) monotonicity on the non-negative range, by chaining steps. -/
theorem wExpPos_mono {x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) : wExpPos x ≤ wExpPos y := by
  have key : ∀ d : Nat, x + d ≤ y → wExpPos x ≤ wExpPos (x + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 : wExpPos x ≤ wExpPos (x + k) := ih (by omega)
      have h2 : wExpPos (x + k) ≤ wExpPos (x + k + 1) := wExpPos_step (by omega)
      have : (x : Int) + (k + 1 : Nat) = x + k + 1 := by grind
      rw [this]
      exact Int.le_trans h1 h2
  have e : (x : Int) + ((y - x).toNat : Nat) = y := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hle := key ((y - x).toNat) (Int.le_of_eq e)
  rwa [e] at hle

/-- `poly` stays positive on its whole segment (poly(-OFFSET) ≈ 7.2e17 is its minimum). -/
theorem poly_pos {r : Int} (hlo : -OFFSET ≤ r) : 0 < poly r := by
  have key : ∀ d : Nat, -OFFSET + d ≤ r → poly (-OFFSET) ≤ poly (-OFFSET + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := poly_step (r := -OFFSET + k) (by omega)
      have : (-OFFSET : Int) + (k + 1 : Nat) = -OFFSET + k + 1 := by grind
      rw [this]
      exact Int.le_trans h1 h2
  have e : (-OFFSET : Int) + ((r + OFFSET).toNat : Nat) = r := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hmin : (0 : Int) < poly (-OFFSET) := by native_decide
  have hle := key ((r + OFFSET).toNat) (Int.le_of_eq e)
  rw [e] at hle
  omega

theorem wExpPos_pos {y : Int} (hy : 0 ≤ y) : 0 < wExpPos y := by
  rw [wExpPos_eq]
  have hpp := poly_pos (rOf_bounds hy).1
  have h2p : (1 : Int) ≤ 2 ^ (qOf y).toNat := by
    have hp : (0 : Int) < 2 ^ (qOf y).toNat := Int.pow_pos (n := 2) (by decide)
    omega
  calc (0 : Int) < poly (rOf y) * 1 := by grind
    _ ≤ poly (rOf y) * 2 ^ (qOf y).toNat :=
        Int.mul_le_mul_of_nonneg_left h2p (Int.le_of_lt hpp)

/-- `N / d` is antitone in the denominator `d > 0` (for `N ≥ 0`). -/
theorem ediv_denom_antitone {N d1 d2 : Int} (hN : 0 ≤ N) (h1 : 0 < d1) (h12 : d1 ≤ d2) :
    N / d2 ≤ N / d1 := by
  have h2 : 0 < d2 := by omega
  have hdecomp := Int.mul_ediv_add_emod N d2
  have hm := Int.emod_nonneg N (b := d2) (by omega)
  have hle : N / d2 * d1 ≤ N / d2 * d2 :=
    Int.mul_le_mul_of_nonneg_left h12 (Int.ediv_nonneg hN (Int.le_of_lt h2))
  have hN2 : N / d2 * d2 ≤ N := by grind
  exact (Int.le_ediv_iff_mul_le h1).2 (by omega)

/-- `wExpIsMonotonicOnNegativeRange`. -/
theorem wExp_step_neg {x : Int} (hx : x < 0) : wExp x ≤ wExp (x + 1) := by
  unfold wExp
  by_cases hx1 : x + 1 < 0
  · rw [if_pos hx, if_pos hx1, show -(x + 1) = -x - 1 from by omega]
    have hle : wExpPos (-x - 1) ≤ wExpPos (-x) := wExpPos_mono (by omega) (by omega)
    have hp : 0 < wExpPos (-x - 1) := wExpPos_pos (by omega)
    rw [Int.tdiv_eq_ediv_of_nonneg (by decide : (0 : Int) ≤ 10 ^ 36),
        Int.tdiv_eq_ediv_of_nonneg (by decide : (0 : Int) ≤ 10 ^ 36)]
    exact ediv_denom_antitone (by decide) hp hle
  · -- boundary: x = -1, compare with wExp(0) = 1e18
    have hx0 : x = -1 := by omega
    rw [if_pos hx, if_neg (by omega : ¬(x + 1 < 0)), hx0]
    have hw1 : wExpPos (-(-1 : Int)) = 1000000000000000001 := by native_decide
    have hw0 : wExpPos (-1 + 1) = 1000000000000000000 := by native_decide
    rw [hw1, hw0]
    native_decide

/-- Full statement: `wExp` is nondecreasing on consecutive inputs everywhere
    (matching the three Certora monotonicity rules combined). -/
theorem wExp_step (x : Int) : wExp x ≤ wExp (x + 1) := by
  rcases Int.lt_or_le x 0 with h | h
  · exact wExp_step_neg h
  · unfold wExp
    rw [if_neg (by omega : ¬x < 0), if_neg (by omega : ¬(x + 1) < 0)]
    exact wExpPos_step h
/-- `maxOutput` from the spec. -/
def MAXOUTPUT : Int := 20134595243400876315901952

/-- The spec-level model of the non-negative branch: the `<<` shift wraps into `uint256`. -/
def specWExpPos (x : Int) : Int := Stele.normalizeInt (.uint ⟨256, by decide⟩) (wExpPos x)

/-- The spec-level model of `wExp`: `.div` is `Int.ediv`, agreeing with `uint256` division
    on the non-negative operands here. -/
def specWExp (x : Int) : Int := if x < 0 then (10 ^ 36 : Int) / specWExpPos (-x) else specWExpPos x

theorem wExpPos_maxInput : wExpPos MAXINPUT = MAXOUTPUT := by native_decide

theorem wExpPos_bound {x : Int} (hx : 0 ≤ x) (hxm : x ≤ MAXINPUT) :
    0 < wExpPos x ∧ wExpPos x ≤ MAXOUTPUT := by
  have h0 : wExpPos 0 = 1000000000000000000 := by native_decide
  have hm : wExpPos x ≤ wExpPos MAXINPUT := wExpPos_mono hx hxm
  have hm0 : wExpPos 0 ≤ wExpPos x := wExpPos_mono (Int.le_refl 0) hx
  rw [wExpPos_maxInput] at hm; rw [h0] at hm0; omega

/-- On `[0, MAXINPUT]` the spec's `uint256` wrap never triggers: the model and the
    spec-level model agree. -/
theorem specWExpPos_eq {x : Int} (hx : 0 ≤ x) (hxm : x ≤ MAXINPUT) :
    specWExpPos x = wExpPos x := by
  unfold specWExpPos
  apply Stele.normalizeInt_uint_eq_self
  · exact Int.le_of_lt (wExpPos_bound hx hxm).1
  · have hb := (wExpPos_bound hx hxm).2
    show wExpPos x < Int.ofNat (EVM.twoPow 256)
    have h2 : (Int.ofNat (EVM.twoPow 256) : Int) =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      native_decide
    unfold MAXOUTPUT at hb; omega

theorem specWExpPos_pos {x : Int} (hx : 0 ≤ x) (hxm : x ≤ MAXINPUT) :
    0 < specWExpPos x := specWExpPos_eq hx hxm ▸ wExpPos_pos hx

/-- On `[-MAXINPUT, MAXINPUT]` the spec-level model and the unbounded model agree. -/
theorem specWExp_eq_wExp {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT) :
    specWExp x = wExp x := by
  unfold specWExp wExp
  by_cases hx : x < 0
  · rw [if_pos hx, if_pos hx, specWExpPos_eq (by omega) (by omega),
        Int.tdiv_eq_ediv_of_nonneg (by decide)]
  · rw [if_neg hx, if_neg hx, specWExpPos_eq (by omega) hhi]

/-- Spec-level `wExp` monotonicity on the Certora range `[-maxInput, maxInput)`. -/
theorem specWExp_step {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x < MAXINPUT) :
    specWExp x ≤ specWExp (x + 1) := by
  rw [specWExp_eq_wExp hlo (by omega), specWExp_eq_wExp (by omega) hhi]
  exact wExp_step x

end WExp
