import Proofs.WExp.Eval

/-!
# `wExp` monotonicity at the spec level

The Stele counterpart of the `wExpIsMonotonicOnNegativeRange`,
`wExpIsMonotonicOnPositiveRangeWhenQStays`, and `wExpIsMonotonicOnPositiveRangeWhenQJumps`
rules from `certora/specs/TickToPrice.spec` (morpho midnight): for every pair of spec
executions of `wExp` on consecutive inputs in `[-maxInput, maxInput)`, the returned
`uint256` values are nondecreasing.
-/

open Stele ABI

namespace WExp

/-- Internal `wExp`: every pair of derivations on consecutive inputs returns nondecreasing
    values. -/
theorem wExp_step_spec {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x < MAXINPUT)
    {s0 s1 f0 f1 : Frame} {e0 e0' e1 e1' : EVM.State} {v0 v1 : List Value}
    (hx0 : s0.locals.get? "x" = some (.int x)) (hc0 : s0.contract = wexpContract)
    (hx1 : s1.locals.get? "x" = some (.int (x + 1))) (hc1 : s1.contract = wexpContract)
    (h0 : ExecFuncBody wexpConfig s0 e0 wExpFunction.body (.returned f0 e0' (some v0)))
    (h1 : ExecFuncBody wexpConfig s1 e1 wExpFunction.body (.returned f1 e1' (some v1))) :
    ∃ a b : Int, v0 = [.int a] ∧ v1 = [.int b] ∧ a ≤ b := by
  obtain ⟨_, _, r0⟩ := wExp_result hlo (by omega) hx0 hc0 h0
  obtain ⟨_, _, r1⟩ := wExp_result (by omega) (by omega) hx1 hc1 h1
  cases r0; cases r1
  exact ⟨_, _, rfl, rfl, specWExp_step hlo hhi⟩

/-- External `wExp` transition: same statement for the wrapper's body. -/
theorem wExpExternal_step_spec {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x < MAXINPUT)
    {s0 s1 f0 f1 : Frame} {e0 e0' e1 e1' : EVM.State} {v0 v1 : List Value}
    (hx0 : s0.locals.get? "x" = some (.int x)) (hc0 : s0.contract = wexpContract)
    (hx1 : s1.locals.get? "x" = some (.int (x + 1))) (hc1 : s1.contract = wexpContract)
    (h0 : ExecFuncBody wexpConfig s0 e0 wExpExternal.body (.returned f0 e0' (some v0)))
    (h1 : ExecFuncBody wexpConfig s1 e1 wExpExternal.body (.returned f1 e1' (some v1))) :
    ∃ a b : Int, v0 = [.int a] ∧ v1 = [.int b] ∧ a ≤ b := by
  obtain ⟨_, _, r0⟩ := wExpExternal_result hlo (by omega) hx0 hc0 h0
  obtain ⟨_, _, r1⟩ := wExpExternal_result (by omega) (by omega) hx1 hc1 h1
  cases r0; cases r1
  exact ⟨_, _, rfl, rfl, specWExp_step hlo hhi⟩

end WExp
