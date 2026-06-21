import Examples.Reuse.Bytecode
import Examples.Reuse.Spec
import Solm.Equiv

/-!
# Reuse — correctness statement (proof TODO)

The deployed (optimizer-on) runtime bytecode of `C` refines its Solm spec (`Reuse.cContract`) under
`cConfig`.  This file states the theorem only.

The point of this example is the **internal-call reuse** scenario: `f` is a public function (its own
external ABI entry) that `g` calls internally.  solc emits `f`'s body once as a shared routine, so
the proof should introduce a single `RD`-routine lemma for that body and apply it at *both* the
external-entry refinement (`f`) and the internal-call refinement (inside `g`) — without re-unfolding
`f`'s body.  See `C.sol` for the compiled-shape evidence.

Proof is `sorry`: it depends on the deferred `valid_jumps`/selector facts in `Bytecode.lean` and on
discharging the optimizer-on dispatch + decode + the shared body routine.
-/

open Solm

/-- **Correctness of `C` (statement only).** -/
theorem cCorrect : runtimeEquivalence!?! cConfig cBytecode Reuse.cContract := by
  sorry
