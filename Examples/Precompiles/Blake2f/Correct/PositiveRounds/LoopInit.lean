import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopState
import Examples.Precompiles.Blake2f.Correct.ZeroRounds.Guards

/-!
# BLAKE2F positive-round loop initialization

The arbitrary-round loop theorem starts from `positiveRoundInvariantContext ctx 0 mem`.  The exact
RDx part of that invariant is already proved by the setup/zero-round guard wrappers; this file
packages those facts in the positive-loop invariant vocabulary.

The remaining initialization obligation is intentionally only the model/memory relation for the
chosen setup memory (`v13MixedMem` or `v14FinalFlagMem`).
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Exact RDx entry at the positive-round loop header for final flag `0`. -/
theorem positiveRoundInitialRDxZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    positiveRoundHeaderRDxContext ctx 0 (v13MixedMem ctx.executionEnv)
      (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) 0) := by
  have hflag : positiveRoundFinalFlagSet ctx = false :=
    positiveRoundFinalFlagSet_eq_false_of_byte_zero ctx hbyte
  have hsetup :=
    validRoundsLoopSetupZeroPrefix ctx hcode haccepts hvalid hbyte
  simpa [positiveRoundHeaderRDxContext, positiveRoundHeaderStack, hflag,
    positiveRoundSetupGas] using hsetup

/-- Exact RDx entry at the positive-round loop header for final flag `1`. -/
theorem positiveRoundInitialRDxOne
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    positiveRoundHeaderRDxContext ctx 0 (v14FinalFlagMem ctx.executionEnv)
      (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) 0) := by
  have hflag : positiveRoundFinalFlagSet ctx = true :=
    positiveRoundFinalFlagSet_eq_true_of_byte_one ctx hbyte
  have hsetup :=
    validRoundsLoopSetupOnePrefix ctx hcode haccepts hvalid hbyte
  simpa [positiveRoundHeaderRDxContext, positiveRoundHeaderStack, hflag,
    positiveRoundSetupGas] using hsetup

/-- Full initial positive-loop invariant for final flag `0`, assuming the setup memory relation. -/
theorem positiveRoundInitialInvariantZero_of_memory
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hmem :
      positiveRoundHeaderInvariant ctx.executionEnv 0 (v13MixedMem ctx.executionEnv)) :
    positiveRoundInvariantContext ctx 0 (v13MixedMem ctx.executionEnv) := by
  exact ⟨positiveRoundInitialRDxZero ctx hcode haccepts hvalid hbyte, hmem⟩

/-- Full initial positive-loop invariant for final flag `1`, assuming the setup memory relation. -/
theorem positiveRoundInitialInvariantOne_of_memory
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hmem :
      positiveRoundHeaderInvariant ctx.executionEnv 0 (v14FinalFlagMem ctx.executionEnv)) :
    positiveRoundInvariantContext ctx 0 (v14FinalFlagMem ctx.executionEnv) := by
  exact ⟨positiveRoundInitialRDxOne ctx hcode haccepts hvalid hbyte, hmem⟩

end Blake2f
