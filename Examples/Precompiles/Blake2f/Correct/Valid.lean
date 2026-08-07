import Examples.Precompiles.Blake2f.Correct.ZeroRounds
import Examples.Precompiles.Blake2f.Correct.PositiveRounds

/-!
# BLAKE2F valid-input bytecode trace

This module joins the completed zero-round and positive-round successful traces into one
valid-input obligation for the bytecode-specific exact gas expression.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Exact successful-path bytecode gas for valid BLAKE2F inputs. -/
def bytecodeGasCost (ctx : BytecodeContext) : Nat :=
  if Model.rounds ctx.executionEnv.calldata = 0 then
    zeroRoundGasCost ctx
  else
    positiveRoundGasCost ctx

/-- Completed successful trace for all valid BLAKE2F inputs. -/
theorem validTrace : ValidTrace bytecodeGasCost := by
  intro ctx hcode haccepts hvalid
  by_cases hrounds0 : Model.rounds ctx.executionEnv.calldata = 0
  · unfold bytecodeGasCost
    rw [if_pos hrounds0]
    exact zeroRoundValidTrace ctx hcode haccepts hvalid hrounds0
  · have hroundsPos : 0 < Model.rounds ctx.executionEnv.calldata :=
      Nat.pos_of_ne_zero hrounds0
    unfold bytecodeGasCost
    rw [if_neg hrounds0]
    exact positiveRoundValidTrace ctx hcode haccepts hvalid hroundsPos

end Blake2f
