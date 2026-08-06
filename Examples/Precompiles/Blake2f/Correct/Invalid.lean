import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.Invalid

/-!
# BLAKE2F invalid-input bytecode-spec wrappers

Public context-level wrappers for the explicit validation-failure traces and final spec interface.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Completed invalid-input branch: calldata length different from 213.

This branch is rejected by the deployed fallback's calldata guard before any Solidity `bytes
memory` allocation, so it reaches the explicit `INVALID` validation sink and therefore matches the
caller-visible failure branch of `PrecompileSpec`. -/
theorem invalidLengthBranch
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hlen : ctx.executionEnv.calldata.size ≠ Model.inputLength) :
    ∃ exception errorThreshold,
      RDxErr runtimeBytecode ctx.gas ctx.initialState exception errorThreshold := by
  obtain ⟨hwv, hsize⟩ := haccepts
  obtain ⟨threshold, herr⟩ := invalidLengthTrace
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv hsize (by simpa [Model.inputLength] using hlen)
  exact ⟨.InvalidInstruction, threshold, herr⟩

/-- Completed bytecode-decoded final-flag branch.

This is stated against `Fallback.finalFlagWord`, the exact word tested by the fallback guard.
The remaining model bridge is to derive this premise from `¬ Model.validFinalFlag` under
`calldata.size = 213`. -/
theorem invalidFinalFlagBranchRaw
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hlen : ctx.executionEnv.calldata.size = Model.inputLength)
    (hflag : UInt256.gt (finalFlagWord ctx.executionEnv) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ exception errorThreshold,
      RDxErr runtimeBytecode ctx.gas ctx.initialState exception errorThreshold := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨threshold, herr⟩ := invalidFinalFlagTraceRaw
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag
  exact ⟨.InvalidInstruction, threshold, herr⟩

/-- Completed invalid-input trace for the BLAKE2F bytecode wrapper.

Source note: this is the bytecode-only failure half of the precompile spec.  It does not use Solm:
invalid length is discharged by the fallback's pre-allocation length guard, and invalid final flag
is discharged by the `CALLDATALOAD 212; BYTE 0; GT 1` guard after bridging that bytecode word to
the trusted model's `calldata[212]!`. -/
theorem invalidTrace : InvalidTrace := by
  intro ctx hcode haccepts hinvalid
  by_cases hlen : ctx.executionEnv.calldata.size = Model.inputLength
  · apply invalidFinalFlagBranchRaw ctx hcode haccepts hlen
    apply finalFlagGuard_of_invalid
    · simpa [Model.inputLength] using hlen
    · intro hflag
      exact hinvalid ⟨hlen, hflag⟩
  · exact invalidLengthBranch ctx hcode haccepts hlen

/-- Close the BLAKE2F precompile-style bytecode spec from branch-local RDx traces. -/
theorem bytecodeSpec_of_traces
    (gasCost : BytecodeContext → Nat)
    (hvalid : ValidTrace gasCost)
    (hinvalid : InvalidTrace) :
    bytecodeSpecTarget gasCost := by
  exact PrecompileSpec.ofRDxRetOrErr
    (code := runtimeBytecode)
    (accepts := accepts)
    (valid := valid)
    (output := output)
    (gasCost := gasCost)
    hvalid
    hinvalid

/-- Current BLAKE2F bytecode-spec interface after closing the invalid-input side.

The remaining proof obligation is the valid-input RDx return trace with its exact bytecode gas
expression. -/
theorem bytecodeSpec_of_validTrace
    (gasCost : BytecodeContext → Nat)
    (hvalid : ValidTrace gasCost) :
    bytecodeSpecTarget gasCost :=
  bytecodeSpec_of_traces gasCost hvalid invalidTrace

end Blake2f
