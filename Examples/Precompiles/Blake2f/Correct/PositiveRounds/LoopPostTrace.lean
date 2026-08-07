import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopPostWords4To7

/-!
# BLAKE2F positive-round post-loop trace wrappers

These theorems compose the arbitrary-round compression-loop proof with the generic output-loop
materialization proof.  The result reaches the shared return path at PC `168` with the scratch
output words written from the final compression memory.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- From any established initial positive-round invariant, run all remaining compression rounds and
materialize the eight scratch output words. -/
theorem positiveRoundOutputLoopExitFromInvariant_from_trace
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContext ctx 0 mem0) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        ⟨168⟩
        [⟨1216⟩]
        (outputWordsMem memFinal) (UInt256.ofNat 62) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1140) := by
  obtain ⟨memFinal, kLoop, hinvFinal, rdExit⟩ :=
    positiveRoundLoopFromInvariant_from_trace ctx hvalid hinv0
  have hmodel := positiveRoundInvariantContext.model hinvFinal
  obtain ⟨kOut, rd168⟩ := positiveRoundOutputLoopExitFromExit
    (ctx := ctx)
    (i := Model.rounds ctx.executionEnv.calldata)
    (mem := memFinal)
    (k := kLoop)
    (C :=
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
        (Model.rounds ctx.executionEnv.calldata) + 23)
    (positiveRoundHeaderInvariant.mem_size hmodel)
    rdExit
  refine ⟨memFinal, kOut, hinvFinal, ?_⟩
  have hcost :
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23 + 1117 =
        positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1140 := by
    omega
  exact RDx.withIndices rd168 rfl hcost

/-- Final-flag `0` positive-round path through output-word materialization. -/
theorem positiveRoundOutputLoopExitZero_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        ⟨168⟩
        [⟨1216⟩]
        (outputWordsMem memFinal) (UInt256.ofNat 62) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1140) := by
  exact positiveRoundOutputLoopExitFromInvariant_from_trace ctx hvalid
    (positiveRoundInitialInvariantZero ctx hcode haccepts hvalid hbyte)

/-- Final-flag `1` positive-round path through output-word materialization. -/
theorem positiveRoundOutputLoopExitOne_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        ⟨168⟩
        [⟨1216⟩]
        (outputWordsMem memFinal) (UInt256.ofNat 62) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1140) := by
  exact positiveRoundOutputLoopExitFromInvariant_from_trace ctx hvalid
    (positiveRoundInitialInvariantOne ctx hcode haccepts hvalid hbyte)

end Blake2f
