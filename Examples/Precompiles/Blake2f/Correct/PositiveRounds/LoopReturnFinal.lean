import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopReturnWords4To7
import Examples.Precompiles.Blake2f.Fallback.ReturnLoop.Terminal
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ReturnSlice.Final

/-!
# BLAKE2F positive-round terminal return trace

This completes the bytecode trace for the arbitrary positive-round path up to `RDxRet`.  The return
slice is still stated as the concrete bytecode return-buffer slice; the model bytearray bridge is a
separate functional-correctness obligation.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Exact bytecode gas for the positive-round successful path.

This is intentionally bytecode-specific and arbitrary-round: the loop contribution is the
computable recurrence `positiveRoundHeaderGas` evaluated at the calldata round count. -/
def positiveRoundGasCost (ctx : BytecodeContext) : Nat :=
  positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
    (Model.rounds ctx.executionEnv.calldata) + 3010

/-- From the final return-loop setup state, format all return words and execute `RETURN`. -/
theorem positiveRoundReturnRetFromSetup
    (ctx : BytecodeContext)
    {mem : ByteArray} {k C : Nat}
    (hlen : ctx.executionEnv.calldata.size = 213)
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩ [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem ctx.executionEnv mem)
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      ((returnLoopWord7Mem ctx.executionEnv mem).readWithPadding 2016 64)
      (C + 1689) := by
  obtain ⟨kWords, rd8⟩ :=
    positiveRoundReturnLoopWords0To7
      (ctx := ctx) (mem := mem) (k := k) (C := C) hlen hmem hrdx
  have hret := returnLoopExitRetGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := kWords)
    (C := C + 1651)
    hlen hmem rd8
  have hcost : C + 1651 + 38 = C + 1689 := by
    omega
  exact hret.withCost hcost

/-- Complete positive-round successful bytecode trace from an initial read64-strengthened invariant.

The output is the concrete bytecode return slice for the final compression memory. -/
theorem positiveRoundReturnRetFromInvariantRead64
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContextRead64 ctx 0 mem0) :
    ∃ memFinal,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem memFinal)).readWithPadding 2016 64)
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 3010) := by
  obtain ⟨memFinal, kSetup, hinvFinal, rd179⟩ :=
    positiveRoundReturnLoopSetupFromInvariantRead64 ctx hvalid hinv0
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hmem : memFinal.size = 1984 :=
    positiveRoundHeaderInvariant.mem_size
      (positiveRoundInvariantContext.model
        (positiveRoundInvariantContextRead64.invariant hinvFinal))
  have houtputSize : (outputWordsMem memFinal).size = 1984 :=
    outputWordsMem_size_of_size hmem
  have hret := positiveRoundReturnRetFromSetup
    (ctx := ctx)
    (mem := outputWordsMem memFinal)
    (k := kSetup)
    (C :=
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
        (Model.rounds ctx.executionEnv.calldata) + 1321)
    (by simpa [Model.inputLength] using hlen)
    houtputSize
    rd179
  refine ⟨memFinal, hinvFinal, ?_⟩
  have hcost :
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1321 + 1689 =
        positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 3010 := by
    omega
  exact hret.withCost hcost

theorem positiveRoundReturnRetZero_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ memFinal,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem memFinal)).readWithPadding 2016 64)
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 3010) := by
  exact positiveRoundReturnRetFromInvariantRead64 ctx hvalid
    (positiveRoundInitialInvariantZeroRead64 ctx hcode haccepts hvalid hbyte)

theorem positiveRoundReturnRetOne_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ memFinal,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem memFinal)).readWithPadding 2016 64)
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 3010) := by
  exact positiveRoundReturnRetFromInvariantRead64 ctx hvalid
    (positiveRoundInitialInvariantOneRead64 ctx hcode haccepts hvalid hbyte)

/-- Positive-round terminal trace, rewritten from the concrete return buffer slice to the bytecode
output-word bytearray.  The remaining bridge to the trusted pure model is the memory/model output
correctness theorem for `bytecodeOutputBytes memFinal`. -/
theorem positiveRoundReturnRetBytecodeOutputFromInvariantRead64
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContextRead64 ctx 0 mem0) :
    ∃ memFinal,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (bytecodeOutputBytes memFinal)
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 3010) := by
  obtain ⟨memFinal, hinvFinal, hret⟩ :=
    positiveRoundReturnRetFromInvariantRead64 ctx hvalid hinv0
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hmem : memFinal.size = 1984 :=
    positiveRoundHeaderInvariant.mem_size
      (positiveRoundInvariantContext.model
        (positiveRoundInvariantContextRead64.invariant hinvFinal))
  have hslice :
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem memFinal)).readWithPadding 2016 64) =
        bytecodeOutputBytes memFinal :=
    zeroRoundsRetSlice_eq_bytecodeOutputBytes ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hmem
  refine ⟨memFinal, hinvFinal, ?_⟩
  rwa [hslice] at hret

theorem positiveRoundReturnRetBytecodeOutputZero_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ memFinal,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (bytecodeOutputBytes memFinal)
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 3010) := by
  exact positiveRoundReturnRetBytecodeOutputFromInvariantRead64 ctx hvalid
    (positiveRoundInitialInvariantZeroRead64 ctx hcode haccepts hvalid hbyte)

theorem positiveRoundReturnRetBytecodeOutputOne_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ memFinal,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (bytecodeOutputBytes memFinal)
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 3010) := by
  exact positiveRoundReturnRetBytecodeOutputFromInvariantRead64 ctx hvalid
    (positiveRoundInitialInvariantOneRead64 ctx hcode haccepts hvalid hbyte)

/-- Positive-round valid trace reduced to the arbitrary-round bytecode-output bridge.

The trace/gas side is closed here.  The only remaining functional obligation is to identify the
bytecode output expression from any final loop invariant at index `Model.rounds calldata` with the
trusted pure model output.  Keeping that obligation quantified over `memFinal` avoids any
fixed-round specialization. -/
theorem positiveRoundValidTrace_of_bytecodeOutputBridge
    (hbridge : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx → valid ctx →
      0 < Model.rounds ctx.executionEnv.calldata →
      ∀ memFinal,
        positiveRoundInvariantContextRead64 ctx
          (Model.rounds ctx.executionEnv.calldata) memFinal →
        bytecodeOutputBytes memFinal = output ctx) :
    ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx →
      valid ctx →
      0 < Model.rounds ctx.executionEnv.calldata →
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (positiveRoundGasCost ctx) := by
  intro ctx hcode haccepts hvalid hrounds
  have hvalidAll : valid ctx := hvalid
  obtain ⟨_hlen, hflag⟩ := hvalid
  rcases hflag with hbyte | hbyte
  · obtain ⟨memFinal, hinvFinal, hret⟩ :=
      positiveRoundReturnRetBytecodeOutputZero_from_trace
        ctx hcode haccepts hvalidAll hbyte
    have hbytes :
        bytecodeOutputBytes memFinal = output ctx :=
      hbridge ctx hcode haccepts hvalidAll hrounds memFinal hinvFinal
    rw [positiveRoundGasCost]
    rwa [hbytes] at hret
  · obtain ⟨memFinal, hinvFinal, hret⟩ :=
      positiveRoundReturnRetBytecodeOutputOne_from_trace
        ctx hcode haccepts hvalidAll hbyte
    have hbytes :
        bytecodeOutputBytes memFinal = output ctx :=
      hbridge ctx hcode haccepts hvalidAll hrounds memFinal hinvFinal
    rw [positiveRoundGasCost]
    rwa [hbytes] at hret

end Blake2f
