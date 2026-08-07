import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopRead64
import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopPostWords4To7
import Examples.Precompiles.Blake2f.Fallback.ReturnLoop.Setup

/-!
# BLAKE2F positive-round return-loop setup

This composes the arbitrary positive-round compression loop, output-word materialization, return
allocation, return-buffer copy, and final return-loop setup.  The return-word formatting loop itself
is left to follow-on files.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem_size_of_size {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (outputWordsMem mem).size = 1984 := by
  unfold outputWordsMem
  exact outputWord7Mem_size
    (outputWord6Mem_size
      (outputWord5Mem_size
        (outputWord4Mem_size
          (outputWord3Mem_size
            (outputWord2Mem_size
              (outputWord1Mem_size (outputWord0Mem_size hmem)))))))

/-- From the arbitrary-round loop exit with preserved `read64`, reach the final return-loop head. -/
theorem positiveRoundReturnLoopSetupFromExitRead64
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {i k C : Nat} {mem : ByteArray}
    (hinv : positiveRoundInvariantContextRead64 ctx i mem)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundExitPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩
      [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem ctx.executionEnv (outputWordsMem mem))
      (UInt256.ofNat 65) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 1298) := by
  have hmodel :=
    positiveRoundInvariantContext.model
      (positiveRoundInvariantContextRead64.invariant hinv)
  have hmem : mem.size = 1984 :=
    positiveRoundHeaderInvariant.mem_size hmodel
  obtain ⟨kOut, rd168⟩ := positiveRoundOutputLoopExitFromExit
    (ctx := ctx) (i := i) (mem := mem) (k := k) (C := C)
    hmem hrdx
  have houtputSize : (outputWordsMem mem).size = 1984 :=
    outputWordsMem_size_of_size hmem
  have houtputRead64 :
      (outputWordsMem mem).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat 1984) :=
    outputWordsMem_read64 hmem (positiveRoundInvariantContextRead64.read64 hinv)
  obtain ⟨kAlloc, rd899⟩ := returnAllocatorPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem mem)
    (k := kOut)
    (C := C + 1117)
    houtputSize houtputRead64 rd168
  obtain ⟨hlen, _hflag⟩ := hvalid
  obtain ⟨kCopy, rd176⟩ := returnBufferCopyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem mem)
    (k := kAlloc)
    (C := C + 1117 + 118)
    (by simpa [Model.inputLength] using hlen)
    rd899
  obtain ⟨kSetup, rd179⟩ := returnLoopSetupPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := returnZeroPadMem ctx.executionEnv (outputWordsMem mem))
    (aw := UInt256.ofNat 65)
    (k := kCopy)
    (C := C + 1117 + 118 + 57)
    rd176
  refine ⟨kSetup, ?_⟩
  have hcost : C + 1117 + 118 + 57 + 6 = C + 1298 := by
    omega
  exact RDx.withIndices rd179 rfl hcost

/-- From an initial positive-round invariant with preserved `read64`, run to the final return-loop
head. -/
theorem positiveRoundReturnLoopSetupFromInvariantRead64
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContextRead64 ctx 0 mem0) :
    ∃ memFinal k,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        ⟨179⟩
        [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
        (returnZeroPadMem ctx.executionEnv (outputWordsMem memFinal))
        (UInt256.ofNat 65) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1321) := by
  obtain ⟨memFinal, kLoop, hinvFinal, rdExit⟩ :=
    positiveRoundLoopRead64FromInvariant ctx hvalid hinv0
  obtain ⟨kSetup, rd179⟩ := positiveRoundReturnLoopSetupFromExitRead64
    (ctx := ctx)
    (hvalid := hvalid)
    (i := Model.rounds ctx.executionEnv.calldata)
    (mem := memFinal)
    (k := kLoop)
    (C :=
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
        (Model.rounds ctx.executionEnv.calldata) + 23)
    hinvFinal rdExit
  refine ⟨memFinal, kSetup, hinvFinal, ?_⟩
  have hcost :
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23 + 1298 =
        positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1321 := by
    omega
  exact RDx.withIndices rd179 rfl hcost

theorem positiveRoundReturnLoopSetupZero_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ memFinal k,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        ⟨179⟩
        [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
        (returnZeroPadMem ctx.executionEnv (outputWordsMem memFinal))
        (UInt256.ofNat 65) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1321) := by
  exact positiveRoundReturnLoopSetupFromInvariantRead64 ctx hvalid
    (positiveRoundInitialInvariantZeroRead64 ctx hcode haccepts hvalid hbyte)

theorem positiveRoundReturnLoopSetupOne_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ memFinal k,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        ⟨179⟩
        [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
        (returnZeroPadMem ctx.executionEnv (outputWordsMem memFinal))
        (UInt256.ofNat 65) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 1321) := by
  exact positiveRoundReturnLoopSetupFromInvariantRead64 ctx hvalid
    (positiveRoundInitialInvariantOneRead64 ctx hcode haccepts hvalid hbyte)

end Blake2f
