import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopPostWords0To3
import Examples.Precompiles.Blake2f.Fallback.ZeroRounds.Words4To7.Words6To7.Word7

/-!
# BLAKE2F positive-round post-loop output bridge, words 4 through 7
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- From output-loop index `4`, materialize output words `4..7`, then fall through to the shared
return path at PC `168`. -/
theorem positiveRoundOutputLoopWords4To7Exit
    (ctx : BytecodeContext)
    {k C : Nat} {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨4⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWordsMem3 mem) (UInt256.ofNat 62) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨168⟩
      [⟨1216⟩]
      (outputWordsMem mem) (UInt256.ofNat 62) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 573) := by
  have hmem3 : (outputWordsMem3 mem).size = 1984 := by
    unfold outputWordsMem3 outputWordsMem2 outputWordsMem1 outputWordsMem0
    exact outputWord3Mem_size
      (outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size hmem)))
  have rd1395_4 := evm_run hrdx with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k4, rd1382_5⟩ := outputLoopFifthBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem3 mem)
    (k := _)
    (C := C + 23)
    hmem3 rd1395_4
  have rd1395_5 := evm_run rd1382_5 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k5, rd1382_6⟩ := outputLoopSixthBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem4 mem)
    (k := _)
    (C := C + 23 + 111 + 23)
    (by
      unfold outputWordsMem4
      exact outputWord4Mem_size hmem3)
    (by simpa [outputWordsMem4] using rd1395_5)
  have rd1395_6 := evm_run rd1382_6 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k6, rd1382_7⟩ := outputLoopSeventhBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem5 mem)
    (k := _)
    (C := C + 23 + 111 + 23 + 111 + 23)
    (by
      unfold outputWordsMem5 outputWordsMem4
      exact outputWord5Mem_size (outputWord4Mem_size hmem3))
    (by simpa [outputWordsMem5, outputWordsMem4] using rd1395_6)
  have rd1395_7 := evm_run rd1382_7 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k7, rd1382_8⟩ := outputLoopEighthBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem6 mem)
    (k := _)
    (C := C + 23 + 111 + 23 + 111 + 23 + 111 + 23)
    (by
      unfold outputWordsMem6 outputWordsMem5 outputWordsMem4
      exact outputWord6Mem_size (outputWord5Mem_size (outputWord4Mem_size hmem3)))
    (by simpa [outputWordsMem6, outputWordsMem5, outputWordsMem4] using rd1395_7)
  have rd168 := evm_run rd1382_8 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiNT (by native_decide),
    pop,
    pop,
    pop,
    jump (by jump_dest) ]
  refine ⟨k7 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1, ?_⟩
  have hcost :
      C + 23 + 111 + 23 + 111 + 23 + 111 + 23 + 111 + 37 = C + 573 := by
    omega
  exact RDx.withIndices (by simpa [outputWordsMem, outputWordsMem7, outputWordsMem6] using rd168)
    rfl hcost

/-- Complete output-loop bridge from the arbitrary-round post-loop setup state. -/
theorem positiveRoundOutputLoopExitFromSetup
    (ctx : BytecodeContext)
    {k C : Nat} {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨168⟩
      [⟨1216⟩]
      (outputWordsMem mem) (UInt256.ofNat 62) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 1109) := by
  obtain ⟨k0, rd4⟩ := positiveRoundOutputLoopWords0To3FromSetup
    (ctx := ctx) (mem := mem) (k := k) (C := C) hmem hrdx
  obtain ⟨k1, rd168⟩ := positiveRoundOutputLoopWords4To7Exit
    (ctx := ctx) (mem := mem) (k := k0) (C := C + 536) hmem rd4
  refine ⟨k1, ?_⟩
  have hcost : C + 536 + 573 = C + 1109 := by omega
  exact RDx.withIndices rd168 rfl hcost

/-- Positive-round post-loop output bridge from the arbitrary-round loop-exit state. -/
theorem positiveRoundOutputLoopExitFromExit
    (ctx : BytecodeContext)
    {i k C : Nat} {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundExitPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨168⟩
      [⟨1216⟩]
      (outputWordsMem mem) (UInt256.ofNat 62) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 1117) := by
  obtain ⟨k0, rd1382⟩ := positiveRoundOutputLoopSetupFromExit
    (ctx := ctx) (i := i) (mem := mem) (k := k) (C := C) hrdx
  obtain ⟨k1, rd168⟩ := positiveRoundOutputLoopExitFromSetup
    (ctx := ctx) (mem := mem) (k := k0) (C := C + 8) hmem rd1382
  refine ⟨k1, ?_⟩
  have hcost : C + 8 + 1109 = C + 1117 := by omega
  exact RDx.withIndices rd168 rfl hcost

end Blake2f
