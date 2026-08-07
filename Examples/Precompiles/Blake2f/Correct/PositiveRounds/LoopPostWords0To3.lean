import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopPost
import Examples.Precompiles.Blake2f.Fallback.ZeroRounds.Words0To3.Words2To3.Word3

/-!
# BLAKE2F positive-round post-loop output bridge, words 0 through 3

This reuses the generic output-loop body facts from the fallback proof, but starts from the
arbitrary-round post-loop memory rather than the zero-round branch memories.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- From the output-loop head with index `0`, materialize output words `0..3` and return to the
output-loop head with index `4`. -/
theorem positiveRoundOutputLoopWords0To3FromSetup
    (ctx : BytecodeContext)
    {k C : Nat} {mem : ByteArray}
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨4⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWordsMem3 mem) (UInt256.ofNat 62) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 536) := by
  have rd1395_0 := evm_run hrdx with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k0, rd1382_1⟩ := outputLoopFirstBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := _)
    (C := C + 23)
    hmem rd1395_0
  have rd1395_1 := evm_run rd1382_1 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k1, rd1382_2⟩ := outputLoopSecondBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem0 mem)
    (k := _)
    (C := C + 23 + 111 + 23)
    (by
      unfold outputWordsMem0
      exact outputWord0Mem_size hmem)
    (by simpa [outputWordsMem0] using rd1395_1)
  have rd1395_2 := evm_run rd1382_2 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k2, rd1382_3⟩ := outputLoopThirdBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem1 mem)
    (k := _)
    (C := C + 23 + 111 + 23 + 111 + 23)
    (by
      unfold outputWordsMem1 outputWordsMem0
      exact outputWord1Mem_size (outputWord0Mem_size hmem))
    (by simpa [outputWordsMem1, outputWordsMem0] using rd1395_2)
  have rd1395_3 := evm_run rd1382_3 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k3, rd1382_4⟩ := outputLoopFourthBodyPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := outputWordsMem2 mem)
    (k := _)
    (C := C + 23 + 111 + 23 + 111 + 23 + 111 + 23)
    (by
      unfold outputWordsMem2 outputWordsMem1 outputWordsMem0
      exact outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size hmem)))
    (by simpa [outputWordsMem2, outputWordsMem1, outputWordsMem0] using rd1395_3)
  refine ⟨k3, ?_⟩
  have hcost :
      C + 23 + 111 + 23 + 111 + 23 + 111 + 23 + 111 = C + 536 := by
    omega
  exact RDx.withIndices (by simpa [outputWordsMem3] using rd1382_4) rfl hcost

end Blake2f
