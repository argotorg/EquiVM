import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopReturnSetup
import Examples.Precompiles.Blake2f.Fallback.ReturnLoop.Words0To3.Words2To3.Word3

/-!
# BLAKE2F positive-round return-loop bridge, words 0 through 3
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Format return words `0..3` from the shared return-loop head. -/
theorem positiveRoundReturnLoopWords0To3
    (ctx : BytecodeContext)
    {mem : ByteArray} {k C : Nat}
    (hlen : ctx.executionEnv.calldata.size = 213)
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩ [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem ctx.executionEnv mem)
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩ [⟨4⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord3Mem ctx.executionEnv mem)
      (UInt256.ofNat 65) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 824) := by
  obtain ⟨k0, rd1⟩ := returnLoopFirstWordPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := k)
    (C := C)
    hlen hmem hrdx
  obtain ⟨k1, rd2⟩ := returnLoopSecondWordPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := k0)
    (C := C + 206)
    hlen hmem rd1
  obtain ⟨k2, rd3⟩ := returnLoopThirdWordPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := k1)
    (C := C + 206 + 206)
    hlen hmem rd2
  obtain ⟨k3, rd4⟩ := returnLoopFourthWordPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := k2)
    (C := C + 206 + 206 + 206)
    hlen hmem rd3
  refine ⟨k3, ?_⟩
  have hcost : C + 206 + 206 + 206 + 206 = C + 824 := by
    omega
  exact RDx.withIndices rd4 rfl hcost

end Blake2f
