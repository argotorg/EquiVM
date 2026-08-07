import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopReturnWords0To3
import Examples.Precompiles.Blake2f.Fallback.ReturnLoop.Words4To7.Words6To7.Word7

/-!
# BLAKE2F positive-round return-loop bridge, words 4 through 7
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Format return words `4..7`, ending at return-loop index `8`. -/
theorem positiveRoundReturnLoopWords4To7
    (ctx : BytecodeContext)
    {mem : ByteArray} {k C : Nat}
    (hlen : ctx.executionEnv.calldata.size = 213)
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩ [⟨4⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord3Mem ctx.executionEnv mem)
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩ [⟨8⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord7Mem ctx.executionEnv mem)
      (UInt256.ofNat 66) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 827) := by
  obtain ⟨k4, rd5⟩ := returnLoopFifthWordPrefixGasFrom
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
  obtain ⟨k5, rd6⟩ := returnLoopSixthWordPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := k4)
    (C := C + 206)
    hlen hmem rd5
  obtain ⟨k6, rd7⟩ := returnLoopSeventhWordPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := k5)
    (C := C + 206 + 209)
    hlen hmem rd6
  obtain ⟨k7, rd8⟩ := returnLoopEighthWordPrefixGasFrom
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (mem := mem)
    (k := k6)
    (C := C + 206 + 209 + 206)
    hlen hmem rd7
  refine ⟨k7, ?_⟩
  have hcost : C + 206 + 209 + 206 + 206 = C + 827 := by
    omega
  exact RDx.withIndices rd8 rfl hcost

/-- Format all eight return words from the return-loop setup state. -/
theorem positiveRoundReturnLoopWords0To7
    (ctx : BytecodeContext)
    {mem : ByteArray} {k C : Nat}
    (hlen : ctx.executionEnv.calldata.size = 213)
    (hmem : mem.size = 1984)
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩ [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem ctx.executionEnv mem)
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩ [⟨8⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord7Mem ctx.executionEnv mem)
      (UInt256.ofNat 66) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k' (C + 1651) := by
  obtain ⟨k3, rd4⟩ :=
    positiveRoundReturnLoopWords0To3
      (ctx := ctx) (mem := mem) (k := k) (C := C) hlen hmem hrdx
  obtain ⟨k7, rd8⟩ :=
    positiveRoundReturnLoopWords4To7
      (ctx := ctx) (mem := mem) (k := k3) (C := C + 824) hlen hmem rd4
  refine ⟨k7, ?_⟩
  have hcost : C + 824 + 827 = C + 1651 := by
    omega
  exact RDx.withIndices rd8 rfl hcost

end Blake2f
