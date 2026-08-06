import Examples.Precompiles.Blake2f.Correct.Setup.Parser

/-!
# BLAKE2F compression setup wrapper entry facts
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validCompressionEntryPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1154⟩
      [UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨168⟩]
      (t1StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6459 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validCompressionEntryPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have run the compression-entry allocator and reached the `v` initialization loop.

This cursor is PC `1182`, with the first compression scratch pointer `1216`, the working-vector
base pointer `1472`, active memory expanded to `46` words, and exact cumulative gas `6692`. -/
theorem validVInitLoopEntryPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨0⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (compressionVAllocMem ctx.executionEnv)
      (UInt256.ofNat 46) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6692 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validVInitLoopEntryPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag
