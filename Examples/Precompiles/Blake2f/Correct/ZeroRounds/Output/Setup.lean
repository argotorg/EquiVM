import Examples.Precompiles.Blake2f.Correct.ZeroRounds.Guards

/-!
# BLAKE2F zero-round output-loop setup wrappers
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validOutputLoopSetupZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7668 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputLoopSetupZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have entered the output-loop setup.

The cursor is PC `1382`, with output index `0` on top of the stack.  Active memory is `62` and
exact cumulative gas is `7695`. -/
theorem validOutputLoopSetupZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7695 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputLoopSetupZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`0` zero-round inputs have entered the first output-loop body.

The cursor is PC `1395`, the body target for the output-loop guard `0 < 8`.  Active memory is
`62` and exact cumulative gas is `7691`. -/
theorem validOutputLoopBodyZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1395⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7691 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputLoopBodyZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have entered the first output-loop body.

The cursor is PC `1395`, the body target for the output-loop guard `0 < 8`.  Active memory is
`62` and exact cumulative gas is `7718`. -/
theorem validOutputLoopBodyZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1395⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7718 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputLoopBodyZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond
