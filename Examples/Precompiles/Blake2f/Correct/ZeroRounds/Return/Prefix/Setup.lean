import Examples.Precompiles.Blake2f.Fallback.OutputBridge
import Examples.Precompiles.Blake2f.Fallback.ReturnLoop

/-!
# BLAKE2F zero-round return setup wrappers
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validReturnAllocZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨899⟩
      [⟨1984⟩, ⟨176⟩, ⟨96⟩, ⟨1216⟩]
      (returnAllocMem (outputWordsMem (v13MixedMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8895 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnAllocZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have allocated the Solidity return buffer.

The cursor is PC `899`, with exact cumulative gas `8922`. -/
theorem validReturnAllocZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨899⟩
      [⟨1984⟩, ⟨176⟩, ⟨96⟩, ⟨1216⟩]
      (returnAllocMem (outputWordsMem (v14FinalFlagMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8922 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnAllocZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`0` zero-round inputs have returned from the return-buffer copy helper.

The cursor is PC `176`, immediately before the final return formatting loop.  Active memory is
`65`, and exact cumulative gas is `8952`. -/
theorem validReturnCopyZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨176⟩
      [⟨1984⟩, ⟨1216⟩]
      (returnZeroPadMem ctx.executionEnv (outputWordsMem (v13MixedMem ctx.executionEnv)))
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8952 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnCopyZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have returned from the return-buffer copy helper.

The cursor is PC `176`, with exact cumulative gas `8979`. -/
theorem validReturnCopyZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨176⟩
      [⟨1984⟩, ⟨1216⟩]
      (returnZeroPadMem ctx.executionEnv (outputWordsMem (v14FinalFlagMem ctx.executionEnv)))
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8979 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnCopyZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`0` zero-round inputs are at the final return-loop head.

The cursor is PC `179`, with loop index `0`, scratch output pointer `0x4c0`, return buffer pointer
`0x7c0`, active memory `65`, and exact cumulative gas `8958`. -/
theorem validReturnLoopSetupZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩
      [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem ctx.executionEnv (outputWordsMem (v13MixedMem ctx.executionEnv)))
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8958 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnLoopSetupZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs are at the final return-loop head.

The cursor is PC `179`, with exact cumulative gas `8985`. -/
theorem validReturnLoopSetupZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨179⟩
      [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem ctx.executionEnv (outputWordsMem (v14FinalFlagMem ctx.executionEnv)))
      (UInt256.ofNat 65) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8985 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnLoopSetupZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond
