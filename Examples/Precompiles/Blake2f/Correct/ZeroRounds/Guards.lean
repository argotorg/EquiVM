import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.ReturnLoop
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F zero-round valid-input wrappers

Public context-level wrappers for the zero-round output and return-loop bytecode facts.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid inputs with final flag `0` have entered the rounds-loop setup.

The cursor is PC `1370`, immediately before the rounds-loop `JUMPDEST`, with loop index `0` pushed.
Active memory is `62` and exact cumulative gas is `7637`. -/
theorem validRoundsLoopSetupZeroPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1370⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7637 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validRoundsLoopSetupZeroPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte

/-- Valid inputs with final flag `1` have entered the rounds-loop setup after the final-block
overwrite.

The cursor is PC `1370`, immediately before the rounds-loop `JUMPDEST`, with loop index `0` pushed.
Active memory is `62` and exact cumulative gas is `7664`. -/
theorem validRoundsLoopSetupOnePrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1370⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7664 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validRoundsLoopSetupOnePrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte

/-- Valid final-flag-`0` inputs with zero rounds leave the compression loop at the first guard.

The cursor is PC `1378`, the fallthrough after the PC `1377` `JUMPI`.  Active memory is `62` and
exact cumulative gas is `7660`. -/
theorem validRoundsGuardZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1378⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7660 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validRoundsGuardZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`0` inputs with positive rounds enter the compression-loop body.

The cursor is PC `1445`, the loop body target.  Active memory is `62` and exact cumulative gas is
`7660`. -/
theorem validRoundsGuardPositiveRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1445⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7660 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validRoundsGuardPositiveRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` inputs with zero rounds leave the compression loop at the first guard.

The cursor is PC `1378`, preserving the final-block memory overwrite.  Active memory is `62` and
exact cumulative gas is `7687`. -/
theorem validRoundsGuardZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1378⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7687 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validRoundsGuardZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` inputs with positive rounds enter the compression-loop body.

The cursor is PC `1445`, preserving the final-block memory overwrite.  Active memory is `62` and
exact cumulative gas is `7687`. -/
theorem validRoundsGuardPositiveRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1445⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7687 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validRoundsGuardPositiveRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Model-facing zero-round guard, final flag `0`. -/
theorem validRoundsGuardZeroRoundsZeroFlagPrefix_of_modelRoundsZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 0) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1378⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7660 := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  exact validRoundsGuardZeroRoundsZeroFlagPrefix ctx hcode haccepts hvalidAll hbyte
    (bytecodeRoundGuard_zero_of_modelRounds_zero ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

/-- Model-facing positive-round guard, final flag `0`. -/
theorem validRoundsGuardPositiveRoundsZeroFlagPrefix_of_modelRoundsPos
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 0 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1445⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7660 := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  exact validRoundsGuardPositiveRoundsZeroFlagPrefix ctx hcode haccepts hvalidAll hbyte
    (bytecodeRoundGuard_ne_zero_of_modelRounds_pos ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

/-- Model-facing zero-round guard, final flag `1`. -/
theorem validRoundsGuardZeroRoundsOneFlagPrefix_of_modelRoundsZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 0) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1378⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7687 := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  exact validRoundsGuardZeroRoundsOneFlagPrefix ctx hcode haccepts hvalidAll hbyte
    (bytecodeRoundGuard_zero_of_modelRounds_zero ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

/-- Model-facing positive-round guard, final flag `1`. -/
theorem validRoundsGuardPositiveRoundsOneFlagPrefix_of_modelRoundsPos
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 0 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1445⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7687 := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  exact validRoundsGuardPositiveRoundsOneFlagPrefix ctx hcode haccepts hvalidAll hbyte
    (bytecodeRoundGuard_ne_zero_of_modelRounds_pos ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

end Blake2f
