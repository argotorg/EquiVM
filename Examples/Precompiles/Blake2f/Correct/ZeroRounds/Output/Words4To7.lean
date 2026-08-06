import Examples.Precompiles.Blake2f.Correct.ZeroRounds.Output.Words0To3

/-!
# BLAKE2F zero-round output wrappers, words 4 through 7
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validOutputWord4ZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨5⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord4Mem
        (outputWord3Mem
          (outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem ctx.executionEnv))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8338 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord4ZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have completed the fifth output-loop write.

The cursor has returned to PC `1382` with output index `5`.  Active memory is `62` and exact
cumulative gas is `8365`. -/
theorem validOutputWord4ZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨5⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord4Mem
        (outputWord3Mem
          (outputWord2Mem (outputWord1Mem (outputWord0Mem (v14FinalFlagMem ctx.executionEnv))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8365 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord4ZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`0` zero-round inputs have completed the sixth output-loop write.

The cursor has returned to PC `1382` with output index `6`.  Active memory is `62` and exact
cumulative gas is `8472`. -/
theorem validOutputWord5ZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨6⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord5Mem
        (outputWord4Mem
          (outputWord3Mem
            (outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem ctx.executionEnv)))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8472 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord5ZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have completed the sixth output-loop write.

The cursor has returned to PC `1382` with output index `6`.  Active memory is `62` and exact
cumulative gas is `8499`. -/
theorem validOutputWord5ZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨6⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord5Mem
        (outputWord4Mem
          (outputWord3Mem
            (outputWord2Mem
              (outputWord1Mem (outputWord0Mem (v14FinalFlagMem ctx.executionEnv)))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8499 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord5ZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`0` zero-round inputs have completed the seventh output-loop write.

The cursor has returned to PC `1382` with output index `7`.  Active memory is `62` and exact
cumulative gas is `8606`. -/
theorem validOutputWord6ZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨7⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord6Mem
        (outputWord5Mem
          (outputWord4Mem
            (outputWord3Mem
              (outputWord2Mem
                (outputWord1Mem (outputWord0Mem (v13MixedMem ctx.executionEnv))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8606 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord6ZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have completed the seventh output-loop write.

The cursor has returned to PC `1382` with output index `7`.  Active memory is `62` and exact
cumulative gas is `8633`. -/
theorem validOutputWord6ZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨7⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord6Mem
        (outputWord5Mem
          (outputWord4Mem
            (outputWord3Mem
              (outputWord2Mem
                (outputWord1Mem (outputWord0Mem (v14FinalFlagMem ctx.executionEnv))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8633 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord6ZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`0` zero-round inputs have completed all eight output-loop writes.

The cursor has returned to PC `1382` with output index `8`.  Active memory is `62` and exact
cumulative gas is `8740`. -/
theorem validOutputWord7ZeroRoundsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨8⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord7Mem
        (outputWord6Mem
          (outputWord5Mem
            (outputWord4Mem
              (outputWord3Mem
                (outputWord2Mem
                  (outputWord1Mem (outputWord0Mem (v13MixedMem ctx.executionEnv)))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8740 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord7ZeroRoundsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs have completed all eight output-loop writes.

The cursor has returned to PC `1382` with output index `8`.  Active memory is `62` and exact
cumulative gas is `8767`. -/
theorem validOutputWord7ZeroRoundsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨8⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord7Mem
        (outputWord6Mem
          (outputWord5Mem
            (outputWord4Mem
              (outputWord3Mem
                (outputWord2Mem
                  (outputWord1Mem (outputWord0Mem (v14FinalFlagMem ctx.executionEnv)))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8767 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validOutputWord7ZeroRoundsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond
