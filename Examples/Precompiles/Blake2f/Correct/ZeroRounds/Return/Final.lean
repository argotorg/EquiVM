import Examples.Precompiles.Blake2f.Correct.ZeroRounds.Return.Prefix

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` zero-round inputs terminate successfully with the concrete bytecode
return slice and exact gas `10647`. -/
theorem validReturnZeroRoundsZeroFlagRet
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v13MixedMem ctx.executionEnv))).readWithPadding 2016 64)
      10647 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnZeroRoundsZeroFlagRetGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Valid final-flag-`1` zero-round inputs terminate successfully with the concrete bytecode
return slice and exact gas `10674`. -/
theorem validReturnZeroRoundsOneFlagRet
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hcond :
      UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩) = ⟨0⟩) :
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v14FinalFlagMem ctx.executionEnv))).readWithPadding 2016 64)
      10674 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validReturnZeroRoundsOneFlagRetGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte hcond

/-- Model-facing zero-round final-flag-`0` terminal trace.

This is the same bytecode trace as `validReturnZeroRoundsZeroFlagRet`, but the loop-exit premise is
the trusted model parser fact `Model.rounds calldata = 0` rather than the internal EVM
`LT 0 rounds` guard result. -/
theorem validReturnZeroRoundsZeroFlagRet_of_modelRoundsZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 0) :
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v13MixedMem ctx.executionEnv))).readWithPadding 2016 64)
      10647 := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  exact validReturnZeroRoundsZeroFlagRet ctx hcode haccepts hvalidAll hbyte
    (bytecodeRoundGuard_zero_of_modelRounds_zero ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

/-- Model-facing zero-round final-flag-`1` terminal trace.

This is the same bytecode trace as `validReturnZeroRoundsOneFlagRet`, but the loop-exit premise is
the trusted model parser fact `Model.rounds calldata = 0` rather than the internal EVM
`LT 0 rounds` guard result. -/
theorem validReturnZeroRoundsOneFlagRet_of_modelRoundsZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 0) :
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v14FinalFlagMem ctx.executionEnv))).readWithPadding 2016 64)
      10674 := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  exact validReturnZeroRoundsOneFlagRet ctx hcode haccepts hvalidAll hbyte
    (bytecodeRoundGuard_zero_of_modelRounds_zero ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

/-- Bytecode-specific exact gas for the already-proved zero-round terminal paths. -/
def zeroRoundGasCost (ctx : BytecodeContext) : Nat :=
  if ctx.executionEnv.calldata[212]! = 0 then 10647 else 10674

/-- Final-flag-`0` zero-round terminal trace, rewritten to the public pure-output interface.

The remaining premise is precisely the pure bytearray bridge from the concrete bytecode return
slice to `output ctx`.  Keeping that bridge as an explicit premise lets the RDx trace side and the
word/byte algebra side develop independently. -/
theorem validReturnZeroRoundsZeroFlagRet_output_of_modelRoundsZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 0)
    (houtput :
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v13MixedMem ctx.executionEnv))).readWithPadding 2016 64) =
        output ctx) :
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (output ctx)
      10647 := by
  rw [← houtput]
  exact validReturnZeroRoundsZeroFlagRet_of_modelRoundsZero
    ctx hcode haccepts hvalid hbyte hrounds

/-- Final-flag-`1` zero-round terminal trace, rewritten to the public pure-output interface. -/
theorem validReturnZeroRoundsOneFlagRet_output_of_modelRoundsZero
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 0)
    (houtput :
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v14FinalFlagMem ctx.executionEnv))).readWithPadding 2016 64) =
        output ctx) :
    RDxRet runtimeBytecode ctx.gas ctx.initialState
      (ctx.createdAccounts, ctx.accountMap)
      (output ctx)
      10674 := by
  rw [← houtput]
  exact validReturnZeroRoundsOneFlagRet_of_modelRoundsZero
    ctx hcode haccepts hvalid hbyte hrounds

/-- Zero-round valid trace reduced to the two concrete bytearray-output bridge obligations. -/
theorem zeroRoundValidTrace_of_outputBridges
    (hbridge0 : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx → valid ctx →
      ctx.executionEnv.calldata[212]! = 0 →
      Model.rounds ctx.executionEnv.calldata = 0 →
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v13MixedMem ctx.executionEnv))).readWithPadding 2016 64) =
        output ctx)
    (hbridge1 : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx → valid ctx →
      ctx.executionEnv.calldata[212]! = 1 →
      Model.rounds ctx.executionEnv.calldata = 0 →
      ((returnLoopWord7Mem ctx.executionEnv
          (outputWordsMem (v14FinalFlagMem ctx.executionEnv))).readWithPadding 2016 64) =
        output ctx) :
    ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx →
      valid ctx →
      Model.rounds ctx.executionEnv.calldata = 0 →
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (zeroRoundGasCost ctx) := by
  intro ctx hcode haccepts hvalid hrounds
  have hvalidAll : valid ctx := hvalid
  obtain ⟨_hlen, hflag⟩ := hvalid
  rcases hflag with hbyte | hbyte
  · unfold zeroRoundGasCost
    rw [hbyte]
    exact validReturnZeroRoundsZeroFlagRet_output_of_modelRoundsZero
      ctx hcode haccepts hvalidAll hbyte hrounds
      (hbridge0 ctx hcode haccepts hvalidAll hbyte hrounds)
  · unfold zeroRoundGasCost
    rw [hbyte]
    simp
    exact validReturnZeroRoundsOneFlagRet_output_of_modelRoundsZero
      ctx hcode haccepts hvalidAll hbyte hrounds
      (hbridge1 ctx hcode haccepts hvalidAll hbyte hrounds)

/-- Zero-round valid trace reduced to bytecode-output-byte bridge obligations.

This is the preferred interface for completing the functional side: the RDx/return-memory proof has
already established that the terminal return slice is `bytecodeOutputBytes` of the zero-round output
memory.  What remains is to identify that bytecode word/endianness expression with
`Model.output`. -/
theorem zeroRoundValidTrace_of_bytecodeOutputBridges
    (hbridge0 : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx → valid ctx →
      ctx.executionEnv.calldata[212]! = 0 →
      Model.rounds ctx.executionEnv.calldata = 0 →
      bytecodeOutputBytes (v13MixedMem ctx.executionEnv) = output ctx)
    (hbridge1 : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx → valid ctx →
      ctx.executionEnv.calldata[212]! = 1 →
      Model.rounds ctx.executionEnv.calldata = 0 →
      bytecodeOutputBytes (v14FinalFlagMem ctx.executionEnv) = output ctx) :
    ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx →
      valid ctx →
      Model.rounds ctx.executionEnv.calldata = 0 →
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (zeroRoundGasCost ctx) := by
  apply zeroRoundValidTrace_of_outputBridges
  · intro ctx hcode haccepts hvalid hbyte hrounds
    rw [zeroRoundsZeroFlagRetSlice_eq_bytecodeOutputBytes ctx.executionEnv]
    · exact hbridge0 ctx hcode haccepts hvalid hbyte hrounds
    · obtain ⟨hlen, _⟩ := hvalid
      simpa [Model.inputLength] using hlen
  · intro ctx hcode haccepts hvalid hbyte hrounds
    rw [zeroRoundsOneFlagRetSlice_eq_bytecodeOutputBytes ctx.executionEnv]
    · exact hbridge1 ctx hcode haccepts hvalid hbyte hrounds
    · obtain ⟨hlen, _⟩ := hvalid
      simpa [Model.inputLength] using hlen

/-/ Zero-round valid trace reduced to the final byte-normal-form bridge obligations.

At this point the RDx trace, return-memory slicing, staged bytecode output-word computation, and
pure model zero-round normalization have all been discharged.  The remaining obligations are the
byte-order/parser bridges identifying the bytecode normal forms with the trusted model normal forms.
-/
theorem zeroRoundValidTrace_of_zeroRoundByteNormalFormBridges
    (hbridge0 : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx → valid ctx →
      ctx.executionEnv.calldata[212]! = 0 →
      Model.rounds ctx.executionEnv.calldata = 0 →
      bytecodeZeroFlag0Bytes ctx.executionEnv = modelZeroFlag0Bytes ctx.executionEnv.calldata)
    (hbridge1 : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx → valid ctx →
      ctx.executionEnv.calldata[212]! = 1 →
      Model.rounds ctx.executionEnv.calldata = 0 →
      bytecodeZeroFlag1Bytes ctx.executionEnv = modelZeroFlag1Bytes ctx.executionEnv.calldata) :
    ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx →
      valid ctx →
      Model.rounds ctx.executionEnv.calldata = 0 →
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (zeroRoundGasCost ctx) := by
  apply zeroRoundValidTrace_of_bytecodeOutputBridges
  · intro ctx hcode haccepts hvalid hbyte hrounds
    have hvalidAll : valid ctx := hvalid
    obtain ⟨hlen, _⟩ := hvalid
    rw [bytecodeOutputBytes_v13MixedMem_norm ctx.executionEnv
      (by simpa [Model.inputLength] using hlen)]
    unfold output
    rw [model_output_zero_flag0_norm ctx.executionEnv.calldata hrounds hbyte]
    exact hbridge0 ctx hcode haccepts hvalidAll hbyte hrounds
  · intro ctx hcode haccepts hvalid hbyte hrounds
    have hvalidAll : valid ctx := hvalid
    obtain ⟨hlen, _⟩ := hvalid
    rw [bytecodeOutputBytes_v14FinalFlagMem_norm ctx.executionEnv
      (by simpa [Model.inputLength] using hlen)]
    unfold output
    rw [model_output_zero_flag1_norm ctx.executionEnv.calldata hrounds hbyte]
    exact hbridge1 ctx hcode haccepts hvalidAll hbyte hrounds

/-- Final no-premise zero-round bytecode theorem.

For every valid accepted zero-round input, the runtime bytecode returns the trusted pure Blake2f
model output and consumes the exact branch-specific gas recorded by `zeroRoundGasCost`.
-/
theorem zeroRoundValidTrace :
    ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx →
      valid ctx →
      Model.rounds ctx.executionEnv.calldata = 0 →
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (zeroRoundGasCost ctx) := by
  apply zeroRoundValidTrace_of_zeroRoundByteNormalFormBridges
  · intro ctx _hcode _haccepts hvalid _hbyte _hrounds
    obtain ⟨hlen, _⟩ := hvalid
    exact bytecodeZeroFlag0Bytes_eq_modelZeroFlag0Bytes ctx.executionEnv
      (by simpa [Model.inputLength] using hlen)
  · intro ctx _hcode _haccepts hvalid _hbyte _hrounds
    obtain ⟨hlen, _⟩ := hvalid
    exact bytecodeZeroFlag1Bytes_eq_modelZeroFlag1Bytes ctx.executionEnv
      (by simpa [Model.inputLength] using hlen)

end Blake2f
