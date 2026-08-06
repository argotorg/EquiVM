import Examples.Precompiles.Blake2f.Correct.Setup.Compression.Entry

/-!
# BLAKE2F compression setup wrappers, vector words 0 through 7
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validV0InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨1⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v0InitMem ctx.executionEnv)
      (UInt256.ofNat 47) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6778 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV0InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the second working-vector initialization iteration.

This returns to the loop head at PC `1182` with loop index `2`, memory updated through `v[1]`,
active memory `48`, and exact cumulative gas `6864`. -/
theorem validV1InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨2⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v1InitMem ctx.executionEnv)
      (UInt256.ofNat 48) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6864 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV1InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the third working-vector initialization iteration.

This returns to the loop head at PC `1182` with loop index `3`, memory updated through `v[2]`,
active memory `49`, and exact cumulative gas `6950`. -/
theorem validV2InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨3⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v2InitMem ctx.executionEnv)
      (UInt256.ofNat 49) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6950 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV2InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the fourth working-vector initialization iteration.

This returns to the loop head at PC `1182` with loop index `4`, memory updated through `v[3]`,
active memory `50`, and exact cumulative gas `7036`. -/
theorem validV3InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨4⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v3InitMem ctx.executionEnv)
      (UInt256.ofNat 50) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7036 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV3InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the fifth working-vector initialization iteration.

This returns to the loop head at PC `1182` with loop index `5`, memory updated through `v[4]`,
active memory `51`, and exact cumulative gas `7123`.  This iteration crosses a `Cₘ` quadratic
memory-cost boundary, so it costs one gas more than the previous vector writes. -/
theorem validV4InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨5⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v4InitMem ctx.executionEnv)
      (UInt256.ofNat 51) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7123 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV4InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the sixth working-vector initialization iteration.

This returns to the loop head at PC `1182` with loop index `6`, memory updated through `v[5]`,
active memory `52`, and exact cumulative gas `7209`. -/
theorem validV5InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨6⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v5InitMem ctx.executionEnv)
      (UInt256.ofNat 52) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7209 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV5InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the seventh working-vector initialization iteration.

This returns to the loop head at PC `1182` with loop index `7`, memory updated through `v[6]`,
active memory `53`, and exact cumulative gas `7295`. -/
theorem validV6InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨7⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v6InitMem ctx.executionEnv)
      (UInt256.ofNat 53) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7295 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV6InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the eighth working-vector initialization iteration.

This returns to the loop head at PC `1182` with loop index `8`, memory updated through `v[7]`,
active memory `54`, and exact cumulative gas `7381`.  This closes the loop iterations that copy
the parsed `h` words into the working vector. -/
theorem validV7InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1182⟩
      [⟨8⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v7InitMem ctx.executionEnv)
      (UInt256.ofNat 54) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7381 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV7InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have exited the first working-vector initialization loop.

The cursor is PC `1192`, immediately before storing the BLAKE2 IV constants into `v[8..15]`.
The copied `h[0..7]` memory is unchanged from `validV7InitPrefix`; the loop index has been popped,
active memory is still `54`, and exact cumulative gas is `7406`. -/
theorem validVLoopExitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1192⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v7InitMem ctx.executionEnv)
      (UInt256.ofNat 54) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7406 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validVLoopExitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag
