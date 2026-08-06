import Examples.Precompiles.Blake2f.Correct.Setup.Compression.V0To7

/-!
# BLAKE2F compression setup wrappers, vector words 8 through final-flag rejoin
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validV8InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1207⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v8InitMem ctx.executionEnv)
      (UInt256.ofNat 55) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7424 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV8InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have stored the second BLAKE2 IV constant into `v[9]`.

The cursor is PC `1222`, immediately before the third IV constant write.  Active memory is `56`
and exact cumulative gas is `7443`; this write crosses a `Cₘ` quadratic memory-cost boundary. -/
theorem validV9InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1222⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v9InitMem ctx.executionEnv)
      (UInt256.ofNat 56) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7443 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV9InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have stored the third BLAKE2 IV constant into `v[10]`.

The cursor is PC `1237`, immediately before the fourth IV constant write.  Active memory is `57`
and exact cumulative gas is `7461`. -/
theorem validV10InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1237⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v10InitMem ctx.executionEnv)
      (UInt256.ofNat 57) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7461 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV10InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have stored the fourth BLAKE2 IV constant into `v[11]`.

The cursor is PC `1252`, immediately before the fifth IV constant write.  Active memory is `58`
and exact cumulative gas is `7479`. -/
theorem validV11InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1252⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v11InitMem ctx.executionEnv)
      (UInt256.ofNat 58) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7479 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV11InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have stored the fifth BLAKE2 IV constant into `v[12]`.

The cursor is PC `1267`, immediately before the sixth IV constant write.  Active memory is `59`
and exact cumulative gas is `7497`. -/
theorem validV12InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1267⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v12InitMem ctx.executionEnv)
      (UInt256.ofNat 59) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7497 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV12InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have stored the sixth BLAKE2 IV constant into `v[13]`.

The cursor is PC `1282`, immediately before the seventh IV constant write.  Active memory is `60`
and exact cumulative gas is `7516`; this write crosses a `Cₘ` quadratic memory-cost boundary. -/
theorem validV13InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1282⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v13InitMem ctx.executionEnv)
      (UInt256.ofNat 60) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7516 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV13InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have stored the seventh BLAKE2 IV constant into `v[14]`.

The cursor is PC `1297`, immediately before the eighth IV constant write.  Active memory is `61`
and exact cumulative gas is `7534`. -/
theorem validV14InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1297⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v14InitMem ctx.executionEnv)
      (UInt256.ofNat 61) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7534 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV14InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have stored the eighth BLAKE2 IV constant into `v[15]`.

The cursor is PC `1312`, immediately before the `t`/final-flag mixing block.  Active memory is
`62` and exact cumulative gas is `7552`. -/
theorem validV15InitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1312⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v15InitMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7552 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validV15InitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have mixed `t[0]` and `t[1]` into `v[12]` and `v[13]`.

The cursor is PC `1367`, immediately before the final-block `JUMPI`.  The stack still contains the
bytecode-level final-flag equality term, so the next proof can split the valid flag cases exactly.
Active memory is `62` and exact cumulative gas is `7624`. -/
theorem validTMixBranchPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1367⟩
      [⟨3298⟩, UInt256.eq (parsedFinalFlagWord ctx.executionEnv) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7624 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validTMixBranchPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs with final flag `0` fall through the final-block branch.

The cursor is PC `1368`, immediately before the fallthrough `JUMPDEST`.  Active memory is `62` and
exact cumulative gas is `7634`. -/
theorem validFinalFlagZeroBranchPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1368⟩
      [⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7634 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validFinalFlagZeroBranchPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte

/-- Valid inputs with final flag `1` take the final-block branch.

The cursor is PC `3298`, immediately before the taken branch's `JUMPDEST`.  Active memory is `62`
and exact cumulative gas is `7634`. -/
theorem validFinalFlagOneBranchPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3298⟩
      [⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (v13MixedMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7634 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validFinalFlagOneBranchPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte

/-- Valid inputs with final flag `1` overwrite `v[14]` and rejoin the common path.

The cursor is PC `1368`, matching the flag-`0` fallthrough PC, but memory has the final-block
overwrite at `v[14]`.  Active memory is `62` and exact cumulative gas is `7661`. -/
theorem validFinalFlagOneRejoinPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1368⟩
      [⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 7661 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validFinalFlagOneRejoinPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte

end Blake2f
