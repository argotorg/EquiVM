import Examples.Precompiles.Blake2f.Correct.Setup.Parser.M.Words8To11

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid inputs have completed the first 13 `m` parser iterations.

The cursor is back at PC `119`, with loop index `13` and memory updated through `m[12]`. -/
theorem validM12StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨119⟩ [⟨13⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (m12StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 5311 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validM12StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first 14 `m` parser iterations.

The cursor is back at PC `119`, with loop index `14` and memory updated through `m[13]`. -/
theorem validM13StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨119⟩ [⟨14⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (m13StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 5517 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validM13StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first 15 `m` parser iterations.

The cursor is back at PC `119`, with loop index `15` and memory updated through `m[14]`. -/
theorem validM14StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨119⟩ [⟨15⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (m14StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 5723 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validM14StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first 16 `m` parser iterations.

The cursor is back at PC `119`, with loop index `16` and memory updated through `m[15]`. -/
theorem validM15StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨119⟩ [⟨16⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (m15StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 5929 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validM15StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have exited the `m` parser loop and are about to enter the `t` parser loop.

The cursor is PC `130`, immediately before the `t` loop-head `JUMPDEST`, with fresh loop index `0`
on top of the stack and memory updated through all sixteen parsed `m` words. -/
theorem validMLoopExitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨130⟩ [⟨0⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (m15StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 5956 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validMLoopExitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

end Blake2f
