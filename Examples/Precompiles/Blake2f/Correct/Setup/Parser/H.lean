import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.Setup

/-!
# BLAKE2F valid-input setup wrappers: h words

Context-level wrappers for parsing/storing the eight h words.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid inputs have entered the first `h` parser iteration and computed the unaligned
`MLOAD` address for `h[0]`.

The cursor is PC `558`, immediately before loading the 32-byte word that contains EIP-152 bytes
`4..11`. -/
theorem validH0LoadAddressPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨558⟩ [⟨164⟩, ⟨644⟩, ⟨0⟩, ⟨1⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (tArrayZeroMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 1012 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH0LoadAddressPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have loaded and byte-swapped the first parsed `h` word.

The cursor is PC `644`, just after returning from the compiler-emitted `swap64` helper for
`h[0]`.  The parsed word is kept as the bytecode-level term `h0ParsedWord`; a later bridge will
connect it to `Model.readLE64 calldata 4`. -/
theorem validH0ParsedPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨644⟩ [h0ParsedWord ctx.executionEnv, ⟨0⟩, ⟨1⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (tArrayZeroMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 1131 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH0ParsedPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first `h` parser iteration.

The cursor is back at PC `108`, with loop index `1` and memory updated at `h[0]`. -/
theorem validH0StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨1⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h0StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 1164 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH0StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first two `h` parser iterations.

The cursor is back at PC `108`, with loop index `2` and memory updated at `h[0]` and `h[1]`. -/
theorem validH1StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨2⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h1StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 1370 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH1StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first three `h` parser iterations.

The cursor is back at PC `108`, with loop index `3` and memory updated through `h[2]`. -/
theorem validH2StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨3⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h2StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 1576 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH2StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first four `h` parser iterations.

The cursor is back at PC `108`, with loop index `4` and memory updated through `h[3]`. -/
theorem validH3StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨4⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h3StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 1782 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH3StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first five `h` parser iterations.

The cursor is back at PC `108`, with loop index `5` and memory updated through `h[4]`. -/
theorem validH4StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨5⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h4StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 1988 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH4StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first six `h` parser iterations.

The cursor is back at PC `108`, with loop index `6` and memory updated through `h[5]`. -/
theorem validH5StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨6⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h5StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 2194 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH5StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first seven `h` parser iterations.

The cursor is back at PC `108`, with loop index `7` and memory updated through `h[6]`. -/
theorem validH6StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨7⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h6StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 2400 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH6StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed all eight `h` parser iterations.

The cursor is back at PC `108`, with loop index `8` and memory updated through `h[7]`.
The next bytecode branch exits the `h` parser loop. -/
theorem validH7StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨8⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h7StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 2606 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validH7StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have exited the `h` parser loop and are about to enter the `m` parser loop.

The cursor is PC `119`, immediately before the `m` loop-head `JUMPDEST`, with fresh loop index `0`
on top of the stack and memory updated through all eight parsed `h` words. -/
theorem validHLoopExitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨119⟩ [⟨0⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (h7StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 2633 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validHLoopExitPrefixGas
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
