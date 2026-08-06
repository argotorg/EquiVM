import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.Setup

/-!
# BLAKE2F valid-input setup wrappers: t words and final flag

Context-level wrappers for the t words and final-flag check.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid inputs have allocated and zero-initialized the `uint64[2]` array for parsed `t`.

The cursor is PC `100`, where the main wrapper resumes with the `t` array pointer above the `m`,
bytes, and `h` pointers. -/
theorem validTArrayPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨100⟩ [⟨1152⟩, ⟨640⟩, ⟨160⟩, ⟨128⟩, ⟨384⟩]
      (tArrayZeroMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 940 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validTArrayPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed the first `t` parser iteration.

The cursor is back at PC `130`, with loop index `1` and memory updated through `t[0]`. -/
theorem validT0StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨130⟩ [⟨1⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (t0StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6162 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validT0StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have completed both `t` parser iterations.

The cursor is back at PC `130`, with loop index `2` and memory updated through `t[1]`. -/
theorem validT1StoredPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨130⟩ [⟨2⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (t1StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6368 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validT1StoredPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have exited the `t` parser loop and are about to load the final-block flag.

The cursor is PC `140`, with memory updated through both parsed `t` words. -/
theorem validTLoopExitPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨140⟩ [⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (t1StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6393 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validTLoopExitPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have computed the bytecode final-flag rejection condition.

The cursor is PC `155`, immediately before the `JUMPI` that would reject flags greater than `1`.
The condition is still stated as the bytecode-level memory-loaded term
`parsedFinalFlagBranchCond`; the next bridge identifies it with the trusted calldata final flag. -/
theorem validFinalFlagCheckPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨155⟩ [⟨310⟩, parsedFinalFlagBranchCond ctx.executionEnv, ⟨384⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩,
        parsedFinalFlagWord ctx.executionEnv]
      (t1StoredMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 6423 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validFinalFlagCheckPrefixGas
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
