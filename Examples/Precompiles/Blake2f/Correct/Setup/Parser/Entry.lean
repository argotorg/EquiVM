import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.Setup

/-!
# BLAKE2F valid-input setup wrappers: entry/allocation

Context-level wrappers for validation, allocation, calldata copy, and array allocation.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid inputs pass the explicit EIP-152 fallback guards with exact cumulative gas `84`.

This is the context-level entry point for the remaining successful return proof. -/
theorem validValidationPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨30⟩ [] Reasoning.Theory.solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (ctx.createdAccounts, ctx.accountMap) k 84 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validValidationPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs also pass the compiler allocation helper for `bytes memory input = msg.data`.

The cursor is PC `46`, immediately before the wrapper stores the length word and executes
`CALLDATACOPY`; memory has the free pointer advanced to `0x180`, and the old free pointer `0x80`
is on the stack. -/
theorem validAllocationHelperPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨46⟩ [⟨128⟩] (Reasoning.Theory.solcBytesReturnAllocMem (UInt256.ofNat 213))
      (UInt256.ofNat 3) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 246 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validAllocationHelperPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs are materialized as Solidity `bytes memory` through the calldata-copy step.

The cursor is PC `59`, immediately before the compiler writes the trailing zero-padding word at
the non-word-aligned end of the 213-byte payload. -/
theorem validCalldataCopyPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨59⟩ [⟨128⟩, ⟨160⟩]
      (Reasoning.Theory.solcBytesSetCalldataMem ctx.executionEnv.calldata (UInt256.ofNat 213) ⟨0⟩)
      (UInt256.ofNat 12) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 325 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validCalldataCopyPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have been fully materialized as Solidity `bytes memory` and pass the
library-level length check.

The cursor is PC `76`, immediately before parsing the 213-byte EIP-152 fields. -/
theorem validBytesInputPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨76⟩ [⟨128⟩, ⟨160⟩]
      (Reasoning.Theory.solcBytesSetPaddedMem ctx.executionEnv.calldata (UInt256.ofNat 213) ⟨0⟩)
      (UInt256.ofNat 13) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 372 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validBytesInputPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have allocated and zero-initialized the first `uint64[8]` array for parsed `h`.

The cursor is PC `83`, where the main wrapper resumes with the `h` array pointer on the stack. -/
theorem validHArrayPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨83⟩ [⟨384⟩, ⟨128⟩, ⟨160⟩]
      (hArrayZeroMem ctx.executionEnv)
      (UInt256.ofNat 20) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 554 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validHArrayPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have allocated and zero-initialized the `uint64[16]` array for parsed `m`.

The cursor is PC `92`, where the main wrapper resumes with the `m` array pointer on the stack
above the materialized bytes pointer pair and the `h` array pointer. -/
theorem validMArrayPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨92⟩ [⟨640⟩, ⟨160⟩, ⟨128⟩, ⟨384⟩]
      (mArrayZeroMem ctx.executionEnv)
      (UInt256.ofNat 36) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 793 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validMArrayPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hflag

/-- Valid inputs have loaded the first input word, extracted the rounds field, and entered the
loop that parses the eight `h` words.

The cursor is PC `108`, with loop index `0` on top of the stack and the extracted round count kept
as `UInt256.shiftRight (inputFirstWord _) 224`. -/
theorem validRoundsLoadPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨108⟩ [⟨0⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩]
      (tArrayZeroMem ctx.executionEnv)
      (UInt256.ofNat 38) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 958 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validRoundsLoadPrefixGas
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
