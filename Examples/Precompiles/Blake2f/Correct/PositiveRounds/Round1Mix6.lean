import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: round-1 third diagonal `mixG`

Context-level wrappers for the completed third diagonal round-1 `mixG` call on the multi-round
path.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with at least two rounds have completed the third diagonal
round-1 `mixG` call.

The cursor is PC `3070`, immediately after updating bytecode vector slots `v[2]`, `v[7]`,
`v[8]`, and `v[13]` with round-1 message arguments `m[11]` and `m[7]`.
Exact cumulative gas is `13216 + 93 + 321 + 93 + 321 = 14044`. -/
theorem validPositiveRound1Mix6DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 1 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3070⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round1Mix6Mem3 (round1Mix5ZeroMem ctx.executionEnv))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      ((((13216 + 93) + 321) + 93) + 321) := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound1Mix6DoneZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv hlen' hbyte
    (bytecodeRoundGuard_ne_zero_of_modelRounds_pos ctx.executionEnv hlen' (by omega))
    (bytecodeRound1Guard_ne_zero_of_modelRounds_gt_one ctx.executionEnv hlen' hrounds)

/-- Valid final-flag-`1` inputs with at least two rounds have completed the third diagonal
round-1 `mixG` call.

The cursor is PC `3070`, immediately after updating bytecode vector slots `v[2]`, `v[7]`,
`v[8]`, and `v[13]` with round-1 message arguments `m[11]` and `m[7]`.
Exact cumulative gas is `13243 + 93 + 321 + 93 + 321 = 14071`. -/
theorem validPositiveRound1Mix6DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 1 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3070⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round1Mix6Mem3 (round1Mix5OneMem ctx.executionEnv))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      ((((13243 + 93) + 321) + 93) + 321) := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound1Mix6DoneOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv hlen' hbyte
    (bytecodeRoundGuard_ne_zero_of_modelRounds_pos ctx.executionEnv hlen' (by omega))
    (bytecodeRound1Guard_ne_zero_of_modelRounds_gt_one ctx.executionEnv hlen' hrounds)

end Blake2f
