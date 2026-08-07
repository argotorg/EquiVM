import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: round-2 fourth `mixG` argument setup

Context-level wrappers for the fourth round-2 `mixG` argument setup on the path with at least
three rounds.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with at least three rounds have prepared the fourth round-2
`mixG` call.

The cursor is PC `2199`, with packed round-2 SIGMA word `0xb8c052fdae367194` and message
arguments `m[15]`/`m[13]`. Exact cumulative gas is `15839 + 93 = 15932`. -/
theorem validPositiveRound2Mix3ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 2 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2199⟩
      [round2M13Arg (round2Mix2ZeroMem ctx.executionEnv),
        round2M15Arg (round2Mix2ZeroMem ctx.executionEnv),
        ⟨2383⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round2Mix2ZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 15932 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound2Mix3ArgsZeroFlagPrefixGas
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
    (bytecodeRound1Guard_ne_zero_of_modelRounds_gt_one ctx.executionEnv hlen' (by omega))
    (bytecodeRound2Guard_ne_zero_of_modelRounds_gt_two ctx.executionEnv hlen' hrounds)

/-- Valid final-flag-`1` inputs with at least three rounds have prepared the fourth round-2
`mixG` call.

The cursor is PC `2199`, with packed round-2 SIGMA word `0xb8c052fdae367194` and message
arguments `m[15]`/`m[13]`. Exact cumulative gas is `15866 + 93 = 15959`. -/
theorem validPositiveRound2Mix3ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 2 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2199⟩
      [round2M13Arg (round2Mix2OneMem ctx.executionEnv),
        round2M15Arg (round2Mix2OneMem ctx.executionEnv),
        ⟨2383⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round2Mix2OneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 15959 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound2Mix3ArgsOneFlagPrefixGas
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
    (bytecodeRound1Guard_ne_zero_of_modelRounds_gt_one ctx.executionEnv hlen' (by omega))
    (bytecodeRound2Guard_ne_zero_of_modelRounds_gt_two ctx.executionEnv hlen' hrounds)

end Blake2f
