import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: round-4 third diagonal `mixG` argument setup

Context-level wrappers for the third diagonal round-4 `mixG` argument setup on the path with at
least five rounds.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with at least five rounds have prepared the third diagonal
round-4 `mixG` call.

The cursor is PC `2886`, with packed round-4 SIGMA word `0x905724afe1bc683d` and message
arguments `m[6]`/`m[8]`. Exact cumulative gas is `24031 + 93 = 24124`. -/
theorem validPositiveRound4Mix6ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 4 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2886⟩
      [round4M8Arg (round4Mix5ZeroMem ctx.executionEnv),
        round4M6Arg (round4Mix5ZeroMem ctx.executionEnv),
        ⟨3070⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round4Mix5ZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 24124 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound4Mix6ArgsZeroFlagPrefixGas
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
    (bytecodeRound2Guard_ne_zero_of_modelRounds_gt_two ctx.executionEnv hlen' (by omega))
    (bytecodeRound3Guard_ne_zero_of_modelRounds_gt_three ctx.executionEnv hlen' (by omega))
    (bytecodeRound4Guard_ne_zero_of_modelRounds_gt_four ctx.executionEnv hlen' hrounds)

/-- Valid final-flag-`1` inputs with at least five rounds have prepared the third diagonal
round-4 `mixG` call.

The cursor is PC `2886`, with packed round-4 SIGMA word `0x905724afe1bc683d` and message
arguments `m[6]`/`m[8]`. Exact cumulative gas is `24058 + 93 = 24151`. -/
theorem validPositiveRound4Mix6ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 4 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2886⟩
      [round4M8Arg (round4Mix5OneMem ctx.executionEnv),
        round4M6Arg (round4Mix5OneMem ctx.executionEnv),
        ⟨3070⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round4Mix5OneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 24151 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound4Mix6ArgsOneFlagPrefixGas
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
    (bytecodeRound2Guard_ne_zero_of_modelRounds_gt_two ctx.executionEnv hlen' (by omega))
    (bytecodeRound3Guard_ne_zero_of_modelRounds_gt_three ctx.executionEnv hlen' (by omega))
    (bytecodeRound4Guard_ne_zero_of_modelRounds_gt_four ctx.executionEnv hlen' hrounds)

end Blake2f
