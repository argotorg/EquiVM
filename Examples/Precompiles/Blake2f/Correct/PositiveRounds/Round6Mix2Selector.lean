import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: round-6 third `mixG` argument setup

Context-level wrappers for the third round-6 `mixG` argument setup on the path with at least
seven rounds.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with at least seven rounds have prepared the third round-6
`mixG` call.

The cursor is PC `1969`, with packed round-6 SIGMA word `0xc51fed4a0763928b` and message
arguments `m[14]`/`m[13]`. Exact cumulative gas is `29425 + 93 = 29518`. -/
theorem validPositiveRound6Mix2ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 6 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1969⟩
      [round6M13Arg (round6Mix1ZeroMem ctx.executionEnv),
        round6M14Arg (round6Mix1ZeroMem ctx.executionEnv),
        ⟨2153⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round6Mix1ZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 29518 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound6Mix2ArgsZeroFlagPrefixGas
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
    (bytecodeRound4Guard_ne_zero_of_modelRounds_gt_four ctx.executionEnv hlen' (by omega))
    (bytecodeRound5Guard_ne_zero_of_modelRounds_gt_five ctx.executionEnv hlen' (by omega))
    (bytecodeRound6Guard_ne_zero_of_modelRounds_gt_six ctx.executionEnv hlen' hrounds)

/-- Valid final-flag-`1` inputs with at least seven rounds have prepared the third round-6
`mixG` call.

The cursor is PC `1969`, with packed round-6 SIGMA word `0xc51fed4a0763928b` and message
arguments `m[14]`/`m[13]`. Exact cumulative gas is `29452 + 93 = 29545`. -/
theorem validPositiveRound6Mix2ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 6 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1969⟩
      [round6M13Arg (round6Mix1OneMem ctx.executionEnv),
        round6M14Arg (round6Mix1OneMem ctx.executionEnv),
        ⟨2153⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round6Mix1OneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 29545 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound6Mix2ArgsOneFlagPrefixGas
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
    (bytecodeRound4Guard_ne_zero_of_modelRounds_gt_four ctx.executionEnv hlen' (by omega))
    (bytecodeRound5Guard_ne_zero_of_modelRounds_gt_five ctx.executionEnv hlen' (by omega))
    (bytecodeRound6Guard_ne_zero_of_modelRounds_gt_six ctx.executionEnv hlen' hrounds)

end Blake2f
