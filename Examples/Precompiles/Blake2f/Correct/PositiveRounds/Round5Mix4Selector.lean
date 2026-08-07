import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: round-5 first diagonal `mixG` argument setup

Context-level wrappers for the first diagonal round-5 `mixG` argument setup on the path with at
least six rounds.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with at least six rounds have prepared the first diagonal
round-5 `mixG` call.

The cursor is PC `2429`, with packed round-5 SIGMA word `0x2c6a0b834d75fe19` and message
arguments `m[4]`/`m[13]`. Exact cumulative gas is `26720 + 93 = 26813`. -/
theorem validPositiveRound5Mix4ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 5 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2429⟩
      [round5M13Arg (round5Mix3ZeroMem ctx.executionEnv),
        round5M4Arg (round5Mix3ZeroMem ctx.executionEnv),
        ⟨2610⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round5Mix3ZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 26813 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound5Mix4ArgsZeroFlagPrefixGas
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
    (bytecodeRound5Guard_ne_zero_of_modelRounds_gt_five ctx.executionEnv hlen' hrounds)

/-- Valid final-flag-`1` inputs with at least six rounds have prepared the first diagonal
round-5 `mixG` call.

The cursor is PC `2429`, with packed round-5 SIGMA word `0x2c6a0b834d75fe19` and message
arguments `m[4]`/`m[13]`. Exact cumulative gas is `26747 + 93 = 26840`. -/
theorem validPositiveRound5Mix4ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 5 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2429⟩
      [round5M13Arg (round5Mix3OneMem ctx.executionEnv),
        round5M4Arg (round5Mix3OneMem ctx.executionEnv),
        ⟨2610⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (round5Mix3OneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 26840 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound5Mix4ArgsOneFlagPrefixGas
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
    (bytecodeRound5Guard_ne_zero_of_modelRounds_gt_five ctx.executionEnv hlen' hrounds)

end Blake2f
