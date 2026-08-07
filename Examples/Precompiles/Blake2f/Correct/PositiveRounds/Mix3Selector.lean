import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: fourth `mixG` argument setup

Context-level wrappers for the fourth round-0 `mixG` argument setup.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with positive rounds have prepared the fourth round-0 `mixG`.

The cursor is PC `2199`, immediately before the shared body that updates bytecode vector slots
`v[3]`, `v[7]`, `v[11]`, and `v[15]`. Exact cumulative gas is `9064`. -/
theorem validPositiveRoundMix3ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 0 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2199⟩
      [firstRoundM7Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem ctx.executionEnv)))),
        firstRoundM6Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem ctx.executionEnv)))),
        ⟨2383⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem ctx.executionEnv))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 9064 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validPositiveRoundMix3ArgsZeroFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte
    (bytecodeRoundGuard_ne_zero_of_modelRounds_pos ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

/-- Valid final-flag-`1` inputs with positive rounds have prepared the fourth round-0 `mixG`.

The cursor is PC `2199`, preserving the previous vector updates. Exact cumulative gas is `9091`. -/
theorem validPositiveRoundMix3ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 0 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2199⟩
      [firstRoundM7Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem ctx.executionEnv)))),
        firstRoundM6Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem ctx.executionEnv)))),
        ⟨2383⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem ctx.executionEnv))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 9091 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validPositiveRoundMix3ArgsOneFlagPrefixGas
    (cA := ctx.createdAccounts)
    (gh := ctx.genesisBlockHeader)
    (bl := ctx.blocks)
    (σ := ctx.accountMap)
    (σ₀ := ctx.originalAccountMap)
    (A := ctx.substate)
    (I := ctx.executionEnv)
    (g := ctx.gas)
    hcode hwv (by simpa [Model.inputLength] using hlen) hbyte
    (bytecodeRoundGuard_ne_zero_of_modelRounds_pos ctx.executionEnv
      (by simpa [Model.inputLength] using hlen) hrounds)

end Blake2f
