import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: third `mixG` argument setup

Context-level wrappers for the third round-0 `mixG` argument setup.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with positive rounds have prepared the third round-0 `mixG`.

The cursor is PC `1969`, immediately before the shared body that updates bytecode vector slots
`v[2]`, `v[6]`, `v[10]`, and `v[14]`. Exact cumulative gas is `8650`. -/
theorem validPositiveRoundMix2ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 0 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1969⟩
      [firstRoundM5Arg (secondMixMem3 (firstMixMem3 (v13MixedMem ctx.executionEnv))),
        firstRoundM4Arg (secondMixMem3 (firstMixMem3 (v13MixedMem ctx.executionEnv))),
        ⟨2153⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (secondMixMem3 (firstMixMem3 (v13MixedMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8650 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validPositiveRoundMix2ArgsZeroFlagPrefixGas
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

/-- Valid final-flag-`1` inputs with positive rounds have prepared the third round-0 `mixG`.

The cursor is PC `1969`, preserving the previous vector updates. Exact cumulative gas is `8677`. -/
theorem validPositiveRoundMix2ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 0 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1969⟩
      [firstRoundM5Arg (secondMixMem3 (firstMixMem3 (v14FinalFlagMem ctx.executionEnv))),
        firstRoundM4Arg (secondMixMem3 (firstMixMem3 (v14FinalFlagMem ctx.executionEnv))),
        ⟨2153⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩, ⟨1472⟩,
        ⟨168⟩, ⟨1216⟩]
      (secondMixMem3 (firstMixMem3 (v14FinalFlagMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 8677 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  simpa [BytecodeContext.initialState] using validPositiveRoundMix2ArgsOneFlagPrefixGas
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
