import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopGuard
import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopUpdate
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds
import Examples.Precompiles.Blake2f.Fallback.ModelBridge

/-!
# BLAKE2F positive-round wrappers: round-6 completion

Context-level wrappers after round 6 has completed and control has returned to the rounds-loop
guard with loop index `7`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with at least seven rounds have completed round 6 and returned to
the rounds-loop guard.

The cursor is PC `1370` with loop index `7`. Exact cumulative gas is `31906`. -/
theorem validPositiveRound6DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 6 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1370⟩
      [⟨7⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6DoneZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 31906 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound6DoneZeroFlagPrefixGas
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

/-- Valid final-flag-`1` inputs with at least seven rounds have completed round 6 and returned to
the rounds-loop guard.

The cursor is PC `1370` with loop index `7`. Exact cumulative gas is `31933`. -/
theorem validPositiveRound6DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 6 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1370⟩
      [⟨7⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6DoneOneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 31933 := by
  obtain ⟨hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState] using validPositiveRound6DoneOneFlagPrefixGas
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

/-- Valid final-flag-`0` inputs with exactly seven rounds exit the compression loop after
round 6.

This uses the parametric loop guard from `Correct.PositiveRounds.LoopGuard`, rather than adding a
new concrete `Guard7` trace file. Exact cumulative gas is `31906 + 23 = 31929`. -/
theorem validPositiveRoundAfter6GuardExitZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 7) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundExitPc
      (positiveRoundHeaderStack ctx.executionEnv 7)
      (round6DoneZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 31929 := by
  have hprefix := validPositiveRound6DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte (by omega)
  simpa using positiveRoundGuardExitOfModelRoundsEq
    ctx hvalid (i := 7) (mem := round6DoneZeroMem ctx.executionEnv) (startGas := 31906)
    hrounds
    (by simpa [positiveRoundHeaderRDxContext] using hprefix)

/-- Valid final-flag-`1` inputs with exactly seven rounds exit the compression loop after
round 6.

This uses the parametric loop guard from `Correct.PositiveRounds.LoopGuard`, rather than adding a
new concrete `Guard7` trace file. Exact cumulative gas is `31933 + 23 = 31956`. -/
theorem validPositiveRoundAfter6GuardExitOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : Model.rounds ctx.executionEnv.calldata = 7) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundExitPc
      (positiveRoundHeaderStack ctx.executionEnv 7)
      (round6DoneOneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 31956 := by
  have hprefix := validPositiveRound6DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte (by omega)
  simpa using positiveRoundGuardExitOfModelRoundsEq
    ctx hvalid (i := 7) (mem := round6DoneOneMem ctx.executionEnv) (startGas := 31933)
    hrounds
    (by simpa [positiveRoundHeaderRDxContext] using hprefix)

/-- Valid final-flag-`0` inputs with more than seven rounds continue to the next round body after
round 6.

This is the current arbitrary-round frontier: control is at PC `1445` with loop index `7`; the
next proof should be a parametric one-round body theorem rather than a concrete round-7 unroll.
Exact cumulative gas is `31906 + 23 = 31929`. -/
theorem validPositiveRoundAfter6GuardContinueZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundBodyPc
      (positiveRoundHeaderStack ctx.executionEnv 7)
      (round6DoneZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 31929 := by
  have hprefix := validPositiveRound6DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte (by omega)
  simpa using positiveRoundGuardContinueOfModelRoundsGt
    ctx hvalid (i := 7) (mem := round6DoneZeroMem ctx.executionEnv) (startGas := 31906)
    hrounds
    (by simpa [positiveRoundHeaderRDxContext] using hprefix)

/-- Valid final-flag-`1` inputs with more than seven rounds continue to the next round body after
round 6.

This is the current arbitrary-round frontier: control is at PC `1445` with loop index `7`; the
next proof should be a parametric one-round body theorem rather than a concrete round-7 unroll.
Exact cumulative gas is `31933 + 23 = 31956`. -/
theorem validPositiveRoundAfter6GuardContinueOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundBodyPc
      (positiveRoundHeaderStack ctx.executionEnv 7)
      (round6DoneOneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 31956 := by
  have hprefix := validPositiveRound6DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte (by omega)
  simpa using positiveRoundGuardContinueOfModelRoundsGt
    ctx hvalid (i := 7) (mem := round6DoneOneMem ctx.executionEnv) (startGas := 31933)
    hrounds
    (by simpa [positiveRoundHeaderRDxContext] using hprefix)

/-- Valid final-flag-`0` inputs with more than seven rounds execute the parametric SIGMA selector
for loop index `7` and reach the shared first `mixG` entry.

This advances the old round-6 frontier using the arbitrary-round selector theorem, without adding
a concrete round-7 unroll. Exact cumulative gas is `31929 + 322 = 32251`. -/
theorem validPositiveRoundAfter6SelectorZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack ctx.executionEnv 7 (round6DoneZeroMem ctx.executionEnv))
      (round6DoneZeroMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 32251 := by
  obtain ⟨k0, hbody⟩ :=
    validPositiveRoundAfter6GuardContinueZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨_hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  obtain ⟨k1, hmix0⟩ :=
    positiveRoundResidue7SelectorTraceRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := round6DoneZeroMem ctx.executionEnv)
      (i := 7)
      (C := 31929)
      (k := k0)
      (round6DoneZeroMem_size hlen')
      (by norm_num [UInt256.size])
      (by norm_num)
      hbody
  exact ⟨k1, by simpa [sigmaSelectorToMix0Gas] using hmix0⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the parametric SIGMA selector
for loop index `7` and reach the shared first `mixG` entry.

This advances the old round-6 frontier using the arbitrary-round selector theorem, without adding
a concrete round-7 unroll. Exact cumulative gas is `31956 + 322 = 32278`. -/
theorem validPositiveRoundAfter6SelectorOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack ctx.executionEnv 7 (round6DoneOneMem ctx.executionEnv))
      (round6DoneOneMem ctx.executionEnv)
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 32278 := by
  obtain ⟨k0, hbody⟩ :=
    validPositiveRoundAfter6GuardContinueOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨_hwv, _hsize⟩ := haccepts
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  obtain ⟨k1, hmix0⟩ :=
    positiveRoundResidue7SelectorTraceRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := round6DoneOneMem ctx.executionEnv)
      (i := 7)
      (C := 31956)
      (k := k0)
      (round6DoneOneMem_size hlen')
      (by norm_num [UInt256.size])
      (by norm_num)
      hbody
  exact ⟨k1, by simpa [sigmaSelectorToMix0Gas] using hmix0⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the parametric selector and
the shared first `mixG` body for loop index `7`.

The `mixG` body proof used here is the arbitrary-index proof from `LoopMix0`, not a concrete
round-7 unroll. Exact cumulative gas is `32251 + 315 = 32566`. -/
theorem validPositiveRoundAfter6Mix0DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1693⟩
      [sigmaPackedWord 7, ⟨3109⟩, ⟨3292⟩, ⟨7⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 32566 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6SelectorZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  obtain ⟨k1, hmix0⟩ :=
    positiveRoundMix0BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := round6DoneZeroMem ctx.executionEnv)
      (i := 7)
      (C := 32251)
      (k := k0)
      (round6DoneZeroMem_size hlen')
      hprefix
  exact ⟨k1, by simpa using hmix0⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the parametric selector and
the shared first `mixG` body for loop index `7`.

The `mixG` body proof used here is the arbitrary-index proof from `LoopMix0`, not a concrete
round-7 unroll. Exact cumulative gas is `32278 + 315 = 32593`. -/
theorem validPositiveRoundAfter6Mix0DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1693⟩
      [sigmaPackedWord 7, ⟨3109⟩, ⟨3292⟩, ⟨7⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
        ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 32593 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6SelectorOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  obtain ⟨k1, hmix0⟩ :=
    positiveRoundMix0BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := round6DoneOneMem ctx.executionEnv)
      (i := 7)
      (C := 32278)
      (k := k0)
      (round6DoneOneMem_size hlen')
      hprefix
  exact ⟨k1, by simpa using hmix0⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic setup for the
second `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix1Selector`. Exact cumulative
gas is `32566 + 93 = 32659`. -/
theorem validPositiveRoundAfter6Mix1ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1739⟩
      (positiveRoundMix1EntryStack ctx.executionEnv 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 32659 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix0DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  obtain ⟨k1, hmix1⟩ :=
    positiveRoundMix1ArgsFromMix0Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))
      (i := 7)
      (C := 32566)
      (k := k0)
      hmem
      (by simpa [positiveRoundAfterMix0Stack] using hprefix)
  exact ⟨k1, by simpa using hmix1⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic setup for the
second `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix1Selector`. Exact cumulative
gas is `32593 + 93 = 32686`. -/
theorem validPositiveRoundAfter6Mix1ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1739⟩
      (positiveRoundMix1EntryStack ctx.executionEnv 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 32686 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix0DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  obtain ⟨k1, hmix1⟩ :=
    positiveRoundMix1ArgsFromMix0Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))
      (i := 7)
      (C := 32593)
      (k := k0)
      hmem
      (by simpa [positiveRoundAfterMix0Stack] using hprefix)
  exact ⟨k1, by simpa using hmix1⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic second `mixG`
body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix1`. Exact cumulative gas is
`32659 + 321 = 32980`. -/
theorem validPositiveRoundAfter6Mix1DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1923⟩
      (positiveRoundAfterMix1Stack ctx.executionEnv 7)
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 32980 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix1ArgsZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  obtain ⟨k1, hmix1⟩ :=
    positiveRoundMix1BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))
      (i := 7)
      (C := 32659)
      (k := k0)
      hmem
      hprefix
  exact ⟨k1, by simpa using hmix1⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic second `mixG`
body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix1`. Exact cumulative gas is
`32686 + 321 = 33007`. -/
theorem validPositiveRoundAfter6Mix1DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1923⟩
      (positiveRoundAfterMix1Stack ctx.executionEnv 7)
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33007 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix1ArgsOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  obtain ⟨k1, hmix1⟩ :=
    positiveRoundMix1BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))
      (i := 7)
      (C := 32686)
      (k := k0)
      hmem
      hprefix
  exact ⟨k1, by simpa using hmix1⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic setup for the
third `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix2Selector`. Exact cumulative
gas is `32980 + 93 = 33073`. -/
theorem validPositiveRoundAfter6Mix2ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1969⟩
      (positiveRoundMix2EntryStack ctx.executionEnv 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33073 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix1DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  obtain ⟨k1, hmix2⟩ :=
    positiveRoundMix2ArgsFromMix1Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))
      (i := 7)
      (C := 32980)
      (k := k0)
      hmem
      hprefix
  exact ⟨k1, by simpa using hmix2⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic setup for the
third `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix2Selector`. Exact cumulative
gas is `33007 + 93 = 33100`. -/
theorem validPositiveRoundAfter6Mix2ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1969⟩
      (positiveRoundMix2EntryStack ctx.executionEnv 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33100 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix1DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  obtain ⟨k1, hmix2⟩ :=
    positiveRoundMix2ArgsFromMix1Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))
      (i := 7)
      (C := 33007)
      (k := k0)
      hmem
      hprefix
  exact ⟨k1, by simpa using hmix2⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic third `mixG`
body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix2`. Exact cumulative gas is
`33073 + 321 = 33394`. -/
theorem validPositiveRoundAfter6Mix2DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2153⟩
      (positiveRoundAfterMix2Stack ctx.executionEnv 7)
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33394 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix2ArgsZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  obtain ⟨k1, hmix2⟩ :=
    positiveRoundMix2BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))
      (i := 7)
      (C := 33073)
      (k := k0)
      hmem1
      hprefix
  exact ⟨k1, by simpa using hmix2⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic third `mixG`
body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix2`. Exact cumulative gas is
`33100 + 321 = 33421`. -/
theorem validPositiveRoundAfter6Mix2DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2153⟩
      (positiveRoundAfterMix2Stack ctx.executionEnv 7)
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33421 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix2ArgsOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  obtain ⟨k1, hmix2⟩ :=
    positiveRoundMix2BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))
      (i := 7)
      (C := 33100)
      (k := k0)
      hmem1
      hprefix
  exact ⟨k1, by simpa using hmix2⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic setup for the
fourth `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix3Selector`. Exact cumulative
gas is `33394 + 93 = 33487`. -/
theorem validPositiveRoundAfter6Mix3ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2199⟩
      (positiveRoundMix3EntryStack ctx.executionEnv 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33487 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix2DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  obtain ⟨k1, hmix3⟩ :=
    positiveRoundMix3ArgsFromMix2Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))
      (i := 7)
      (C := 33394)
      (k := k0)
      hmem2
      hprefix
  exact ⟨k1, by simpa using hmix3⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic setup for the
fourth `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix3Selector`. Exact cumulative
gas is `33421 + 93 = 33514`. -/
theorem validPositiveRoundAfter6Mix3ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2199⟩
      (positiveRoundMix3EntryStack ctx.executionEnv 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33514 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix2DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  obtain ⟨k1, hmix3⟩ :=
    positiveRoundMix3ArgsFromMix2Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))
      (i := 7)
      (C := 33421)
      (k := k0)
      hmem2
      hprefix
  exact ⟨k1, by simpa using hmix3⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic fourth `mixG`
body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix3`. Exact cumulative gas is
`33487 + 321 = 33808`. -/
theorem validPositiveRoundAfter6Mix3DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2383⟩
      (positiveRoundAfterMix3Stack ctx.executionEnv 7)
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33808 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix3ArgsZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  obtain ⟨k1, hmix3⟩ :=
    positiveRoundMix3BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))
      (i := 7)
      (C := 33487)
      (k := k0)
      hmem2
      hprefix
  exact ⟨k1, by simpa using hmix3⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic fourth `mixG`
body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix3`. Exact cumulative gas is
`33514 + 321 = 33835`. -/
theorem validPositiveRoundAfter6Mix3DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2383⟩
      (positiveRoundAfterMix3Stack ctx.executionEnv 7)
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33835 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix3ArgsOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  obtain ⟨k1, hmix3⟩ :=
    positiveRoundMix3BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))
      (i := 7)
      (C := 33514)
      (k := k0)
      hmem2
      hprefix
  exact ⟨k1, by simpa using hmix3⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic setup for the
first diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix4Selector`. Exact cumulative
gas is `33808 + 93 = 33901`. -/
theorem validPositiveRoundAfter6Mix4ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2429⟩
      (positiveRoundMix4EntryStack ctx.executionEnv 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33901 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix3DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  obtain ⟨k1, hmix4⟩ :=
    positiveRoundMix4ArgsFromMix3Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))
      (i := 7)
      (C := 33808)
      (k := k0)
      hmem3
      hprefix
  exact ⟨k1, by simpa using hmix4⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic setup for the
first diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix4Selector`. Exact cumulative
gas is `33835 + 93 = 33928`. -/
theorem validPositiveRoundAfter6Mix4ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2429⟩
      (positiveRoundMix4EntryStack ctx.executionEnv 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 33928 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix3DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  obtain ⟨k1, hmix4⟩ :=
    positiveRoundMix4ArgsFromMix3Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))
      (i := 7)
      (C := 33835)
      (k := k0)
      hmem3
      hprefix
  exact ⟨k1, by simpa using hmix4⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic first diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix4`. Exact cumulative gas is
`33901 + 315 = 34216`. -/
theorem validPositiveRoundAfter6Mix4DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2610⟩
      (positiveRoundAfterMix4Stack ctx.executionEnv 7)
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34216 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix4ArgsZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  obtain ⟨k1, hmix4⟩ :=
    positiveRoundMix4BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))
      (i := 7)
      (C := 33901)
      (k := k0)
      hmem3
      hprefix
  exact ⟨k1, by simpa using hmix4⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic first diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix4`. Exact cumulative gas is
`33928 + 315 = 34243`. -/
theorem validPositiveRoundAfter6Mix4DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2610⟩
      (positiveRoundAfterMix4Stack ctx.executionEnv 7)
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34243 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix4ArgsOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  obtain ⟨k1, hmix4⟩ :=
    positiveRoundMix4BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))
      (i := 7)
      (C := 33928)
      (k := k0)
      hmem3
      hprefix
  exact ⟨k1, by simpa using hmix4⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic setup for the
second diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix5Selector`. Exact cumulative
gas is `34216 + 93 = 34309`. -/
theorem validPositiveRoundAfter6Mix5ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2656⟩
      (positiveRoundMix5EntryStack ctx.executionEnv 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34309 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix4DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  obtain ⟨k1, hmix5⟩ :=
    positiveRoundMix5ArgsFromMix4Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))
      (i := 7)
      (C := 34216)
      (k := k0)
      hmem4
      hprefix
  exact ⟨k1, by simpa using hmix5⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic setup for the
second diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix5Selector`. Exact cumulative
gas is `34243 + 93 = 34336`. -/
theorem validPositiveRoundAfter6Mix5ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2656⟩
      (positiveRoundMix5EntryStack ctx.executionEnv 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34336 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix4DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  obtain ⟨k1, hmix5⟩ :=
    positiveRoundMix5ArgsFromMix4Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))
      (i := 7)
      (C := 34243)
      (k := k0)
      hmem4
      hprefix
  exact ⟨k1, by simpa using hmix5⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic second diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix5`. Exact cumulative gas is
`34309 + 321 = 34630`. -/
theorem validPositiveRoundAfter6Mix5DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2840⟩
      (positiveRoundAfterMix5Stack ctx.executionEnv 7)
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34630 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix5ArgsZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  obtain ⟨k1, hmix5⟩ :=
    positiveRoundMix5BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))
      (i := 7)
      (C := 34309)
      (k := k0)
      hmem4
      hprefix
  exact ⟨k1, by simpa using hmix5⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic second diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix5`. Exact cumulative gas is
`34336 + 321 = 34657`. -/
theorem validPositiveRoundAfter6Mix5DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2840⟩
      (positiveRoundAfterMix5Stack ctx.executionEnv 7)
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34657 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix5ArgsOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  obtain ⟨k1, hmix5⟩ :=
    positiveRoundMix5BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))
      (i := 7)
      (C := 34336)
      (k := k0)
      hmem4
      hprefix
  exact ⟨k1, by simpa using hmix5⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic setup for the
third diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix6Selector`. Exact cumulative
gas is `34630 + 93 = 34723`. -/
theorem validPositiveRoundAfter6Mix6ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2886⟩
      (positiveRoundMix6EntryStack ctx.executionEnv 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))))
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34723 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix5DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  obtain ⟨k1, hmix6⟩ :=
    positiveRoundMix6ArgsFromMix5Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))
      (i := 7)
      (C := 34630)
      (k := k0)
      hmem5
      hprefix
  exact ⟨k1, by simpa using hmix6⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic setup for the
third diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix6Selector`. Exact cumulative
gas is `34657 + 93 = 34750`. -/
theorem validPositiveRoundAfter6Mix6ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨2886⟩
      (positiveRoundMix6EntryStack ctx.executionEnv 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))))
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 34750 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix5DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  obtain ⟨k1, hmix6⟩ :=
    positiveRoundMix6ArgsFromMix5Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))
      (i := 7)
      (C := 34657)
      (k := k0)
      hmem5
      hprefix
  exact ⟨k1, by simpa using hmix6⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic third diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix6`. Exact cumulative gas is
`34723 + 321 = 35044`. -/
theorem validPositiveRoundAfter6Mix6DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3070⟩
      (positiveRoundAfterMix6Stack ctx.executionEnv 7)
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35044 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix6ArgsZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  obtain ⟨k1, hmix6⟩ :=
    positiveRoundMix6BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))
      (i := 7)
      (C := 34723)
      (k := k0)
      hmem5
      hprefix
  exact ⟨k1, by simpa using hmix6⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic third diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix6`. Exact cumulative gas is
`34750 + 321 = 35071`. -/
theorem validPositiveRoundAfter6Mix6DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3070⟩
      (positiveRoundAfterMix6Stack ctx.executionEnv 7)
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35071 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix6ArgsOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  obtain ⟨k1, hmix6⟩ :=
    positiveRoundMix6BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))
      (i := 7)
      (C := 34750)
      (k := k0)
      hmem5
      hprefix
  exact ⟨k1, by simpa using hmix6⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic setup for the
fourth diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix7Selector`. Exact cumulative
gas is `35044 + 84 = 35128`. -/
theorem validPositiveRoundAfter6Mix7ArgsZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3109⟩
      (positiveRoundMix7EntryStack ctx.executionEnv 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))))
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35128 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix6DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  have hmem6 :
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))).size = 1984 :=
    positiveRoundMix6Mem3_size hmem5
  obtain ⟨k1, hmix7⟩ :=
    positiveRoundMix7ArgsFromMix6Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))))
      (i := 7)
      (C := 35044)
      (k := k0)
      hmem6
      hprefix
  exact ⟨k1, by simpa using hmix7⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic setup for the
fourth diagonal `mixG` call of loop index `7`.

This uses the arbitrary-index argument-selector proof from `LoopMix7Selector`. Exact cumulative
gas is `35071 + 84 = 35155`. -/
theorem validPositiveRoundAfter6Mix7ArgsOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3109⟩
      (positiveRoundMix7EntryStack ctx.executionEnv 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))))
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35155 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix6DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  have hmem6 :
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))).size = 1984 :=
    positiveRoundMix6Mem3_size hmem5
  obtain ⟨k1, hmix7⟩ :=
    positiveRoundMix7ArgsFromMix6Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))))
      (i := 7)
      (C := 35071)
      (k := k0)
      hmem6
      hprefix
  exact ⟨k1, by simpa using hmix7⟩

/-- Valid final-flag-`0` inputs with more than seven rounds execute the generic fourth diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix7`. Exact cumulative gas is
`35128 + 318 = 35446`. -/
theorem validPositiveRoundAfter6Mix7DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3292⟩
      (positiveRoundAfterMix7Stack ctx.executionEnv 7)
      (positiveRoundMix7Mem3 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35446 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix7ArgsZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneZeroMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  have hmem6 :
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))).size = 1984 :=
    positiveRoundMix6Mem3_size hmem5
  obtain ⟨k1, hmix7⟩ :=
    positiveRoundMix7BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv))))))))
      (i := 7)
      (C := 35128)
      (k := k0)
      hmem6
      hprefix
  exact ⟨k1, by simpa using hmix7⟩

/-- Valid final-flag-`1` inputs with more than seven rounds execute the generic fourth diagonal
`mixG` body for loop index `7`.

This uses the arbitrary-index body proof from `LoopMix7`. Exact cumulative gas is
`35155 + 318 = 35473`. -/
theorem validPositiveRoundAfter6Mix7DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨3292⟩
      (positiveRoundAfterMix7Stack ctx.executionEnv 7)
      (positiveRoundMix7Mem3 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35473 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix7ArgsOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  have hmem0 :
      (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)).size = 1984 :=
    positiveRoundMix0Mem3_size (round6DoneOneMem_size hlen')
  have hmem1 :
      (positiveRoundMix1Mem3 7
        (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  have hmem2 :
      (positiveRoundMix2Mem3 7
        (positiveRoundMix1Mem3 7
          (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  have hmem3 :
      (positiveRoundMix3Mem3 7
        (positiveRoundMix2Mem3 7
          (positiveRoundMix1Mem3 7
            (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  have hmem4 :
      (positiveRoundMix4Mem3 7
        (positiveRoundMix3Mem3 7
          (positiveRoundMix2Mem3 7
            (positiveRoundMix1Mem3 7
              (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  have hmem5 :
      (positiveRoundMix5Mem3 7
        (positiveRoundMix4Mem3 7
          (positiveRoundMix3Mem3 7
            (positiveRoundMix2Mem3 7
              (positiveRoundMix1Mem3 7
                (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  have hmem6 :
      (positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))).size = 1984 :=
    positiveRoundMix6Mem3_size hmem5
  obtain ⟨k1, hmix7⟩ :=
    positiveRoundMix7BodyFromEntryStackRaw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix6Mem3 7
        (positiveRoundMix5Mem3 7
          (positiveRoundMix4Mem3 7
            (positiveRoundMix3Mem3 7
              (positiveRoundMix2Mem3 7
                (positiveRoundMix1Mem3 7
                  (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv))))))))
      (i := 7)
      (C := 35155)
      (k := k0)
      hmem6
      hprefix
  exact ⟨k1, by simpa using hmix7⟩

/-- Valid final-flag-`0` inputs with more than seven rounds complete loop index `7` and return
to the rounds-loop guard at index `8`.

This uses the arbitrary-index loop-update proof from `LoopUpdate`. Exact cumulative gas is
`35446 + 15 = 35461`. -/
theorem validPositiveRoundAfter7DoneZeroFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1370⟩
      (positiveRoundAfterUpdateStack ctx.executionEnv 7)
      (positiveRoundMix7Mem3 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35461 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix7DoneZeroFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨k1, hupdate⟩ :=
    positiveRoundUpdateFromMix7Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix7Mem3 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneZeroMem ctx.executionEnv)))))))))
      (i := 7)
      (C := 35446)
      (k := k0)
      (by native_decide)
      hprefix
  exact ⟨k1, by simpa using hupdate⟩

/-- Valid final-flag-`1` inputs with more than seven rounds complete loop index `7` and return
to the rounds-loop guard at index `8`.

This uses the arbitrary-index loop-update proof from `LoopUpdate`. Exact cumulative gas is
`35473 + 15 = 35488`. -/
theorem validPositiveRoundAfter7DoneOneFlagPrefix
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1)
    (hrounds : 7 < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1370⟩
      (positiveRoundAfterUpdateStack ctx.executionEnv 7)
      (positiveRoundMix7Mem3 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))))
      (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k 35488 := by
  obtain ⟨k0, hprefix⟩ :=
    validPositiveRoundAfter6Mix7DoneOneFlagPrefix ctx hcode haccepts hvalid hbyte hrounds
  obtain ⟨k1, hupdate⟩ :=
    positiveRoundUpdateFromMix7Raw
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      (mem := positiveRoundMix7Mem3 7
        (positiveRoundMix6Mem3 7
          (positiveRoundMix5Mem3 7
            (positiveRoundMix4Mem3 7
              (positiveRoundMix3Mem3 7
                (positiveRoundMix2Mem3 7
                  (positiveRoundMix1Mem3 7
                    (positiveRoundMix0Mem3 7 (round6DoneOneMem ctx.executionEnv)))))))))
      (i := 7)
      (C := 35473)
      (k := k0)
      (by native_decide)
      hprefix
  exact ⟨k1, by simpa using hupdate⟩

end Blake2f
