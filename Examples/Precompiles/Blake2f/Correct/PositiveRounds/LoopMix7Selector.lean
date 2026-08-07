import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix6

/-!
# BLAKE2F positive-round arbitrary fourth diagonal `mixG` argument setup

This file factors the bytecode from PC `3070` to PC `3109`.  It extracts
`SIGMA[i % 10][14]` and `SIGMA[i % 10][15]`, loads the selected message words, and prepares the
fourth diagonal shared `mixG` call.  The theorem is parametric in the loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `3109`, with the fourth diagonal `mixG` arguments prepared. -/
def positiveRoundMix7EntryStack (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    List UInt256 :=
  [sigmaMessageArg mem i 15, sigmaMessageArg mem i 14, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundMix7EntryStack_length
    (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    (positiveRoundMix7EntryStack I i mem).length = 11 := by
  simp [positiveRoundMix7EntryStack]

private theorem sigmaPackedWord_offset14 (i : Nat) :
    (⟨640⟩ : UInt256) + UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨1⟩)
      ⟨480⟩ = sigmaMessageOffsetWord i 14 := by
  unfold sigmaPackedWord sigmaPackedWordNat sigmaMessageOffsetWord sigmaMessageOffset
    sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> native_decide

private theorem sigmaPackedWord_offset15 (i : Nat) :
    UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨5⟩) ⟨480⟩ +
      (⟨640⟩ : UInt256) = sigmaMessageOffsetWord i 15 := by
  unfold sigmaPackedWord sigmaPackedWordNat sigmaMessageOffsetWord sigmaMessageOffset
    sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> native_decide

private theorem sigmaMessageOffset_toNat_lt_1984 (i j : Nat) (hj : j < 16) :
    (UInt256.ofNat (sigmaMessageOffset i j)).toNat < 1984 := by
  unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> interval_cases j <;> native_decide

private theorem sigmaMessageOffsetWord_toNat (i j : Nat) (hj : j < 16) :
    (UInt256.ofNat (sigmaMessageOffset i j)).toNat = sigmaMessageOffset i j := by
  unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> interval_cases j <;> native_decide

private theorem sigmaMessageOffset_not_ge_activeWords (i j : Nat) (hj : j < 16) :
    ¬ UInt256.ofNat (sigmaMessageOffset i j) ≥ (UInt256.ofNat 62) * ⟨32⟩ := by
  unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> interval_cases j <;> native_decide

private theorem sigmaMessageOffset_memoryExpansion_zero (i j : Nat) (hj : j < 16) :
    Cₘ (UInt256.ofNat
        (MachineState.M (UInt256.ofNat 62).toNat (sigmaMessageOffsetWord i j).toNat 32)) -
      Cₘ (UInt256.ofNat 62) = 0 := by
  unfold sigmaMessageOffsetWord sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> interval_cases j <;> native_decide

private theorem sigmaMessageOffset_activeWords (i j : Nat) (hj : j < 16) :
    UInt256.ofNat
      (MachineState.M (UInt256.ofNat 62).toNat (sigmaMessageOffsetWord i j).toNat 32) =
      UInt256.ofNat 62 := by
  unfold sigmaMessageOffsetWord sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> interval_cases j <;> native_decide

private theorem positiveRoundMix7ArgsMload14
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨1⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨1⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨1⟩) ⟨480⟩).toNat) 32))) =
      sigmaMessageLoad mem i 14 := by
  rw [sigmaPackedWord_offset14 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 14))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 14 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 14 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 14 (by decide)] using hload

private theorem positiveRoundMix7ArgsMload15
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨5⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat ≥ mem.size
        ∨ (UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨5⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        ((UInt256.land (UInt256.shiftLeft (sigmaPackedWord i) ⟨5⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat) 32))) =
      sigmaMessageLoad mem i 15 := by
  rw [sigmaPackedWord_offset15 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 15))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 15 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 15 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 15 (by decide)] using hload

/-- Generic exact trace for the fourth diagonal `mixG` argument setup, from PC `3070` to PC
`3109`. -/
theorem positiveRoundMix7ArgsFromMix6Raw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨3070⟩
      (positiveRoundAfterMix6Stack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨3109⟩
      (positiveRoundMix7EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 84) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨3070⟩
      [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundAfterMix6Stack] using hprefix
  have hmload14 := positiveRoundMix7ArgsMload14 i hmem
  have hmload15 := positiveRoundMix7ArgsMload15 i hmem
  have rd3109 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup6,
    push8 ⟨18446744073709551615⟩,
    swap1,
    swap3,
    swap2,
    swap3,
    push2 ⟨480⟩,
    dup3,
    dup2,
    dup7,
    push1 ⟨1⟩,
    shl,
    and,
    dup4,
    add,
    raw mload 0 (sigmaMessageLoad mem i 14) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset14 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 14 (by decide))
      hmload14
      (by
        rw [sigmaPackedWord_offset14 i]
        exact sigmaMessageOffset_activeWords i 14 (by decide)) (by evm_ov),
    and,
    swap5,
    push1 ⟨5⟩,
    shl,
    and,
    add,
    raw mload 0 (sigmaMessageLoad mem i 15) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset15 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 15 (by decide))
      hmload15
      (by
        rw [sigmaPackedWord_offset15 i]
        exact sigmaMessageOffset_activeWords i 15 (by decide)) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundMix7EntryStack, sigmaMessageArg, u64MaskWord] using rd3109⟩

/-- Context-level wrapper for the generic fourth diagonal `mixG` argument setup. -/
theorem positiveRoundMix7ArgsFromMix6
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨3070⟩
          (positiveRoundAfterMix6Stack ctx.executionEnv i)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨3109⟩
            (positiveRoundMix7EntryStack ctx.executionEnv i mem)
            mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
            (C + 84) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix7ArgsFromMix6Raw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
