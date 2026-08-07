import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix2

/-!
# BLAKE2F positive-round arbitrary fourth `mixG` argument setup

This file factors the bytecode from PC `2153` to PC `2199`.  It extracts
`SIGMA[i % 10][6]` and `SIGMA[i % 10][7]`, loads the selected message words, and prepares the
fourth shared `mixG` call.  The theorem is parametric in the loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `2199`, with the fourth `mixG` arguments prepared. -/
def positiveRoundMix3EntryStack (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    List UInt256 :=
  [sigmaMessageArg mem i 7, sigmaMessageArg mem i 6, ⟨2383⟩, sigmaPackedWord i,
    ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundMix3EntryStack_length
    (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    (positiveRoundMix3EntryStack I i mem).length = 14 := by
  simp [positiveRoundMix3EntryStack]

private theorem sigmaPackedWord_offset6 (i : Nat) :
    (⟨640⟩ : UInt256) + UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨31⟩)
      ⟨480⟩ = sigmaMessageOffsetWord i 6 := by
  unfold sigmaPackedWord sigmaPackedWordNat sigmaMessageOffsetWord sigmaMessageOffset
    sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> native_decide

private theorem sigmaPackedWord_offset7 (i : Nat) :
    UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨27⟩) ⟨480⟩ +
      (⟨640⟩ : UInt256) = sigmaMessageOffsetWord i 7 := by
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

private theorem positiveRoundMix3ArgsMload6
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨31⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨31⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨31⟩) ⟨480⟩).toNat) 32))) =
      sigmaMessageLoad mem i 6 := by
  rw [sigmaPackedWord_offset6 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 6))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 6 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 6 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 6 (by decide)] using hload

private theorem positiveRoundMix3ArgsMload7
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨27⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat ≥ mem.size
        ∨ (UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨27⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        ((UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨27⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat) 32))) =
      sigmaMessageLoad mem i 7 := by
  rw [sigmaPackedWord_offset7 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 7))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 7 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 7 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 7 (by decide)] using hload

/-- Generic exact trace for the fourth `mixG` argument setup, from PC `2153` to PC `2199`. -/
theorem positiveRoundMix3ArgsFromMix2Raw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨2153⟩
      (positiveRoundAfterMix2Stack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨2199⟩
      (positiveRoundMix3EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 93) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨2153⟩
      [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundAfterMix2Stack] using hprefix
  have hmload6 := positiveRoundMix3ArgsMload6 i hmem
  have hmload7 := positiveRoundMix3ArgsMload7 i hmem
  have rd2199 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2383⟩,
    push2 ⟨2199⟩,
    dup3,
    dup9,
    push8 ⟨18446744073709551615⟩,
    swap1,
    swap3,
    swap2,
    swap3,
    push2 ⟨480⟩,
    dup3,
    dup2,
    dup7,
    push1 ⟨31⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (sigmaMessageLoad mem i 6) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset6 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 6 (by decide))
      hmload6
      (by
        rw [sigmaPackedWord_offset6 i]
        exact sigmaMessageOffset_activeWords i 6 (by decide)) (by evm_ov),
    and,
    swap5,
    push1 ⟨27⟩,
    shr,
    and,
    add,
    raw mload 0 (sigmaMessageLoad mem i 7) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset7 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 7 (by decide))
      hmload7
      (by
        rw [sigmaPackedWord_offset7 i]
        exact sigmaMessageOffset_activeWords i 7 (by decide)) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundMix3EntryStack, sigmaMessageArg, u64MaskWord] using rd2199⟩

/-- Context-level wrapper for the generic fourth `mixG` argument setup. -/
theorem positiveRoundMix3ArgsFromMix2
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨2153⟩
          (positiveRoundAfterMix2Stack ctx.executionEnv i)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨2199⟩
            (positiveRoundMix3EntryStack ctx.executionEnv i mem)
            mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
            (C + 93) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix3ArgsFromMix2Raw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
