import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix4

/-!
# BLAKE2F positive-round arbitrary second diagonal `mixG` argument setup

This file factors the bytecode from PC `2610` to PC `2656`.  It extracts
`SIGMA[i % 10][10]` and `SIGMA[i % 10][11]`, loads the selected message words, and prepares the
second diagonal shared `mixG` call.  The theorem is parametric in the loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `2656`, with the second diagonal `mixG` arguments prepared. -/
def positiveRoundMix5EntryStack (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    List UInt256 :=
  [sigmaMessageArg mem i 11, sigmaMessageArg mem i 10, ⟨2840⟩, sigmaPackedWord i,
    ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundMix5EntryStack_length
    (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    (positiveRoundMix5EntryStack I i mem).length = 14 := by
  simp [positiveRoundMix5EntryStack]

private theorem sigmaPackedWord_offset10 (i : Nat) :
    (⟨640⟩ : UInt256) + UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨15⟩)
      ⟨480⟩ = sigmaMessageOffsetWord i 10 := by
  unfold sigmaPackedWord sigmaPackedWordNat sigmaMessageOffsetWord sigmaMessageOffset
    sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> native_decide

private theorem sigmaPackedWord_offset11 (i : Nat) :
    UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨11⟩) ⟨480⟩ +
      (⟨640⟩ : UInt256) = sigmaMessageOffsetWord i 11 := by
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

private theorem positiveRoundMix5ArgsMload10
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨15⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨15⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨15⟩) ⟨480⟩).toNat) 32))) =
      sigmaMessageLoad mem i 10 := by
  rw [sigmaPackedWord_offset10 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 10))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 10 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 10 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 10 (by decide)] using hload

private theorem positiveRoundMix5ArgsMload11
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨11⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat ≥ mem.size
        ∨ (UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨11⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        ((UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨11⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat) 32))) =
      sigmaMessageLoad mem i 11 := by
  rw [sigmaPackedWord_offset11 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 11))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 11 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 11 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 11 (by decide)] using hload

/-- Generic exact trace for the second diagonal `mixG` argument setup, from PC `2610` to PC `2656`. -/
theorem positiveRoundMix5ArgsFromMix4Raw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨2610⟩
      (positiveRoundAfterMix4Stack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨2656⟩
      (positiveRoundMix5EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 93) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨2610⟩
      [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundAfterMix4Stack] using hprefix
  have hmload10 := positiveRoundMix5ArgsMload10 i hmem
  have hmload11 := positiveRoundMix5ArgsMload11 i hmem
  have rd2656 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2840⟩,
    push2 ⟨2656⟩,
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
    push1 ⟨15⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (sigmaMessageLoad mem i 10) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset10 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 10 (by decide))
      hmload10
      (by
        rw [sigmaPackedWord_offset10 i]
        exact sigmaMessageOffset_activeWords i 10 (by decide)) (by evm_ov),
    and,
    swap5,
    push1 ⟨11⟩,
    shr,
    and,
    add,
    raw mload 0 (sigmaMessageLoad mem i 11) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset11 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 11 (by decide))
      hmload11
      (by
        rw [sigmaPackedWord_offset11 i]
        exact sigmaMessageOffset_activeWords i 11 (by decide)) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundMix5EntryStack, sigmaMessageArg, u64MaskWord] using rd2656⟩

/-- Context-level wrapper for the generic second diagonal `mixG` argument setup. -/
theorem positiveRoundMix5ArgsFromMix4
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨2610⟩
          (positiveRoundAfterMix4Stack ctx.executionEnv i)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨2656⟩
            (positiveRoundMix5EntryStack ctx.executionEnv i mem)
            mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
            (C + 93) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix5ArgsFromMix4Raw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
