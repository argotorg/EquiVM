import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix3

/-!
# BLAKE2F positive-round arbitrary first diagonal `mixG` argument setup

This file factors the bytecode from PC `2383` to PC `2429`.  It extracts
`SIGMA[i % 10][8]` and `SIGMA[i % 10][9]`, loads the selected message words, and prepares the
first diagonal shared `mixG` call.  The theorem is parametric in the loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `2429`, with the first diagonal `mixG` arguments prepared. -/
def positiveRoundMix4EntryStack (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    List UInt256 :=
  [sigmaMessageArg mem i 9, sigmaMessageArg mem i 8, ⟨2610⟩, sigmaPackedWord i,
    ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundMix4EntryStack_length
    (I : ExecutionEnv) (i : Nat) (mem : ByteArray) :
    (positiveRoundMix4EntryStack I i mem).length = 14 := by
  simp [positiveRoundMix4EntryStack]

private theorem sigmaPackedWord_offset8 (i : Nat) :
    (⟨640⟩ : UInt256) + UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨23⟩)
      ⟨480⟩ = sigmaMessageOffsetWord i 8 := by
  unfold sigmaPackedWord sigmaPackedWordNat sigmaMessageOffsetWord sigmaMessageOffset
    sigmaNibble mBaseOffset wordBytes
  have hi : i % 10 < 10 := Nat.mod_lt i (by decide)
  interval_cases i % 10 <;> native_decide

private theorem sigmaPackedWord_offset9 (i : Nat) :
    UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨19⟩) ⟨480⟩ +
      (⟨640⟩ : UInt256) = sigmaMessageOffsetWord i 9 := by
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

private theorem positiveRoundMix4ArgsMload8
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨23⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ ((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨23⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (((⟨640⟩ : UInt256) +
          UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨23⟩) ⟨480⟩).toNat) 32))) =
      sigmaMessageLoad mem i 8 := by
  rw [sigmaPackedWord_offset8 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 8))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 8 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 8 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 8 (by decide)] using hload

private theorem positiveRoundMix4ArgsMload9
    {mem : ByteArray} (i : Nat) (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨19⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat ≥ mem.size
        ∨ (UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨19⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        ((UInt256.land (UInt256.shiftRight (sigmaPackedWord i) ⟨19⟩) ⟨480⟩ +
          (⟨640⟩ : UInt256)).toNat) 32))) =
      sigmaMessageLoad mem i 9 := by
  rw [sigmaPackedWord_offset9 i]
  unfold sigmaMessageLoad sigmaMessageOffsetWord
  have hload := mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62)
    (off := UInt256.ofNat (sigmaMessageOffset i 9))
    (memSize := 1984) hmem
    (sigmaMessageOffset_toNat_lt_1984 i 9 (by decide))
    (sigmaMessageOffset_not_ge_activeWords i 9 (by decide))
  simpa [sigmaMessageOffsetWord_toNat i 9 (by decide)] using hload

/-- Generic exact trace for the first diagonal `mixG` argument setup, from PC `2383` to PC `2429`. -/
theorem positiveRoundMix4ArgsFromMix3Raw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨2383⟩
      (positiveRoundAfterMix3Stack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨2429⟩
      (positiveRoundMix4EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 93) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨2383⟩
      [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundAfterMix3Stack] using hprefix
  have hmload8 := positiveRoundMix4ArgsMload8 i hmem
  have hmload9 := positiveRoundMix4ArgsMload9 i hmem
  have rd2429 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2610⟩,
    push2 ⟨2429⟩,
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
    push1 ⟨23⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (sigmaMessageLoad mem i 8) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset8 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 8 (by decide))
      hmload8
      (by
        rw [sigmaPackedWord_offset8 i]
        exact sigmaMessageOffset_activeWords i 8 (by decide)) (by evm_ov),
    and,
    swap5,
    push1 ⟨19⟩,
    shr,
    and,
    add,
    raw mload 0 (sigmaMessageLoad mem i 9) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [sigmaPackedWord_offset9 i]
        exact sigmaMessageOffset_memoryExpansion_zero i 9 (by decide))
      hmload9
      (by
        rw [sigmaPackedWord_offset9 i]
        exact sigmaMessageOffset_activeWords i 9 (by decide)) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundMix4EntryStack, sigmaMessageArg, u64MaskWord] using rd2429⟩

/-- Context-level wrapper for the generic first diagonal `mixG` argument setup. -/
theorem positiveRoundMix4ArgsFromMix3
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨2383⟩
          (positiveRoundAfterMix3Stack ctx.executionEnv i)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨2429⟩
            (positiveRoundMix4EntryStack ctx.executionEnv i mem)
            mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
            (C + 93) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix4ArgsFromMix3Raw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
