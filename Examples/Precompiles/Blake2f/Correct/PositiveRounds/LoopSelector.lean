import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopResidues
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round2Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round4Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round6Selector

/-!
# BLAKE2F positive-round arbitrary selector traces

This file starts replacing the fixed `RoundNSelector` frontier with residue-specific selector
traces usable by the arbitrary-round loop proof.  The first case is residue `0`: any loop index
`i` with `i % 10 = 0` takes the same compiled selector branch as concrete round `0`, but preserves
the original loop index on the stack.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Raw residue-0 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue0SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 0)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod0 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨0⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hbranch :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod0]
    native_decide
  have hmloadM0 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        firstRoundM0Load mem := by
    rw [sigmaRound0Offset0]
    unfold firstRoundM0Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM1 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        firstRoundM1Load mem := by
    rw [sigmaRound0Offset1]
    unfold firstRoundM1Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiT hbranch (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound0Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (firstRoundM0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM1
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 168 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound0Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound0Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 640 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 672 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound0Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      firstRoundM0Arg, firstRoundM1Arg, firstRoundM0Load, firstRoundM1Load] using hrd0⟩

/-- Context-level residue-0 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue0SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 0
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue0SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- Raw residue-1 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue1SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 1)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod1 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨1⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod1]
    native_decide
  have htake1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod1]
    native_decide
  have hmloadM14 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        secondRoundM14Load mem := by
    rw [sigmaRound1Offset0]
    unfold secondRoundM14Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1088⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM10 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        secondRoundM10Load mem := by
    rw [sigmaRound1Offset1]
    unfold secondRoundM10Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨960⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiT htake1 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound1Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (secondRoundM14Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM14
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (secondRoundM10Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM10
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 190 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound1Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound1Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 1088 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 960 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound1Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      secondRoundM14Arg, secondRoundM10Arg, secondRoundM14Load, secondRoundM10Load] using hrd0⟩

/-- Context-level residue-1 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue1SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 1
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue1SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- Raw residue-2 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue2SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 2)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod2 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨2⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod2]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod2]
    native_decide
  have htake2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod2]
    native_decide
  have hmloadM11 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round2M11Load mem := by
    rw [sigmaRound2Offset0]
    unfold round2M11Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM8 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round2M8Load mem := by
    rw [sigmaRound2Offset1]
    unfold round2M8Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨896⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiT htake2 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound2Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round2M11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM11
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round2M8Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM8
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 212 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound2Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound2Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 992 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 896 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound2Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round2M11Arg, round2M8Arg, round2M11Load, round2M8Load] using hrd0⟩

/-- Context-level residue-2 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue2SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 2
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue2SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- Raw residue-3 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue3SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 3)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod3 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨3⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod3]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod3]
    native_decide
  have hskip2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod3]
    native_decide
  have htake3 :
      UInt256.eq (⟨3⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod3]
    native_decide
  have hmloadM7 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round3M7Load mem := by
    rw [sigmaRound3Offset0]
    unfold round3M7Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM9 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round3M9Load mem := by
    rw [sigmaRound3Offset1]
    unfold round3M9Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT hskip2,
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiT htake3 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound3Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round3M7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM7
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 234 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound3Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound3Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 864 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 928 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound3Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round3M7Arg, round3M9Arg, round3M7Load, round3M9Load] using hrd0⟩

/-- Context-level residue-3 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue3SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 3
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue3SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- Raw residue-4 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue4SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 4)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod4 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨4⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod4]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod4]
    native_decide
  have hskip2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod4]
    native_decide
  have hskip3 :
      UInt256.eq (⟨3⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod4]
    native_decide
  have htake4 :
      UInt256.eq (⟨4⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod4]
    native_decide
  have hmloadM9 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round4M9Load mem := by
    rw [sigmaRound4Offset0]
    unfold round4M9Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM0 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round4M0Load mem := by
    rw [sigmaRound4Offset1]
    unfold round4M0Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT hskip2,
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiNT hskip3,
    dup1,
    push1 ⟨4⟩,
    eq,
    push2 ⟨1089⟩,
    jumpiT htake4 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound4Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round4M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round4M0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 256 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound4Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound4Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 928 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 640 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound4Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round4M9Arg, round4M0Arg, round4M9Load, round4M0Load] using hrd0⟩

/-- Context-level residue-4 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue4SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 4
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue4SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- Raw residue-5 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue5SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 5)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod5 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨5⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod5]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod5]
    native_decide
  have hskip2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod5]
    native_decide
  have hskip3 :
      UInt256.eq (⟨3⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod5]
    native_decide
  have hskip4 :
      UInt256.eq (⟨4⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod5]
    native_decide
  have htake5 :
      UInt256.eq (⟨5⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod5]
    native_decide
  have hmloadM2 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round5M2Load mem := by
    rw [sigmaRound5Offset0]
    unfold round5M2Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM12 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round5M12Load mem := by
    rw [sigmaRound5Offset1]
    unfold round5M12Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT hskip2,
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiNT hskip3,
    dup1,
    push1 ⟨4⟩,
    eq,
    push2 ⟨1089⟩,
    jumpiNT hskip4,
    dup1,
    push1 ⟨5⟩,
    eq,
    push2 ⟨1076⟩,
    jumpiT htake5 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound5Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round5M2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM2
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 278 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound5Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound5Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 704 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 1024 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound5Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round5M2Arg, round5M12Arg, round5M2Load, round5M12Load] using hrd0⟩

/-- Context-level residue-5 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue5SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 5
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue5SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- Raw residue-6 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue6SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 6)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod6 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨6⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod6]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod6]
    native_decide
  have hskip2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod6]
    native_decide
  have hskip3 :
      UInt256.eq (⟨3⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod6]
    native_decide
  have hskip4 :
      UInt256.eq (⟨4⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod6]
    native_decide
  have hskip5 :
      UInt256.eq (⟨5⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod6]
    native_decide
  have htake6 :
      UInt256.eq (⟨6⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod6]
    native_decide
  have hmloadM12 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round6M12Load mem := by
    rw [sigmaRound6Offset0]
    unfold round6M12Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM5 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round6M5Load mem := by
    rw [sigmaRound6Offset1]
    unfold round6M5Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT hskip2,
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiNT hskip3,
    dup1,
    push1 ⟨4⟩,
    eq,
    push2 ⟨1089⟩,
    jumpiNT hskip4,
    dup1,
    push1 ⟨5⟩,
    eq,
    push2 ⟨1076⟩,
    jumpiNT hskip5,
    dup1,
    push1 ⟨6⟩,
    eq,
    push2 ⟨1063⟩,
    jumpiT htake6 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound6Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round6M12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round6M5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM5
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 300 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound6Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound6Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 1024 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 800 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound6Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round6M12Arg, round6M5Arg, round6M12Load, round6M5Load] using hrd0⟩

/-- Context-level residue-6 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue6SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 6
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue6SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- The compiled selector's packed SIGMA word for residue `7`.

There is no old top-level `Round7Selector` file: the previous fixed-round proof frontier stopped
after round 6.  This constant is read directly from the bytecode branch at PC `1050` and agrees
with the trusted-model checkpoint in `sigmaPackedWordNat_checkpoints`. -/
abbrev sigmaRound7Word : UInt256 :=
  ⟨15816291393287259690⟩

theorem sigmaRound7Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨55⟩)
    ⟨480⟩ = (⟨1056⟩ : UInt256) := by
  native_decide

theorem sigmaRound7Offset1 : UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨992⟩ : UInt256) := by
  native_decide

abbrev round7M13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1056 32))

abbrev round7M11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 992 32))

abbrev round7M13Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round7M13Load mem) u64MaskWord

abbrev round7M11Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round7M11Load mem) u64MaskWord

/-- Raw residue-7 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue7SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 7)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod7 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨7⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have hskip2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have hskip3 :
      UInt256.eq (⟨3⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have hskip4 :
      UInt256.eq (⟨4⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have hskip5 :
      UInt256.eq (⟨5⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have hskip6 :
      UInt256.eq (⟨6⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have htake7 :
      UInt256.eq (⟨7⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod7]
    native_decide
  have hmloadM13 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round7M13Load mem := by
    rw [sigmaRound7Offset0]
    unfold round7M13Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1056⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM11 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound7Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round7M11Load mem := by
    rw [sigmaRound7Offset1]
    unfold round7M11Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT hskip2,
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiNT hskip3,
    dup1,
    push1 ⟨4⟩,
    eq,
    push2 ⟨1089⟩,
    jumpiNT hskip4,
    dup1,
    push1 ⟨5⟩,
    eq,
    push2 ⟨1076⟩,
    jumpiNT hskip5,
    dup1,
    push1 ⟨6⟩,
    eq,
    push2 ⟨1063⟩,
    jumpiNT hskip6,
    dup1,
    push1 ⟨7⟩,
    eq,
    push2 ⟨1050⟩,
    jumpiT htake7 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound7Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round7M13Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM13
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round7M11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM11
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 322 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound7Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound7Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 1056 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 992 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound7Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round7M13Arg, round7M11Arg, round7M13Load, round7M11Load] using hrd0⟩

/-- Context-level residue-7 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue7SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 7
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue7SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- The compiled selector's packed SIGMA word for residue `8`.

Read directly from the bytecode branch at PC `1037`; this agrees with the trusted-model checkpoint
in `sigmaPackedWordNat_checkpoints`. -/
abbrev sigmaRound8Word : UInt256 :=
  ⟨8064173457993569445⟩

theorem sigmaRound8Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨55⟩)
    ⟨480⟩ = (⟨832⟩ : UInt256) := by
  native_decide

theorem sigmaRound8Offset1 : UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1120⟩ : UInt256) := by
  native_decide

abbrev round8M6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 832 32))

abbrev round8M15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1120 32))

abbrev round8M6Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round8M6Load mem) u64MaskWord

abbrev round8M15Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round8M15Load mem) u64MaskWord

/-- Raw residue-8 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue8SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 8)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod8 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨8⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hskip2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hskip3 :
      UInt256.eq (⟨3⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hskip4 :
      UInt256.eq (⟨4⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hskip5 :
      UInt256.eq (⟨5⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hskip6 :
      UInt256.eq (⟨6⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hskip7 :
      UInt256.eq (⟨7⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have htake8 :
      UInt256.eq (⟨8⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod8]
    native_decide
  have hmloadM6 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round8M6Load mem := by
    rw [sigmaRound8Offset0]
    unfold round8M6Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨832⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM15 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound8Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round8M15Load mem := by
    rw [sigmaRound8Offset1]
    unfold round8M15Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1120⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT hskip2,
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiNT hskip3,
    dup1,
    push1 ⟨4⟩,
    eq,
    push2 ⟨1089⟩,
    jumpiNT hskip4,
    dup1,
    push1 ⟨5⟩,
    eq,
    push2 ⟨1076⟩,
    jumpiNT hskip5,
    dup1,
    push1 ⟨6⟩,
    eq,
    push2 ⟨1063⟩,
    jumpiNT hskip6,
    dup1,
    push1 ⟨7⟩,
    eq,
    push2 ⟨1050⟩,
    jumpiNT hskip7,
    dup1,
    push1 ⟨8⟩,
    eq,
    push2 ⟨1037⟩,
    jumpiT htake8 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound8Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round8M6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM6
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round8M15Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM15
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 344 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound8Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound8Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 832 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 1120 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound8Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round8M6Arg, round8M15Arg, round8M6Load, round8M15Load] using hrd0⟩

/-- Context-level residue-8 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue8SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 8
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue8SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- The compiled selector's packed SIGMA word for residue `9`.

Read directly from the bytecode branch at PC `1025`; this agrees with the trusted-model checkpoint
in `sigmaPackedWordNat_checkpoints`. -/
abbrev sigmaRound9Word : UInt256 :=
  ⟨11710614767857974480⟩

theorem sigmaRound9Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨55⟩)
    ⟨480⟩ = (⟨960⟩ : UInt256) := by
  native_decide

theorem sigmaRound9Offset1 : UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨704⟩ : UInt256) := by
  native_decide

abbrev round9M10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 960 32))

abbrev round9M2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

abbrev round9M10Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round9M10Load mem) u64MaskWord

abbrev round9M2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round9M2Load mem) u64MaskWord

/-- Raw residue-9 selector trace from the loop body to the shared first `mixG` entry. -/
theorem positiveRoundResidue9SelectorTraceRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i < UInt256.size)
    (hresidue : i % 10 = 9)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + sigmaSelectorToMix0Gas i) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1445⟩
      [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundBodyPc, positiveRoundHeaderStack] using hprefix
  have hmod9 : UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10) = (⟨9⟩ : UInt256) := by
    rw [u256_mod_ten_ofNat_of_lt hi, hresidue]
    rfl
  have hskip0 :
      UInt256.isZero (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip1 :
      UInt256.eq (⟨1⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip2 :
      UInt256.eq (⟨2⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip3 :
      UInt256.eq (⟨3⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip4 :
      UInt256.eq (⟨4⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip5 :
      UInt256.eq (⟨5⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip6 :
      UInt256.eq (⟨6⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip7 :
      UInt256.eq (⟨7⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hskip8 :
      UInt256.eq (⟨8⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) =
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have htake9 :
      UInt256.eq (⟨9⟩ : UInt256) (UInt256.mod (UInt256.ofNat i) (UInt256.ofNat 10)) ≠
        (⟨0⟩ : UInt256) := by
    rw [hmod9]
    native_decide
  have hmloadM10 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨55⟩) ⟨480⟩).toNat ≥
            mem.size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        round9M10Load mem := by
    rw [sigmaRound9Offset0]
    unfold round9M10Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨960⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmloadM2 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            mem.size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound9Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        round9M2Load mem := by
    rw [sigmaRound9Offset1]
    unfold round9M2Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1512 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT hskip0,
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT hskip1,
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT hskip2,
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiNT hskip3,
    dup1,
    push1 ⟨4⟩,
    eq,
    push2 ⟨1089⟩,
    jumpiNT hskip4,
    dup1,
    push1 ⟨5⟩,
    eq,
    push2 ⟨1076⟩,
    jumpiNT hskip5,
    dup1,
    push1 ⟨6⟩,
    eq,
    push2 ⟨1063⟩,
    jumpiNT hskip6,
    dup1,
    push1 ⟨7⟩,
    eq,
    push2 ⟨1050⟩,
    jumpiNT hskip7,
    dup1,
    push1 ⟨8⟩,
    eq,
    push2 ⟨1037⟩,
    jumpiNT hskip8,
    push1 ⟨9⟩,
    eq,
    push2 ⟨1025⟩,
    jumpiT htake9 (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push8 sigmaRound9Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
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
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round9M10Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM10
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round9M2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM2
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  have hgas : C + 361 = C + sigmaSelectorToMix0Gas i := by
    unfold sigmaSelectorToMix0Gas
    rw [hresidue]
    norm_num
  have hpacked : sigmaPackedWord i = sigmaRound9Word := by
    unfold sigmaPackedWord sigmaPackedWordNat sigmaNibble sigmaRound9Word
    rw [hresidue]
    native_decide
  have hoff0 : sigmaMessageOffset i 0 = 960 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  have hoff1 : sigmaMessageOffset i 1 = 704 := by
    unfold sigmaMessageOffset sigmaNibble mBaseOffset wordBytes
    rw [hresidue]
    native_decide
  exact ⟨_, by
    have hrd0 := RDx.withIndices rd1512 rfl hgas
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack, sigmaRound9Word,
      hpacked, hoff0, hoff1, sigmaMessageArg, sigmaMessageLoad, u64MaskWord,
      round9M10Arg, round9M2Arg, round9M10Load, round9M2Load] using hrd0⟩

/-- Context-level residue-9 selector trace for the arbitrary positive-round loop. -/
theorem positiveRoundResidue9SelectorTrace
    (ctx : BytecodeContext) :
    PositiveRoundResidueSelectorTrace ctx 9
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  intro i mem hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i < UInt256.size := by
    exact lt_trans hrounds
      (lt_trans (modelRounds_lt_uint32 ctx.executionEnv.calldata) (by norm_num [UInt256.size]))
  exact positiveRoundResidue9SelectorTraceRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hi hresidue hrdx

/-- The complete residue-indexed selector family for the arbitrary positive-round loop. -/
theorem positiveRoundResidueSelectorTrace
    (ctx : BytecodeContext) {residue : Nat} (hlt : residue < 10) :
    PositiveRoundResidueSelectorTrace ctx residue
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem) := by
  interval_cases residue <;>
    first
    | exact positiveRoundResidue0SelectorTrace ctx
    | exact positiveRoundResidue1SelectorTrace ctx
    | exact positiveRoundResidue2SelectorTrace ctx
    | exact positiveRoundResidue3SelectorTrace ctx
    | exact positiveRoundResidue4SelectorTrace ctx
    | exact positiveRoundResidue5SelectorTrace ctx
    | exact positiveRoundResidue6SelectorTrace ctx
    | exact positiveRoundResidue7SelectorTrace ctx
    | exact positiveRoundResidue8SelectorTrace ctx
    | exact positiveRoundResidue9SelectorTrace ctx

/-- Selector trace without exposing the residue split.

This is the bytecode-facing selector interface the shared mix-remainder proof should consume:
for any loop index `i`, execute the periodic SIGMA selector and reach the generic `mixG` entry
stack, with exact selector gas. -/
theorem positiveRoundSelectorTrace
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      i < Model.rounds ctx.executionEnv.calldata →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundBodyPc
          (positiveRoundHeaderStack ctx.executionEnv i)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            positiveRoundMix0Pc
            (positiveRoundMix0EntryStack ctx.executionEnv i mem)
            mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
            (C + sigmaSelectorToMix0Gas i) := by
  intro i mem hinv hrounds k C hrdx
  exact positiveRoundResidueSelectorTrace ctx (Nat.mod_lt i (by decide))
    rfl hinv hrounds hrdx

end Blake2f
