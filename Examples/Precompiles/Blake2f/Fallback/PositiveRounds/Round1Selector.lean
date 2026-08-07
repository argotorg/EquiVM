import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Guard1

/-!
# BLAKE2F fallback positive-round traces: round-1 SIGMA selector

This module starts the second compression round on the multi-round path.  From PC `1445` with loop
index `1`, the bytecode computes `1 % 10`, selects packed SIGMA word
`0xea489fd61c02b753`, loads message words `m[14]` and `m[10]`, and jumps to the first shared
`mixG` body at PC `1512`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The compiled selector's packed SIGMA word for round `1`. -/
abbrev sigmaRound1Word : UInt256 :=
  ⟨16881918945140062035⟩

/-- Round-1 SIGMA index `0` selects bytecode memory offset `1088`, i.e. `m[14]`. -/
theorem sigmaRound1Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨55⟩)
    ⟨480⟩ = (⟨1088⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `1` selects bytecode memory offset `960`, i.e. `m[10]`. -/
theorem sigmaRound1Offset1 : UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨960⟩ : UInt256) := by
  native_decide

abbrev secondRoundM14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1088 32))

abbrev secondRoundM10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 960 32))

abbrev secondRoundM14Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (secondRoundM14Load mem) u64MaskWord

abbrev secondRoundM10Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (secondRoundM10Load mem) u64MaskWord

private theorem round1SelectorMloadM14 {mem : ByteArray} (hmem : mem.size = 1984) :
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

private theorem round1SelectorMloadM10 {mem : ByteArray} (hmem : mem.size = 1984) :
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

private theorem round1Mix0ArgsFromGuardGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1445⟩
        [⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [secondRoundM10Arg mem, secondRoundM14Arg mem, ⟨1693⟩,
        sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 190) := by
  obtain ⟨k0, rd1445⟩ := hprefix
  have hmloadM14 := round1SelectorMloadM14 hmem
  have hmloadM10 := round1SelectorMloadM10 hmem
  have rd1512 := evm_run rd1445 with [
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
    jumpiNT (by native_decide),
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiT (by native_decide) (by jump_dest),
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
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, secondRoundM14Arg, secondRoundM10Arg,
    Nat.add_assoc] using rd1512⟩

/-- Final-flag-`0`, at least two rounds: the first round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix0ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [secondRoundM10Arg
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))),
        secondRoundM14Arg
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))),
        ⟨1693⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 11251 := by
  have hprefix := validPositiveRound1GuardContinueZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := eighthMixMem3
      (seventhMixMem3
        (sixthMixMem3
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))
    (startGas := 11061)
    (eighthMixMem3_size
      (seventhMixMem3_size
        (sixthMixMem3_size
          (fifthMixMem3_size
            (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))))))))
    hprefix

/-- Final-flag-`1`, at least two rounds: the first round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix0ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [secondRoundM10Arg
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))),
        secondRoundM14Arg
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))),
        ⟨1693⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 11278 := by
  have hprefix := validPositiveRound1GuardContinueOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := eighthMixMem3
      (seventhMixMem3
        (sixthMixMem3
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))
    (startGas := 11088)
    (eighthMixMem3_size
      (seventhMixMem3_size
        (sixthMixMem3_size
          (fifthMixMem3_size
            (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))))))))
    hprefix

end Blake2f
