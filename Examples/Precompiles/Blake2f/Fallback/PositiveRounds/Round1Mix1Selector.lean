import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix0

/-!
# BLAKE2F fallback positive-round traces: round-1 second `mixG` argument setup

This module continues the multi-round path from PC `1693`.  For round 1, the bytecode extracts
SIGMA indices `2` and `3`, loads message words `m[4]` and `m[8]`, and jumps to the next shared
`mixG` body at PC `1739`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-1 SIGMA index `2` selects bytecode memory offset `768`, i.e. `m[4]`. -/
theorem sigmaRound1Offset2 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨47⟩)
    ⟨480⟩ = (⟨768⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `3` selects bytecode memory offset `896`, i.e. `m[8]`. -/
theorem sigmaRound1Offset3 : UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨43⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨896⟩ : UInt256) := by
  native_decide

abbrev secondRoundM4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 768 32))

abbrev secondRoundM8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 896 32))

abbrev secondRoundM4Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (secondRoundM4Load mem) u64MaskWord

abbrev secondRoundM8Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (secondRoundM8Load mem) u64MaskWord

private theorem round1Mix1ArgsMloadM4 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨47⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨47⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨47⟩) ⟨480⟩).toNat 32))) =
      secondRoundM4Load mem := by
  rw [sigmaRound1Offset2]
  unfold secondRoundM4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨768⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix1ArgsMloadM8 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨43⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      secondRoundM8Load mem := by
  rw [sigmaRound1Offset3]
  unfold secondRoundM8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨896⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix1ArgsFromRound1Mix0Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1693⟩
        [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [secondRoundM8Arg mem, secondRoundM4Arg mem, ⟨1923⟩, sigmaRound1Word,
        ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1693⟩ := hprefix
  have hmloadM4 := round1Mix1ArgsMloadM4 hmem
  have hmloadM8 := round1Mix1ArgsMloadM8 hmem
  have rd1739 := evm_run rd1693 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1923⟩,
    push2 ⟨1739⟩,
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
    push1 ⟨47⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (secondRoundM4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM4
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨43⟩,
    shr,
    and,
    add,
    raw mload 0 (secondRoundM8Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, secondRoundM4Arg, secondRoundM8Arg] using rd1739⟩

/-- Final-flag-`0`, at least two rounds: the second round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix1ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [secondRoundM8Arg
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))),
        secondRoundM4Arg
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))),
        ⟨1923⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix0Mem3
        (eighthMixMem3
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 11659 := by
  have hprefix := validPositiveRound1Mix0DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix1ArgsFromRound1Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix0Mem3
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))
    (startGas := 11566)
    (round1Mix0Mem3_size
      (eighthMixMem3_size
        (seventhMixMem3_size
          (sixthMixMem3_size
            (fifthMixMem3_size
              (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))))))))
    hprefix

/-- Final-flag-`1`, at least two rounds: the second round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix1ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [secondRoundM8Arg
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))),
        secondRoundM4Arg
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))),
        ⟨1923⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix0Mem3
        (eighthMixMem3
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 11686 := by
  have hprefix := validPositiveRound1Mix0DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix1ArgsFromRound1Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix0Mem3
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))
    (startGas := 11593)
    (round1Mix0Mem3_size
      (eighthMixMem3_size
        (seventhMixMem3_size
          (sixthMixMem3_size
            (fifthMixMem3_size
              (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))))))))
    hprefix

end Blake2f
