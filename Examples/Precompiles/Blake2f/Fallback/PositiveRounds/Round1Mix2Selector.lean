import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix1

/-!
# BLAKE2F fallback positive-round traces: round-1 third `mixG` argument setup

This module continues the multi-round path from PC `1923`.  For round 1, the bytecode extracts
SIGMA indices `4` and `5`, loads message words `m[9]` and `m[15]`, and jumps to the next shared
`mixG` body at PC `1969`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-1 SIGMA index `4` selects bytecode memory offset `928`, i.e. `m[9]`. -/
theorem sigmaRound1Offset4 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨39⟩)
    ⟨480⟩ = (⟨928⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `5` selects bytecode memory offset `1120`, i.e. `m[15]`. -/
theorem sigmaRound1Offset5 : UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨35⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1120⟩ : UInt256) := by
  native_decide

abbrev round1M9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 928 32))

abbrev round1M15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1120 32))

abbrev round1M9Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M9Load mem) u64MaskWord

abbrev round1M15Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M15Load mem) u64MaskWord

private theorem round1Mix2ArgsMloadM9 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨39⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨39⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨39⟩) ⟨480⟩).toNat 32))) =
      round1M9Load mem := by
  rw [sigmaRound1Offset4]
  unfold round1M9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix2ArgsMloadM15 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨35⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round1M15Load mem := by
  rw [sigmaRound1Offset5]
  unfold round1M15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1120⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix2ArgsFromRound1Mix1Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1923⟩
        [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round1M15Arg mem, round1M9Arg mem, ⟨2153⟩, sigmaRound1Word,
        ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1923⟩ := hprefix
  have hmloadM9 := round1Mix2ArgsMloadM9 hmem
  have hmloadM15 := round1Mix2ArgsMloadM15 hmem
  have rd1969 := evm_run rd1923 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2153⟩,
    push2 ⟨1969⟩,
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
    push1 ⟨39⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round1M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨35⟩,
    shr,
    and,
    add,
    raw mload 0 (round1M15Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, round1M9Arg, round1M15Arg] using rd1969⟩

/-- Final-flag-`0`, at least two rounds: the third round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix2ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round1M15Arg
          (round1Mix1Mem3
            (round1Mix0Mem3
              (eighthMixMem3
                (seventhMixMem3
                  (sixthMixMem3
                    (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))),
        round1M9Arg
          (round1Mix1Mem3
            (round1Mix0Mem3
              (eighthMixMem3
                (seventhMixMem3
                  (sixthMixMem3
                    (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))),
        ⟨2153⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix1Mem3
        (round1Mix0Mem3
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 12073 := by
  have hprefix := validPositiveRound1Mix1DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix2ArgsFromRound1Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix1Mem3
      (round1Mix0Mem3
        (eighthMixMem3
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))
    (startGas := 11980)
    (round1Mix1Mem3_size
      (round1Mix0Mem3_size
        (eighthMixMem3_size
          (seventhMixMem3_size
            (sixthMixMem3_size
              (fifthMixMem3_size
                (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))))))))))
    hprefix

/-- Final-flag-`1`, at least two rounds: the third round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix2ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round1M15Arg
          (round1Mix1Mem3
            (round1Mix0Mem3
              (eighthMixMem3
                (seventhMixMem3
                  (sixthMixMem3
                    (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))),
        round1M9Arg
          (round1Mix1Mem3
            (round1Mix0Mem3
              (eighthMixMem3
                (seventhMixMem3
                  (sixthMixMem3
                    (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))),
        ⟨2153⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix1Mem3
        (round1Mix0Mem3
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 12100 := by
  have hprefix := validPositiveRound1Mix1DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix2ArgsFromRound1Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix1Mem3
      (round1Mix0Mem3
        (eighthMixMem3
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))
    (startGas := 12007)
    (round1Mix1Mem3_size
      (round1Mix0Mem3_size
        (eighthMixMem3_size
          (seventhMixMem3_size
            (sixthMixMem3_size
              (fifthMixMem3_size
                (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))))))))))
    hprefix

end Blake2f
