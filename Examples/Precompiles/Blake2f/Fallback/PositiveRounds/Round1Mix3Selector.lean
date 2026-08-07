import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix2

/-!
# BLAKE2F fallback positive-round traces: round-1 fourth `mixG` argument setup

This module continues the multi-round path from PC `2153`.  For round 1, the bytecode extracts
SIGMA indices `6` and `7`, loads message words `m[13]` and `m[6]`, and jumps to the next shared
`mixG` body at PC `2199`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-1 SIGMA index `6` selects bytecode memory offset `1056`, i.e. `m[13]`. -/
theorem sigmaRound1Offset6 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨31⟩)
    ⟨480⟩ = (⟨1056⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `7` selects bytecode memory offset `832`, i.e. `m[6]`. -/
theorem sigmaRound1Offset7 : UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨27⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨832⟩ : UInt256) := by
  native_decide

abbrev round1M13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1056 32))

abbrev round1M6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 832 32))

abbrev round1M13Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M13Load mem) u64MaskWord

abbrev round1M6Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M6Load mem) u64MaskWord

private theorem round1Mix3ArgsMloadM13 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨31⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨31⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨31⟩) ⟨480⟩).toNat 32))) =
      round1M13Load mem := by
  rw [sigmaRound1Offset6]
  unfold round1M13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1056⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix3ArgsMloadM6 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨27⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round1M6Load mem := by
  rw [sigmaRound1Offset7]
  unfold round1M6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨832⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix3ArgsFromRound1Mix2Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2153⟩
        [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round1M6Arg mem, round1M13Arg mem, ⟨2383⟩, sigmaRound1Word,
        ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2153⟩ := hprefix
  have hmloadM13 := round1Mix3ArgsMloadM13 hmem
  have hmloadM6 := round1Mix3ArgsMloadM6 hmem
  have rd2199 := evm_run rd2153 with [
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
    raw mload 0 (round1M13Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM13
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨27⟩,
    shr,
    and,
    add,
    raw mload 0 (round1M6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM6
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, round1M13Arg, round1M6Arg] using rd2199⟩

/-- Final-flag-`0`, at least two rounds: the fourth round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix3ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round1M6Arg
          (round1Mix2Mem3
            (round1Mix1Mem3
              (round1Mix0Mem3
                (eighthMixMem3
                  (seventhMixMem3
                    (sixthMixMem3
                      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))),
        round1M13Arg
          (round1Mix2Mem3
            (round1Mix1Mem3
              (round1Mix0Mem3
                (eighthMixMem3
                  (seventhMixMem3
                    (sixthMixMem3
                      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))),
        ⟨2383⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 12487 := by
  have hprefix := validPositiveRound1Mix2DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix3ArgsFromRound1Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix2Mem3
      (round1Mix1Mem3
        (round1Mix0Mem3
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))))
    (startGas := 12394)
    (round1Mix2Mem3_size
      (round1Mix1Mem3_size
        (round1Mix0Mem3_size
          (eighthMixMem3_size
            (seventhMixMem3_size
              (sixthMixMem3_size
                (fifthMixMem3_size
                  (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))))))))))
    hprefix

/-- Final-flag-`1`, at least two rounds: the fourth round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix3ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round1M6Arg
          (round1Mix2Mem3
            (round1Mix1Mem3
              (round1Mix0Mem3
                (eighthMixMem3
                  (seventhMixMem3
                    (sixthMixMem3
                      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))),
        round1M13Arg
          (round1Mix2Mem3
            (round1Mix1Mem3
              (round1Mix0Mem3
                (eighthMixMem3
                  (seventhMixMem3
                    (sixthMixMem3
                      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))),
        ⟨2383⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 12514 := by
  have hprefix := validPositiveRound1Mix2DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix3ArgsFromRound1Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix2Mem3
      (round1Mix1Mem3
        (round1Mix0Mem3
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))))
    (startGas := 12421)
    (round1Mix2Mem3_size
      (round1Mix1Mem3_size
        (round1Mix0Mem3_size
          (eighthMixMem3_size
            (seventhMixMem3_size
              (sixthMixMem3_size
                (fifthMixMem3_size
                  (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))))))))))
    hprefix

end Blake2f
