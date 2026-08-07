import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix3

/-!
# BLAKE2F fallback positive-round traces: round-1 first diagonal `mixG` argument setup

This module continues the multi-round path from PC `2383`.  For round 1, the bytecode extracts
SIGMA indices `8` and `9`, loads message words `m[1]` and `m[12]`, and jumps to the first diagonal
shared `mixG` body at PC `2429`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-1 SIGMA index `8` selects bytecode memory offset `672`, i.e. `m[1]`. -/
theorem sigmaRound1Offset8 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨23⟩)
    ⟨480⟩ = (⟨672⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `9` selects bytecode memory offset `1024`, i.e. `m[12]`. -/
theorem sigmaRound1Offset9 : UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨19⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1024⟩ : UInt256) := by
  native_decide

abbrev round1M1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 672 32))

abbrev round1M12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1024 32))

abbrev round1M1Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M1Load mem) u64MaskWord

abbrev round1M12Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M12Load mem) u64MaskWord

private theorem round1Mix4ArgsMloadM1 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨23⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨23⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨23⟩) ⟨480⟩).toNat 32))) =
      round1M1Load mem := by
  rw [sigmaRound1Offset8]
  unfold round1M1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix4ArgsMloadM12 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨19⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round1M12Load mem := by
  rw [sigmaRound1Offset9]
  unfold round1M12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix4ArgsFromRound1Mix3Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2383⟩
        [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round1M12Arg mem, round1M1Arg mem, ⟨2610⟩, sigmaRound1Word,
        ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2383⟩ := hprefix
  have hmloadM1 := round1Mix4ArgsMloadM1 hmem
  have hmloadM12 := round1Mix4ArgsMloadM12 hmem
  have rd2429 := evm_run rd2383 with [
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
    raw mload 0 (round1M1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM1
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨19⟩,
    shr,
    and,
    add,
    raw mload 0 (round1M12Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, round1M1Arg, round1M12Arg] using rd2429⟩

/-- Final-flag-`0`, at least two rounds: the first diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix4ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round1M12Arg
          (round1Mix3Mem3
            (round1Mix2Mem3
              (round1Mix1Mem3
                (round1Mix0Mem3
                  (eighthMixMem3
                    (seventhMixMem3
                      (sixthMixMem3
                        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))))),
        round1M1Arg
          (round1Mix3Mem3
            (round1Mix2Mem3
              (round1Mix1Mem3
                (round1Mix0Mem3
                  (eighthMixMem3
                    (seventhMixMem3
                      (sixthMixMem3
                        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))))),
        ⟨2610⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix3Mem3
        (round1Mix2Mem3
          (round1Mix1Mem3
            (round1Mix0Mem3
              (eighthMixMem3
                (seventhMixMem3
                  (sixthMixMem3
                    (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 12901 := by
  have hprefix := validPositiveRound1Mix3DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix4ArgsFromRound1Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix3Mem3
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))))
    (startGas := 12808)
    (round1Mix3Mem3_size
      (round1Mix2Mem3_size
        (round1Mix1Mem3_size
          (round1Mix0Mem3_size
            (eighthMixMem3_size
              (seventhMixMem3_size
                (sixthMixMem3_size
                  (fifthMixMem3_size
                    (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))))))))))))
    hprefix

/-- Final-flag-`1`, at least two rounds: the first diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix4ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round1M12Arg
          (round1Mix3Mem3
            (round1Mix2Mem3
              (round1Mix1Mem3
                (round1Mix0Mem3
                  (eighthMixMem3
                    (seventhMixMem3
                      (sixthMixMem3
                        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))))),
        round1M1Arg
          (round1Mix3Mem3
            (round1Mix2Mem3
              (round1Mix1Mem3
                (round1Mix0Mem3
                  (eighthMixMem3
                    (seventhMixMem3
                      (sixthMixMem3
                        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))))),
        ⟨2610⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix3Mem3
        (round1Mix2Mem3
          (round1Mix1Mem3
            (round1Mix0Mem3
              (eighthMixMem3
                (seventhMixMem3
                  (sixthMixMem3
                    (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 12928 := by
  have hprefix := validPositiveRound1Mix3DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix4ArgsFromRound1Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix3Mem3
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))))
    (startGas := 12835)
    (round1Mix3Mem3_size
      (round1Mix2Mem3_size
        (round1Mix1Mem3_size
          (round1Mix0Mem3_size
            (eighthMixMem3_size
              (seventhMixMem3_size
                (sixthMixMem3_size
                  (fifthMixMem3_size
                    (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))))))))))))
    hprefix

end Blake2f
