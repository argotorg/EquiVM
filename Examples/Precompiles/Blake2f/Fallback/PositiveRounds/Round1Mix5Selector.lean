import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix4

/-!
# BLAKE2F fallback positive-round traces: round-1 second diagonal `mixG` argument setup

This module continues the multi-round path from PC `2610`.  For round 1, the bytecode extracts
SIGMA indices `10` and `11`, loads message words `m[0]` and `m[2]`, and jumps to the second
diagonal shared `mixG` body at PC `2656`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-1 SIGMA index `10` selects bytecode memory offset `640`, i.e. `m[0]`. -/
theorem sigmaRound1Offset10 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨15⟩)
    ⟨480⟩ = (⟨640⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `11` selects bytecode memory offset `704`, i.e. `m[2]`. -/
theorem sigmaRound1Offset11 : UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨11⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨704⟩ : UInt256) := by
  native_decide

abbrev round1M0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 640 32))

abbrev round1M2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

abbrev round1M0Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M0Load mem) u64MaskWord

abbrev round1M2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M2Load mem) u64MaskWord

private theorem round1Mix5ArgsMloadM0 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨15⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨15⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨15⟩) ⟨480⟩).toNat 32))) =
      round1M0Load mem := by
  rw [sigmaRound1Offset10]
  unfold round1M0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix5ArgsMloadM2 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨11⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round1M2Load mem := by
  rw [sigmaRound1Offset11]
  unfold round1M2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix5ArgsFromRound1Mix4Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2610⟩
        [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round1M2Arg mem, round1M0Arg mem, ⟨2840⟩, sigmaRound1Word,
        ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2610⟩ := hprefix
  have hmloadM0 := round1Mix5ArgsMloadM0 hmem
  have hmloadM2 := round1Mix5ArgsMloadM2 hmem
  have rd2656 := evm_run rd2610 with [
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
    raw mload 0 (round1M0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨11⟩,
    shr,
    and,
    add,
    raw mload 0 (round1M2Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, round1M0Arg, round1M2Arg] using rd2656⟩

def round1Mix4ZeroMem (I : ExecutionEnv) : ByteArray :=
  round1Mix4Mem3
    (round1Mix3Mem3
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3
                    (fourthMixMem3
                      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))))

def round1Mix4OneMem (I : ExecutionEnv) : ByteArray :=
  round1Mix4Mem3
    (round1Mix3Mem3
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3
                    (fourthMixMem3
                      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))))

theorem round1Mix4ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1Mix4ZeroMem I).size = 1984 := by
  unfold round1Mix4ZeroMem
  have h0 := v13MixedMem_size I hlen
  have h1 := firstMixMem3_size h0
  have h2 := secondMixMem3_size h1
  have h3 := thirdMixMem3_size h2
  have h4 := fourthMixMem3_size h3
  have h5 := fifthMixMem3_size h4
  have h6 := sixthMixMem3_size h5
  have h7 := seventhMixMem3_size h6
  have h8 := eighthMixMem3_size h7
  have h9 := round1Mix0Mem3_size h8
  have h10 := round1Mix1Mem3_size h9
  have h11 := round1Mix2Mem3_size h10
  have h12 := round1Mix3Mem3_size h11
  exact round1Mix4Mem3_size h12

theorem round1Mix4OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1Mix4OneMem I).size = 1984 := by
  unfold round1Mix4OneMem
  have h0 := v14FinalFlagMem_size I hlen
  have h1 := firstMixMem3_size h0
  have h2 := secondMixMem3_size h1
  have h3 := thirdMixMem3_size h2
  have h4 := fourthMixMem3_size h3
  have h5 := fifthMixMem3_size h4
  have h6 := sixthMixMem3_size h5
  have h7 := seventhMixMem3_size h6
  have h8 := eighthMixMem3_size h7
  have h9 := round1Mix0Mem3_size h8
  have h10 := round1Mix1Mem3_size h9
  have h11 := round1Mix2Mem3_size h10
  have h12 := round1Mix3Mem3_size h11
  exact round1Mix4Mem3_size h12

/-- Final-flag-`0`, at least two rounds: the second diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix5ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round1M2Arg (round1Mix4ZeroMem I),
        round1M0Arg (round1Mix4ZeroMem I),
        ⟨2840⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix4ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (13216 + 93) := by
  have hprefix := validPositiveRound1Mix4DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix5ArgsFromRound1Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix4ZeroMem I)
    (startGas := 13216)
    (round1Mix4ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least two rounds: the second diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix5ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round1M2Arg (round1Mix4OneMem I),
        round1M0Arg (round1Mix4OneMem I),
        ⟨2840⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix4OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (13243 + 93) := by
  have hprefix := validPositiveRound1Mix4DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix5ArgsFromRound1Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix4OneMem I)
    (startGas := 13243)
    (round1Mix4OneMem_size hlen)
    hprefix

end Blake2f
