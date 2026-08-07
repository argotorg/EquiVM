import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix6

/-!
# BLAKE2F fallback positive-round traces: eighth `mixG` argument setup

This module continues the first positive-round body from PC `3070`.  The bytecode extracts
round-0 SIGMA indices `14` and `15`, loads message words `m[14]` and `m[15]`, and jumps to the
last diagonal shared `mixG` body at PC `3109`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-0 SIGMA index `14` selects bytecode memory offset `1088`, i.e. `m[14]`. -/
theorem sigmaRound0Offset14 : ⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨1⟩)
    ⟨480⟩ = (⟨1088⟩ : UInt256) := by
  native_decide

/-- Round-0 SIGMA index `15` selects bytecode memory offset `1120`, i.e. `m[15]`. -/
theorem sigmaRound0Offset15 : UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨5⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1120⟩ : UInt256) := by
  native_decide

abbrev firstRoundM14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1088 32))

abbrev firstRoundM15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1120 32))

abbrev firstRoundM14Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM14Load mem) u64MaskWord

abbrev firstRoundM15Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM15Load mem) u64MaskWord

private theorem eighthMixArgsMloadM14 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨1⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨1⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨1⟩) ⟨480⟩).toNat 32))) =
      firstRoundM14Load mem := by
  rw [sigmaRound0Offset14]
  unfold firstRoundM14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1088⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem eighthMixArgsMloadM15 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨5⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftLeft sigmaRound0Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      firstRoundM15Load mem := by
  rw [sigmaRound0Offset15]
  unfold firstRoundM15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1120⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem eighthMixArgsFromSeventhMixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3070⟩
        [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [firstRoundM15Arg mem, firstRoundM14Arg mem, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 84) := by
  obtain ⟨k0, rd3070⟩ := hprefix
  have hmloadM14 := eighthMixArgsMloadM14 hmem
  have hmloadM15 := eighthMixArgsMloadM15 hmem
  have rd3109 := evm_run rd3070 with [
    raw jumpdest (by decide) (by evm_ov),
    dup6,
    push8 ⟨18446744073709551615⟩,
    swap1,
    swap3,
    swap2,
    swap3,
    push2 ⟨480⟩,
    dup3,
    dup2,
    dup7,
    push1 ⟨1⟩,
    shl,
    and,
    dup4,
    add,
    raw mload 0 (firstRoundM14Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM14
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨5⟩,
    shl,
    and,
    add,
    raw mload 0 (firstRoundM15Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM14Arg, firstRoundM15Arg] using rd3109⟩

/-- Final-flag-`0` positive-round inputs have prepared the last diagonal round-0 `mixG` call. -/
theorem validPositiveRoundMix7ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [firstRoundM15Arg
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))),
        firstRoundM14Arg
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))),
        ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (seventhMixMem3
        (sixthMixMem3
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10705 := by
  have hprefix := validPositiveRoundMix6DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using eighthMixArgsFromSeventhMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := seventhMixMem3
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))
    (startGas := 10621)
    (seventhMixMem3_size
      (sixthMixMem3_size
        (fifthMixMem3_size
          (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))))))
    hprefix

/-- Final-flag-`1` positive-round inputs have prepared the last diagonal round-0 `mixG` call. -/
theorem validPositiveRoundMix7ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [firstRoundM15Arg
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))),
        firstRoundM14Arg
          (seventhMixMem3
            (sixthMixMem3
              (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))),
        ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (seventhMixMem3
        (sixthMixMem3
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10732 := by
  have hprefix := validPositiveRoundMix6DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using eighthMixArgsFromSeventhMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := seventhMixMem3
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))
    (startGas := 10648)
    (seventhMixMem3_size
      (sixthMixMem3_size
        (fifthMixMem3_size
          (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))))))
    hprefix

end Blake2f
