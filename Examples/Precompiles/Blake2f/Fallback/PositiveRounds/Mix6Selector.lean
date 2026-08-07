import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix5

/-!
# BLAKE2F fallback positive-round traces: seventh `mixG` argument setup

This module continues the first positive-round body from PC `2840`.  The bytecode extracts
round-0 SIGMA indices `12` and `13`, loads message words `m[12]` and `m[13]`, and jumps to the
third diagonal shared `mixG` body at PC `2886`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-0 SIGMA index `12` selects bytecode memory offset `1024`, i.e. `m[12]`. -/
theorem sigmaRound0Offset12 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨7⟩)
    ⟨480⟩ = (⟨1024⟩ : UInt256) := by
  native_decide

/-- Round-0 SIGMA index `13` selects bytecode memory offset `1056`, i.e. `m[13]`. -/
theorem sigmaRound0Offset13 : UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨3⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1056⟩ : UInt256) := by
  native_decide

abbrev firstRoundM12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1024 32))

abbrev firstRoundM13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1056 32))

abbrev firstRoundM12Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM12Load mem) u64MaskWord

abbrev firstRoundM13Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM13Load mem) u64MaskWord

private theorem seventhMixArgsMloadM12 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨7⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨7⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨7⟩) ⟨480⟩).toNat 32))) =
      firstRoundM12Load mem := by
  rw [sigmaRound0Offset12]
  unfold firstRoundM12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem seventhMixArgsMloadM13 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨3⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      firstRoundM13Load mem := by
  rw [sigmaRound0Offset13]
  unfold firstRoundM13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1056⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem seventhMixArgsFromSixthMixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2840⟩
        [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [firstRoundM13Arg mem, firstRoundM12Arg mem, ⟨3070⟩, sigmaRound0Word,
        ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2840⟩ := hprefix
  have hmloadM12 := seventhMixArgsMloadM12 hmem
  have hmloadM13 := seventhMixArgsMloadM13 hmem
  have rd2886 := evm_run rd2840 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨3070⟩,
    push2 ⟨2886⟩,
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
    push1 ⟨7⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (firstRoundM12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨3⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM13Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM13
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM12Arg, firstRoundM13Arg] using rd2886⟩

/-- Final-flag-`0` positive-round inputs have prepared the third diagonal round-0 `mixG` call. -/
theorem validPositiveRoundMix6ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [firstRoundM13Arg
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))),
        firstRoundM12Arg
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))),
        ⟨3070⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10300 := by
  have hprefix := validPositiveRoundMix5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using seventhMixArgsFromSixthMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := sixthMixMem3
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))
    (startGas := 10207)
    (sixthMixMem3_size
      (fifthMixMem3_size
        (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))))))
    hprefix

/-- Final-flag-`1` positive-round inputs have prepared the third diagonal round-0 `mixG` call. -/
theorem validPositiveRoundMix6ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [firstRoundM13Arg
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))),
        firstRoundM12Arg
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))),
        ⟨3070⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10327 := by
  have hprefix := validPositiveRoundMix5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using seventhMixArgsFromSixthMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := sixthMixMem3
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))
    (startGas := 10234)
    (sixthMixMem3_size
      (fifthMixMem3_size
        (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))))))
    hprefix

end Blake2f
