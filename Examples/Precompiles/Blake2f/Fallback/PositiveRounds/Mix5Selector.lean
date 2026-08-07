import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix4

/-!
# BLAKE2F fallback positive-round traces: sixth `mixG` argument setup

This module continues the first positive-round body from PC `2610`.  The bytecode extracts
round-0 SIGMA indices `10` and `11`, loads message words `m[10]` and `m[11]`, and jumps to the
second diagonal shared `mixG` body at PC `2656`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-0 SIGMA index `10` selects bytecode memory offset `960`, i.e. `m[10]`. -/
theorem sigmaRound0Offset10 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨15⟩)
    ⟨480⟩ = (⟨960⟩ : UInt256) := by
  native_decide

/-- Round-0 SIGMA index `11` selects bytecode memory offset `992`, i.e. `m[11]`. -/
theorem sigmaRound0Offset11 : UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨11⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨992⟩ : UInt256) := by
  native_decide

abbrev firstRoundM10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 960 32))

abbrev firstRoundM11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 992 32))

abbrev firstRoundM10Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM10Load mem) u64MaskWord

abbrev firstRoundM11Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM11Load mem) u64MaskWord

private theorem sixthMixArgsMloadM10 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨15⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨15⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨15⟩) ⟨480⟩).toNat 32))) =
      firstRoundM10Load mem := by
  rw [sigmaRound0Offset10]
  unfold firstRoundM10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨960⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem sixthMixArgsMloadM11 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨11⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      firstRoundM11Load mem := by
  rw [sigmaRound0Offset11]
  unfold firstRoundM11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem sixthMixArgsFromFifthMixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2610⟩
        [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [firstRoundM11Arg mem, firstRoundM10Arg mem, ⟨2840⟩, sigmaRound0Word,
        ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2610⟩ := hprefix
  have hmloadM10 := sixthMixArgsMloadM10 hmem
  have hmloadM11 := sixthMixArgsMloadM11 hmem
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
    raw mload 0 (firstRoundM10Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM10
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨11⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM11Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM10Arg, firstRoundM11Arg] using rd2656⟩

/-- Final-flag-`0` positive-round inputs have prepared the second diagonal round-0 `mixG` call. -/
theorem validPositiveRoundMix5ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [firstRoundM11Arg
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))),
        firstRoundM10Arg
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))),
        ⟨2840⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9886 := by
  have hprefix := validPositiveRoundMix4DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using sixthMixArgsFromFifthMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))
    (startGas := 9793)
    (fifthMixMem3_size
      (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))))
    hprefix

/-- Final-flag-`1` positive-round inputs have prepared the second diagonal round-0 `mixG` call. -/
theorem validPositiveRoundMix5ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [firstRoundM11Arg
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))),
        firstRoundM10Arg
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))),
        ⟨2840⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9913 := by
  have hprefix := validPositiveRoundMix4DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using sixthMixArgsFromFifthMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))
    (startGas := 9820)
    (fifthMixMem3_size
      (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))))
    hprefix

end Blake2f
