import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix2

/-!
# BLAKE2F fallback positive-round traces: fourth `mixG` argument setup

This module continues the first positive-round body from PC `2153`.  The bytecode extracts
round-0 SIGMA indices `6` and `7`, loads message words `m[6]` and `m[7]`, and jumps to the next
shared `mixG` body at PC `2199`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-0 SIGMA index `6` selects bytecode memory offset `832`, i.e. `m[6]`. -/
theorem sigmaRound0Offset6 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨31⟩)
    ⟨480⟩ = (⟨832⟩ : UInt256) := by
  native_decide

/-- Round-0 SIGMA index `7` selects bytecode memory offset `864`, i.e. `m[7]`. -/
theorem sigmaRound0Offset7 : UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨27⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨864⟩ : UInt256) := by
  native_decide

abbrev firstRoundM6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 832 32))

abbrev firstRoundM7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 864 32))

abbrev firstRoundM6Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM6Load mem) u64MaskWord

abbrev firstRoundM7Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM7Load mem) u64MaskWord

private theorem fourthMixArgsMloadM6 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨31⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨31⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨31⟩) ⟨480⟩).toNat 32))) =
      firstRoundM6Load mem := by
  rw [sigmaRound0Offset6]
  unfold firstRoundM6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨832⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fourthMixArgsMloadM7 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨27⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      firstRoundM7Load mem := by
  rw [sigmaRound0Offset7]
  unfold firstRoundM7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fourthMixArgsFromThirdMixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2153⟩
        [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [firstRoundM7Arg mem, firstRoundM6Arg mem, ⟨2383⟩, sigmaRound0Word,
        ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2153⟩ := hprefix
  have hmloadM6 := fourthMixArgsMloadM6 hmem
  have hmloadM7 := fourthMixArgsMloadM7 hmem
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
    raw mload 0 (firstRoundM6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM6
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨27⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM7
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM6Arg, firstRoundM7Arg] using rd2199⟩

/-- Final-flag-`0` positive-round inputs have prepared the fourth round-0 `mixG` call. -/
theorem validPositiveRoundMix3ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [firstRoundM7Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))),
        firstRoundM6Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))),
        ⟨2383⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9064 := by
  have hprefix := validPositiveRoundMix2DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using fourthMixArgsFromThirdMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))) (startGas := 8971)
    (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))) hprefix

/-- Final-flag-`1` positive-round inputs have prepared the fourth round-0 `mixG` call. -/
theorem validPositiveRoundMix3ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [firstRoundM7Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))),
        firstRoundM6Arg (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))),
        ⟨2383⟩, sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9091 := by
  have hprefix := validPositiveRoundMix2DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using fourthMixArgsFromThirdMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))) (startGas := 8998)
    (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))) hprefix

end Blake2f
