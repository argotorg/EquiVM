import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix1

/-!
# BLAKE2F fallback positive-round traces: third `mixG` argument setup

This module continues the first positive-round body from PC `1923`.  The bytecode extracts
round-0 SIGMA indices `4` and `5`, loads message words `m[4]` and `m[5]`, and jumps to the next
shared `mixG` body at PC `1969`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-0 SIGMA index `4` selects bytecode memory offset `768`, i.e. `m[4]`. -/
theorem sigmaRound0Offset4 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨39⟩)
    ⟨480⟩ = (⟨768⟩ : UInt256) := by
  native_decide

/-- Round-0 SIGMA index `5` selects bytecode memory offset `800`, i.e. `m[5]`. -/
theorem sigmaRound0Offset5 : UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨35⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨800⟩ : UInt256) := by
  native_decide

abbrev firstRoundM4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 768 32))

abbrev firstRoundM5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 800 32))

abbrev firstRoundM4Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM4Load mem) u64MaskWord

abbrev firstRoundM5Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM5Load mem) u64MaskWord

private theorem thirdMixArgsMloadM4 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨39⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨39⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨39⟩) ⟨480⟩).toNat 32))) =
      firstRoundM4Load mem := by
  rw [sigmaRound0Offset4]
  unfold firstRoundM4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨768⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem thirdMixArgsMloadM5 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨35⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      firstRoundM5Load mem := by
  rw [sigmaRound0Offset5]
  unfold firstRoundM5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem thirdMixArgsFromSecondMixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1923⟩
        [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [firstRoundM5Arg mem, firstRoundM4Arg mem, ⟨2153⟩, sigmaRound0Word,
        ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1923⟩ := hprefix
  have hmloadM4 := thirdMixArgsMloadM4 hmem
  have hmloadM5 := thirdMixArgsMloadM5 hmem
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
    raw mload 0 (firstRoundM4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM4
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨35⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM5
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM4Arg, firstRoundM5Arg] using rd1969⟩

/-- Final-flag-`0` positive-round inputs have prepared the third round-0 `mixG` call. -/
theorem validPositiveRoundMix2ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [firstRoundM5Arg (secondMixMem3 (firstMixMem3 (v13MixedMem I))),
        firstRoundM4Arg (secondMixMem3 (firstMixMem3 (v13MixedMem I))), ⟨2153⟩,
        sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (secondMixMem3 (firstMixMem3 (v13MixedMem I)))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8650 := by
  have hprefix := validPositiveRoundMix1DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using thirdMixArgsFromSecondMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := secondMixMem3 (firstMixMem3 (v13MixedMem I))) (startGas := 8557)
    (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))) hprefix

/-- Final-flag-`1` positive-round inputs have prepared the third round-0 `mixG` call. -/
theorem validPositiveRoundMix2ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [firstRoundM5Arg (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))),
        firstRoundM4Arg (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))), ⟨2153⟩,
        sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8677 := by
  have hprefix := validPositiveRoundMix1DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using thirdMixArgsFromSecondMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))) (startGas := 8584)
    (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))) hprefix

end Blake2f
