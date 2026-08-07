import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix0

/-!
# BLAKE2F fallback positive-round traces: second `mixG` argument setup

This module continues the first positive-round body from PC `1693`.  The bytecode extracts
round-0 SIGMA indices `2` and `3`, loads message words `m[2]` and `m[3]`, and jumps to the next
shared `mixG` body at PC `1739`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-0 SIGMA index `2` selects bytecode memory offset `704`, i.e. `m[2]`. -/
theorem sigmaRound0Offset2 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨47⟩)
    ⟨480⟩ = (⟨704⟩ : UInt256) := by
  native_decide

/-- Round-0 SIGMA index `3` selects bytecode memory offset `736`, i.e. `m[3]`. -/
theorem sigmaRound0Offset3 : UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨43⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨736⟩ : UInt256) := by
  native_decide

/-- First round's third message load, selected by SIGMA index `2`. -/
abbrev firstRoundM2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

/-- First round's fourth message load, selected by SIGMA index `3`. -/
abbrev firstRoundM3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 736 32))

/-- First round's third message argument, selected by SIGMA index `2`. -/
abbrev firstRoundM2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM2Load mem) u64MaskWord

/-- First round's fourth message argument, selected by SIGMA index `3`. -/
abbrev firstRoundM3Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM3Load mem) u64MaskWord

private theorem secondMixArgsMloadM2 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨47⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨47⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨47⟩) ⟨480⟩).toNat 32))) =
      firstRoundM2Load mem := by
  rw [sigmaRound0Offset2]
  unfold firstRoundM2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem secondMixArgsMloadM3 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨43⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      firstRoundM3Load mem := by
  rw [sigmaRound0Offset3]
  unfold firstRoundM3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨736⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem secondMixArgsFromFirstMixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1693⟩
        [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [firstRoundM3Arg mem, firstRoundM2Arg mem, ⟨1923⟩, sigmaRound0Word,
        ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1693⟩ := hprefix
  have hmloadM2 := secondMixArgsMloadM2 hmem
  have hmloadM3 := secondMixArgsMloadM3 hmem
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
    raw mload 0 (firstRoundM2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM2
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨43⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM3
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM2Arg, firstRoundM3Arg] using rd1739⟩

/-- Final-flag-`0` positive-round inputs have prepared the second round-0 `mixG` call. -/
theorem validPositiveRoundMix1ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [firstRoundM3Arg (firstMixMem3 (v13MixedMem I)),
        firstRoundM2Arg (firstMixMem3 (v13MixedMem I)), ⟨1923⟩, sigmaRound0Word,
        ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (firstMixMem3 (v13MixedMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8236 := by
  have hprefix := validPositiveRoundMix0DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using secondMixArgsFromFirstMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := firstMixMem3 (v13MixedMem I)) (startGas := 8143)
    (firstMixMem3_size (v13MixedMem_size I hlen)) hprefix

/-- Final-flag-`1` positive-round inputs have prepared the second round-0 `mixG` call. -/
theorem validPositiveRoundMix1ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [firstRoundM3Arg (firstMixMem3 (v14FinalFlagMem I)),
        firstRoundM2Arg (firstMixMem3 (v14FinalFlagMem I)), ⟨1923⟩, sigmaRound0Word,
        ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (firstMixMem3 (v14FinalFlagMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8263 := by
  have hprefix := validPositiveRoundMix0DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using secondMixArgsFromFirstMixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := firstMixMem3 (v14FinalFlagMem I)) (startGas := 8170)
    (firstMixMem3_size (v14FinalFlagMem_size I hlen)) hprefix

end Blake2f
