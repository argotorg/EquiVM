import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round2Mix0

/-!
# BLAKE2F fallback positive-round traces: round-2 second `mixG` argument setup

This module continues the path with at least three rounds from PC `1693`.  For round 2, the
bytecode extracts SIGMA indices `2` and `3`, loads message words `m[12]` and `m[0]`, and jumps to
the next shared `mixG` body at PC `1739`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-2 SIGMA index `2` selects bytecode memory offset `1024`, i.e. `m[12]`. -/
theorem sigmaRound2Offset2 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨47⟩)
    ⟨480⟩ = (⟨1024⟩ : UInt256) := by
  native_decide

/-- Round-2 SIGMA index `3` selects bytecode memory offset `640`, i.e. `m[0]`. -/
theorem sigmaRound2Offset3 : UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨43⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨640⟩ : UInt256) := by
  native_decide

abbrev round2M12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1024 32))

abbrev round2M0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 640 32))

abbrev round2M12Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M12Load mem) u64MaskWord

abbrev round2M0Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M0Load mem) u64MaskWord

private theorem round2Mix1ArgsMloadM12 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨47⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨47⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨47⟩) ⟨480⟩).toNat 32))) =
      round2M12Load mem := by
  rw [sigmaRound2Offset2]
  unfold round2M12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix1ArgsMloadM0 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨43⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round2M0Load mem := by
  rw [sigmaRound2Offset3]
  unfold round2M0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix1ArgsFromRound2Mix0Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1693⟩
        [sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round2M0Arg mem, round2M12Arg mem, ⟨1923⟩, sigmaRound2Word,
        ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1693⟩ := hprefix
  have hmloadM12 := round2Mix1ArgsMloadM12 hmem
  have hmloadM0 := round2Mix1ArgsMloadM0 hmem
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
    raw mload 0 (round2M12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨43⟩,
    shr,
    and,
    add,
    raw mload 0 (round2M0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound2Word, u64MaskWord, round2M12Arg, round2M0Arg] using rd1739⟩

def round2Mix0ZeroMem (I : ExecutionEnv) : ByteArray :=
  round2Mix0Mem3 (round1DoneZeroMem I)

def round2Mix0OneMem (I : ExecutionEnv) : ByteArray :=
  round2Mix0Mem3 (round1DoneOneMem I)

theorem round2Mix0ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix0ZeroMem I).size = 1984 := by
  unfold round2Mix0ZeroMem
  exact round2Mix0Mem3_size (round1DoneZeroMem_size hlen)

theorem round2Mix0OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix0OneMem I).size = 1984 := by
  unfold round2Mix0OneMem
  exact round2Mix0Mem3_size (round1DoneOneMem_size hlen)

/-- Final-flag-`0`, at least three rounds: the second round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix1ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round2M0Arg (round2Mix0ZeroMem I),
        round2M12Arg (round2Mix0ZeroMem I),
        ⟨1923⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix0ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k
      ((((((((((13216 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23) + 212) + 315 + 93) := by
  have hprefix := validPositiveRound2Mix0DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round2Mix1ArgsFromRound2Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix0ZeroMem I)
    (startGas := ((((((((((13216 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23) + 212) + 315))
    (round2Mix0ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least three rounds: the second round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix1ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round2M0Arg (round2Mix0OneMem I),
        round2M12Arg (round2Mix0OneMem I),
        ⟨1923⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix0OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k
      ((((((((((13243 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23) + 212) + 315 + 93) := by
  have hprefix := validPositiveRound2Mix0DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round2Mix1ArgsFromRound2Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix0OneMem I)
    (startGas := ((((((((((13243 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23) + 212) + 315))
    (round2Mix0OneMem_size hlen)
    hprefix

end Blake2f
