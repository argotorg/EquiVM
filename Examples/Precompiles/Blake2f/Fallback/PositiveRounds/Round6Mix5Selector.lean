import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round6Mix4

/-!
# BLAKE2F fallback positive-round traces: round-6 second diagonal `mixG` argument setup

This module continues the path with at least seven rounds from PC `2610`. For round 6, the
bytecode extracts SIGMA indices `10` and `11`, loads message words `m[6]` and `m[3]`, and jumps
to the second diagonal shared `mixG` body at PC `2656`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-6 SIGMA index `10` selects bytecode memory offset `832`, i.e. `m[6]`. -/
theorem sigmaRound6Offset10 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨15⟩)
    ⟨480⟩ = (⟨832⟩ : UInt256) := by
  native_decide

/-- Round-6 SIGMA index `11` selects bytecode memory offset `736`, i.e. `m[3]`. -/
theorem sigmaRound6Offset11 : UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨11⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨736⟩ : UInt256) := by
  native_decide

abbrev round6M6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 832 32))

abbrev round6M3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 736 32))

abbrev round6M6Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M6Load mem) u64MaskWord

abbrev round6M3Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M3Load mem) u64MaskWord

private theorem round6Mix5ArgsMloadM6 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨15⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨15⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨15⟩) ⟨480⟩).toNat 32))) =
      round6M6Load mem := by
  rw [sigmaRound6Offset10]
  unfold round6M6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨832⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix5ArgsMloadM3 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨11⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round6M3Load mem := by
  rw [sigmaRound6Offset11]
  unfold round6M3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨736⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix5ArgsFromRound6Mix4Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2610⟩
        [sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round6M3Arg mem, round6M6Arg mem, ⟨2840⟩, sigmaRound6Word,
        ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2610⟩ := hprefix
  have hmloadM6 := round6Mix5ArgsMloadM6 hmem
  have hmloadM3 := round6Mix5ArgsMloadM3 hmem
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
    raw mload 0 (round6M6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM6
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨11⟩,
    shr,
    and,
    add,
    raw mload 0 (round6M3Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound6Word, u64MaskWord, round6M6Arg, round6M3Arg] using rd2656⟩

def round6Mix4ZeroMem (I : ExecutionEnv) : ByteArray :=
  round6Mix4Mem3 (round6Mix3ZeroMem I)

def round6Mix4OneMem (I : ExecutionEnv) : ByteArray :=
  round6Mix4Mem3 (round6Mix3OneMem I)

theorem round6Mix4ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round6Mix4ZeroMem I).size = 1984 := by
  unfold round6Mix4ZeroMem
  exact round6Mix4Mem3_size (round6Mix3ZeroMem_size hlen)

theorem round6Mix4OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round6Mix4OneMem I).size = 1984 := by
  unfold round6Mix4OneMem
  exact round6Mix4Mem3_size (round6Mix3OneMem_size hlen)

/-- Final-flag-`0`, at least seven rounds: the second diagonal round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix5ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round6M3Arg (round6Mix4ZeroMem I),
        round6M6Arg (round6Mix4ZeroMem I),
        ⟨2840⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix4ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 30754 := by
  have hprefix := validPositiveRound6Mix4DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix5ArgsFromRound6Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round6Mix4ZeroMem I)
    (startGas := 30661)
    (round6Mix4ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least seven rounds: the second diagonal round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix5ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round6M3Arg (round6Mix4OneMem I),
        round6M6Arg (round6Mix4OneMem I),
        ⟨2840⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix4OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 30781 := by
  have hprefix := validPositiveRound6Mix4DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix5ArgsFromRound6Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round6Mix4OneMem I)
    (startGas := 30688)
    (round6Mix4OneMem_size hlen)
    hprefix

end Blake2f
