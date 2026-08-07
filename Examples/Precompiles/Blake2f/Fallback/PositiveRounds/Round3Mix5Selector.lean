import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix4

/-!
# BLAKE2F fallback positive-round traces: round-3 second diagonal `mixG` argument setup

This module continues the path with at least four rounds from PC `2610`. For round 3, the
bytecode extracts SIGMA indices `10` and `11`, loads message words `m[5]` and `m[10]`, and jumps
to the second diagonal shared `mixG` body at PC `2656`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-3 SIGMA index `10` selects bytecode memory offset `800`, i.e. `m[5]`. -/
theorem sigmaRound3Offset10 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨15⟩)
    ⟨480⟩ = (⟨800⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `11` selects bytecode memory offset `960`, i.e. `m[10]`. -/
theorem sigmaRound3Offset11 : UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨11⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨960⟩ : UInt256) := by
  native_decide

abbrev round3M5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 800 32))

abbrev round3M10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 960 32))

abbrev round3M5Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M5Load mem) u64MaskWord

abbrev round3M10Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M10Load mem) u64MaskWord

private theorem round3Mix5ArgsMloadM5 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨15⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨15⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨15⟩) ⟨480⟩).toNat 32))) =
      round3M5Load mem := by
  rw [sigmaRound3Offset10]
  unfold round3M5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix5ArgsMloadM10 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨11⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M10Load mem := by
  rw [sigmaRound3Offset11]
  unfold round3M10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨960⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix5ArgsFromRound3Mix4Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2610⟩
        [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round3M10Arg mem, round3M5Arg mem, ⟨2840⟩, sigmaRound3Word,
        ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2610⟩ := hprefix
  have hmloadM5 := round3Mix5ArgsMloadM5 hmem
  have hmloadM10 := round3Mix5ArgsMloadM10 hmem
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
    raw mload 0 (round3M5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM5
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨11⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M10Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM10
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M5Arg, round3M10Arg] using rd2656⟩

def round3Mix4ZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix4Mem3 (round3Mix3ZeroMem I)

def round3Mix4OneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix4Mem3 (round3Mix3OneMem I)

theorem round3Mix4ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix4ZeroMem I).size = 1984 := by
  unfold round3Mix4ZeroMem
  exact round3Mix4Mem3_size (round3Mix3ZeroMem_size hlen)

theorem round3Mix4OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix4OneMem I).size = 1984 := by
  unfold round3Mix4OneMem
  exact round3Mix4Mem3_size (round3Mix3OneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the second diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix5ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round3M10Arg (round3Mix4ZeroMem I),
        round3M5Arg (round3Mix4ZeroMem I),
        ⟨2840⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix4ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 20221 := by
  have hprefix := validPositiveRound3Mix4DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix5ArgsFromRound3Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix4ZeroMem I)
    (startGas := 20128)
    (round3Mix4ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the second diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix5ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round3M10Arg (round3Mix4OneMem I),
        round3M5Arg (round3Mix4OneMem I),
        ⟨2840⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix4OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 20248 := by
  have hprefix := validPositiveRound3Mix4DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix5ArgsFromRound3Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix4OneMem I)
    (startGas := 20155)
    (round3Mix4OneMem_size hlen)
    hprefix

end Blake2f
