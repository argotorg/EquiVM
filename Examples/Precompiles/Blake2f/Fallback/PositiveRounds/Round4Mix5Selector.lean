import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round4Mix4

/-!
# BLAKE2F fallback positive-round traces: round-4 second diagonal `mixG` argument setup

This module continues the path with at least five rounds from PC `2610`. For round 4, the
bytecode extracts SIGMA indices `10` and `11`, loads message words `m[11]` and `m[12]`, and jumps
to the second diagonal shared `mixG` body at PC `2656`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-4 SIGMA index `10` selects bytecode memory offset `992`, i.e. `m[11]`. -/
theorem sigmaRound4Offset10 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨15⟩)
    ⟨480⟩ = (⟨992⟩ : UInt256) := by
  native_decide

/-- Round-4 SIGMA index `11` selects bytecode memory offset `1024`, i.e. `m[12]`. -/
theorem sigmaRound4Offset11 : UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨11⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1024⟩ : UInt256) := by
  native_decide

abbrev round4M11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 992 32))

abbrev round4M12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1024 32))

abbrev round4M11Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M11Load mem) u64MaskWord

abbrev round4M12Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M12Load mem) u64MaskWord

private theorem round4Mix5ArgsMloadM11 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨15⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨15⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨15⟩) ⟨480⟩).toNat 32))) =
      round4M11Load mem := by
  rw [sigmaRound4Offset10]
  unfold round4M11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix5ArgsMloadM12 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨11⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round4M12Load mem := by
  rw [sigmaRound4Offset11]
  unfold round4M12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix5ArgsFromRound4Mix4Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2610⟩
        [sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round4M12Arg mem, round4M11Arg mem, ⟨2840⟩, sigmaRound4Word,
        ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2610⟩ := hprefix
  have hmloadM11 := round4Mix5ArgsMloadM11 hmem
  have hmloadM12 := round4Mix5ArgsMloadM12 hmem
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
    raw mload 0 (round4M11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM11
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨11⟩,
    shr,
    and,
    add,
    raw mload 0 (round4M12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound4Word, u64MaskWord, round4M11Arg, round4M12Arg] using rd2656⟩

def round4Mix4ZeroMem (I : ExecutionEnv) : ByteArray :=
  round4Mix4Mem3 (round4Mix3ZeroMem I)

def round4Mix4OneMem (I : ExecutionEnv) : ByteArray :=
  round4Mix4Mem3 (round4Mix3OneMem I)

theorem round4Mix4ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix4ZeroMem I).size = 1984 := by
  unfold round4Mix4ZeroMem
  exact round4Mix4Mem3_size (round4Mix3ZeroMem_size hlen)

theorem round4Mix4OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix4OneMem I).size = 1984 := by
  unfold round4Mix4OneMem
  exact round4Mix4Mem3_size (round4Mix3OneMem_size hlen)

/-- Final-flag-`0`, at least five rounds: the second diagonal round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix5ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round4M12Arg (round4Mix4ZeroMem I),
        round4M11Arg (round4Mix4ZeroMem I),
        ⟨2840⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix4ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 23710 := by
  have hprefix := validPositiveRound4Mix4DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix5ArgsFromRound4Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix4ZeroMem I)
    (startGas := 23617)
    (round4Mix4ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least five rounds: the second diagonal round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix5ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round4M12Arg (round4Mix4OneMem I),
        round4M11Arg (round4Mix4OneMem I),
        ⟨2840⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix4OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 23737 := by
  have hprefix := validPositiveRound4Mix4DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix5ArgsFromRound4Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix4OneMem I)
    (startGas := 23644)
    (round4Mix4OneMem_size hlen)
    hprefix

end Blake2f
