import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round6Mix5

/-!
# BLAKE2F fallback positive-round traces: round-6 third diagonal `mixG` argument setup

This module continues the path with at least seven rounds from PC `2840`. For round 6, the
bytecode extracts SIGMA indices `12` and `13`, loads message words `m[9]` and `m[2]`, and jumps
to the third diagonal shared `mixG` body at PC `2886`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-6 SIGMA index `12` selects bytecode memory offset `928`, i.e. `m[9]`. -/
theorem sigmaRound6Offset12 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨7⟩)
    ⟨480⟩ = (⟨928⟩ : UInt256) := by
  native_decide

/-- Round-6 SIGMA index `13` selects bytecode memory offset `704`, i.e. `m[2]`. -/
theorem sigmaRound6Offset13 : UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨3⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨704⟩ : UInt256) := by
  native_decide

abbrev round6M9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 928 32))

abbrev round6M2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

abbrev round6M9Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M9Load mem) u64MaskWord

abbrev round6M2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M2Load mem) u64MaskWord

private theorem round6Mix6ArgsMloadM9 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨7⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨7⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨7⟩) ⟨480⟩).toNat 32))) =
      round6M9Load mem := by
  rw [sigmaRound6Offset12]
  unfold round6M9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix6ArgsMloadM2 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨3⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round6M2Load mem := by
  rw [sigmaRound6Offset13]
  unfold round6M2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix6ArgsFromRound6Mix5Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2840⟩
        [sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round6M2Arg mem, round6M9Arg mem, ⟨3070⟩, sigmaRound6Word,
        ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2840⟩ := hprefix
  have hmloadM9 := round6Mix6ArgsMloadM9 hmem
  have hmloadM2 := round6Mix6ArgsMloadM2 hmem
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
    raw mload 0 (round6M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨3⟩,
    shr,
    and,
    add,
    raw mload 0 (round6M2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM2
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound6Word, u64MaskWord, round6M9Arg, round6M2Arg] using rd2886⟩

def round6Mix5ZeroMem (I : ExecutionEnv) : ByteArray :=
  round6Mix5Mem3 (round6Mix4ZeroMem I)

def round6Mix5OneMem (I : ExecutionEnv) : ByteArray :=
  round6Mix5Mem3 (round6Mix4OneMem I)

theorem round6Mix5ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round6Mix5ZeroMem I).size = 1984 := by
  unfold round6Mix5ZeroMem
  exact round6Mix5Mem3_size (round6Mix4ZeroMem_size hlen)

theorem round6Mix5OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round6Mix5OneMem I).size = 1984 := by
  unfold round6Mix5OneMem
  exact round6Mix5Mem3_size (round6Mix4OneMem_size hlen)

/-- Final-flag-`0`, at least seven rounds: the third diagonal round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix6ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2886⟩
      [round6M2Arg (round6Mix5ZeroMem I),
        round6M9Arg (round6Mix5ZeroMem I),
        ⟨3070⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix5ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 31168 := by
  have hprefix := validPositiveRound6Mix5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix6ArgsFromRound6Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round6Mix5ZeroMem I)
    (startGas := 31075)
    (round6Mix5ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least seven rounds: the third diagonal round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix6ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2886⟩
      [round6M2Arg (round6Mix5OneMem I),
        round6M9Arg (round6Mix5OneMem I),
        ⟨3070⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix5OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 31195 := by
  have hprefix := validPositiveRound6Mix5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix6ArgsFromRound6Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round6Mix5OneMem I)
    (startGas := 31102)
    (round6Mix5OneMem_size hlen)
    hprefix

end Blake2f
