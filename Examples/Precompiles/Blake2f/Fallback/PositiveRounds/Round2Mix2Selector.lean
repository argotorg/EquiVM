import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round2Mix1

/-!
# BLAKE2F fallback positive-round traces: round-2 third `mixG` argument setup

This module continues the path with at least three rounds from PC `1923`.  For round 2, the
bytecode extracts SIGMA indices `4` and `5`, loads message words `m[5]` and `m[2]`, and jumps to
the next shared `mixG` body at PC `1969`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-2 SIGMA index `4` selects bytecode memory offset `800`, i.e. `m[5]`. -/
theorem sigmaRound2Offset4 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨39⟩)
    ⟨480⟩ = (⟨800⟩ : UInt256) := by
  native_decide

/-- Round-2 SIGMA index `5` selects bytecode memory offset `704`, i.e. `m[2]`. -/
theorem sigmaRound2Offset5 : UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨35⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨704⟩ : UInt256) := by
  native_decide

abbrev round2M5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 800 32))

abbrev round2M2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

abbrev round2M5Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M5Load mem) u64MaskWord

abbrev round2M2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M2Load mem) u64MaskWord

private theorem round2Mix2ArgsMloadM5 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨39⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨39⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨39⟩) ⟨480⟩).toNat 32))) =
      round2M5Load mem := by
  rw [sigmaRound2Offset4]
  unfold round2M5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix2ArgsMloadM2 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨35⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round2M2Load mem := by
  rw [sigmaRound2Offset5]
  unfold round2M2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix2ArgsFromRound2Mix1Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1923⟩
        [sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round2M2Arg mem, round2M5Arg mem, ⟨2153⟩, sigmaRound2Word,
        ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1923⟩ := hprefix
  have hmloadM5 := round2Mix2ArgsMloadM5 hmem
  have hmloadM2 := round2Mix2ArgsMloadM2 hmem
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
    raw mload 0 (round2M5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM5
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨35⟩,
    shr,
    and,
    add,
    raw mload 0 (round2M2Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound2Word, u64MaskWord, round2M5Arg, round2M2Arg] using rd1969⟩

def round2Mix1ZeroMem (I : ExecutionEnv) : ByteArray :=
  round2Mix1Mem3 (round2Mix0ZeroMem I)

def round2Mix1OneMem (I : ExecutionEnv) : ByteArray :=
  round2Mix1Mem3 (round2Mix0OneMem I)

theorem round2Mix1ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix1ZeroMem I).size = 1984 := by
  unfold round2Mix1ZeroMem
  exact round2Mix1Mem3_size (round2Mix0ZeroMem_size hlen)

theorem round2Mix1OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix1OneMem I).size = 1984 := by
  unfold round2Mix1OneMem
  exact round2Mix1Mem3_size (round2Mix0OneMem_size hlen)

/-- Final-flag-`0`, at least three rounds: the third round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix2ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round2M2Arg (round2Mix1ZeroMem I),
        round2M5Arg (round2Mix1ZeroMem I),
        ⟨2153⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix1ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 15518 := by
  have hprefix := validPositiveRound2Mix1DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix2ArgsFromRound2Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix1ZeroMem I)
    (startGas := 15425)
    (round2Mix1ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least three rounds: the third round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix2ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round2M2Arg (round2Mix1OneMem I),
        round2M5Arg (round2Mix1OneMem I),
        ⟨2153⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix1OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 15545 := by
  have hprefix := validPositiveRound2Mix1DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix2ArgsFromRound2Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix1OneMem I)
    (startGas := 15452)
    (round2Mix1OneMem_size hlen)
    hprefix

end Blake2f
