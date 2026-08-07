import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round2Mix5

/-!
# BLAKE2F fallback positive-round traces: round-2 third diagonal `mixG` argument setup

This module continues the path with at least three rounds from PC `2840`. For round 2, the
bytecode extracts SIGMA indices `12` and `13`, loads message words `m[7]` and `m[1]`, and jumps to
the third diagonal shared `mixG` body at PC `2886`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-2 SIGMA index `12` selects bytecode memory offset `864`, i.e. `m[7]`. -/
theorem sigmaRound2Offset12 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨7⟩)
    ⟨480⟩ = (⟨864⟩ : UInt256) := by
  native_decide

/-- Round-2 SIGMA index `13` selects bytecode memory offset `672`, i.e. `m[1]`. -/
theorem sigmaRound2Offset13 : UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨3⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨672⟩ : UInt256) := by
  native_decide

abbrev round2M7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 864 32))

abbrev round2M1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 672 32))

abbrev round2M7Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M7Load mem) u64MaskWord

abbrev round2M1Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M1Load mem) u64MaskWord

private theorem round2Mix6ArgsMloadM7 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨7⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨7⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨7⟩) ⟨480⟩).toNat 32))) =
      round2M7Load mem := by
  rw [sigmaRound2Offset12]
  unfold round2M7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix6ArgsMloadM1 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨3⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round2M1Load mem := by
  rw [sigmaRound2Offset13]
  unfold round2M1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix6ArgsFromRound2Mix5Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2840⟩
        [sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round2M1Arg mem, round2M7Arg mem, ⟨3070⟩, sigmaRound2Word,
        ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2840⟩ := hprefix
  have hmloadM7 := round2Mix6ArgsMloadM7 hmem
  have hmloadM1 := round2Mix6ArgsMloadM1 hmem
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
    raw mload 0 (round2M7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM7
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨3⟩,
    shr,
    and,
    add,
    raw mload 0 (round2M1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM1
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound2Word, u64MaskWord, round2M7Arg, round2M1Arg] using rd2886⟩

def round2Mix5ZeroMem (I : ExecutionEnv) : ByteArray :=
  round2Mix5Mem3 (round2Mix4ZeroMem I)

def round2Mix5OneMem (I : ExecutionEnv) : ByteArray :=
  round2Mix5Mem3 (round2Mix4OneMem I)

theorem round2Mix5ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix5ZeroMem I).size = 1984 := by
  unfold round2Mix5ZeroMem
  exact round2Mix5Mem3_size (round2Mix4ZeroMem_size hlen)

theorem round2Mix5OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix5OneMem I).size = 1984 := by
  unfold round2Mix5OneMem
  exact round2Mix5Mem3_size (round2Mix4OneMem_size hlen)

/-- Final-flag-`0`, at least three rounds: the third diagonal round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix6ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round2M1Arg (round2Mix5ZeroMem I),
        round2M7Arg (round2Mix5ZeroMem I),
        ⟨3070⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix5ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17168 := by
  have hprefix := validPositiveRound2Mix5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix6ArgsFromRound2Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix5ZeroMem I)
    (startGas := 17075)
    (round2Mix5ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least three rounds: the third diagonal round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix6ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round2M1Arg (round2Mix5OneMem I),
        round2M7Arg (round2Mix5OneMem I),
        ⟨3070⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix5OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17195 := by
  have hprefix := validPositiveRound2Mix5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix6ArgsFromRound2Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix5OneMem I)
    (startGas := 17102)
    (round2Mix5OneMem_size hlen)
    hprefix

end Blake2f
