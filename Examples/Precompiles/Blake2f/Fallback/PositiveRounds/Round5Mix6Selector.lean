import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix5

/-!
# BLAKE2F fallback positive-round traces: round-5 third diagonal `mixG` argument setup

This module continues the path with at least six rounds from PC `2840`. For round 5, the
bytecode extracts SIGMA indices `12` and `13`, loads message words `m[15]` and `m[14]`, and jumps
to the third diagonal shared `mixG` body at PC `2886`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-5 SIGMA index `12` selects bytecode memory offset `1120`, i.e. `m[15]`. -/
theorem sigmaRound5Offset12 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨7⟩)
    ⟨480⟩ = (⟨1120⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `13` selects bytecode memory offset `1088`, i.e. `m[14]`. -/
theorem sigmaRound5Offset13 : UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨3⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1088⟩ : UInt256) := by
  native_decide

abbrev round5M15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1120 32))

abbrev round5M14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1088 32))

abbrev round5M15Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M15Load mem) u64MaskWord

abbrev round5M14Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M14Load mem) u64MaskWord

private theorem round5Mix6ArgsMloadM15 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨7⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨7⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨7⟩) ⟨480⟩).toNat 32))) =
      round5M15Load mem := by
  rw [sigmaRound5Offset12]
  unfold round5M15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1120⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix6ArgsMloadM14 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨3⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M14Load mem := by
  rw [sigmaRound5Offset13]
  unfold round5M14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1088⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix6ArgsFromRound5Mix5Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2840⟩
        [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round5M14Arg mem, round5M15Arg mem, ⟨3070⟩, sigmaRound5Word,
        ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2840⟩ := hprefix
  have hmloadM15 := round5Mix6ArgsMloadM15 hmem
  have hmloadM14 := round5Mix6ArgsMloadM14 hmem
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
    raw mload 0 (round5M15Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM15
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨3⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M14Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM14
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M15Arg, round5M14Arg] using rd2886⟩

def round5Mix5ZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix5Mem3 (round5Mix4ZeroMem I)

def round5Mix5OneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix5Mem3 (round5Mix4OneMem I)

theorem round5Mix5ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix5ZeroMem I).size = 1984 := by
  unfold round5Mix5ZeroMem
  exact round5Mix5Mem3_size (round5Mix4ZeroMem_size hlen)

theorem round5Mix5OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix5OneMem I).size = 1984 := by
  unfold round5Mix5OneMem
  exact round5Mix5Mem3_size (round5Mix4OneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the third diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix6ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round5M14Arg (round5Mix5ZeroMem I),
        round5M15Arg (round5Mix5ZeroMem I),
        ⟨3070⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix5ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 27635 := by
  have hprefix := validPositiveRound5Mix5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix6ArgsFromRound5Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix5ZeroMem I)
    (startGas := 27542)
    (round5Mix5ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the third diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix6ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round5M14Arg (round5Mix5OneMem I),
        round5M15Arg (round5Mix5OneMem I),
        ⟨3070⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix5OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 27662 := by
  have hprefix := validPositiveRound5Mix5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix6ArgsFromRound5Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix5OneMem I)
    (startGas := 27569)
    (round5Mix5OneMem_size hlen)
    hprefix

end Blake2f
