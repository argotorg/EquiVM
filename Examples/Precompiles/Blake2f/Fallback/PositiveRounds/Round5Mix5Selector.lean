import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix4

/-!
# BLAKE2F fallback positive-round traces: round-5 second diagonal `mixG` argument setup

This module continues the path with at least six rounds from PC `2610`. For round 5, the
bytecode extracts SIGMA indices `10` and `11`, loads message words `m[7]` and `m[5]`, and jumps
to the second diagonal shared `mixG` body at PC `2656`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-5 SIGMA index `10` selects bytecode memory offset `864`, i.e. `m[7]`. -/
theorem sigmaRound5Offset10 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨15⟩)
    ⟨480⟩ = (⟨864⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `11` selects bytecode memory offset `800`, i.e. `m[5]`. -/
theorem sigmaRound5Offset11 : UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨11⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨800⟩ : UInt256) := by
  native_decide

abbrev round5M7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 864 32))

abbrev round5M5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 800 32))

abbrev round5M7Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M7Load mem) u64MaskWord

abbrev round5M5Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M5Load mem) u64MaskWord

private theorem round5Mix5ArgsMloadM7 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨15⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨15⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨15⟩) ⟨480⟩).toNat 32))) =
      round5M7Load mem := by
  rw [sigmaRound5Offset10]
  unfold round5M7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix5ArgsMloadM5 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨11⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨11⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M5Load mem := by
  rw [sigmaRound5Offset11]
  unfold round5M5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix5ArgsFromRound5Mix4Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2610⟩
        [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2656⟩
      [round5M5Arg mem, round5M7Arg mem, ⟨2840⟩, sigmaRound5Word,
        ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2610⟩ := hprefix
  have hmloadM7 := round5Mix5ArgsMloadM7 hmem
  have hmloadM5 := round5Mix5ArgsMloadM5 hmem
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
    raw mload 0 (round5M7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM7
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨11⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M5Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M7Arg, round5M5Arg] using rd2656⟩

def round5Mix4ZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix4Mem3 (round5Mix3ZeroMem I)

def round5Mix4OneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix4Mem3 (round5Mix3OneMem I)

theorem round5Mix4ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix4ZeroMem I).size = 1984 := by
  unfold round5Mix4ZeroMem
  exact round5Mix4Mem3_size (round5Mix3ZeroMem_size hlen)

theorem round5Mix4OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix4OneMem I).size = 1984 := by
  unfold round5Mix4OneMem
  exact round5Mix4Mem3_size (round5Mix3OneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the second diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix5ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2656⟩
      [round5M5Arg (round5Mix4ZeroMem I),
        round5M7Arg (round5Mix4ZeroMem I),
        ⟨2840⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix4ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 27221 := by
  have hprefix := validPositiveRound5Mix4DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix5ArgsFromRound5Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix4ZeroMem I)
    (startGas := 27128)
    (round5Mix4ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the second diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix5ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2656⟩
      [round5M5Arg (round5Mix4OneMem I),
        round5M7Arg (round5Mix4OneMem I),
        ⟨2840⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix4OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 27248 := by
  have hprefix := validPositiveRound5Mix4DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix5ArgsFromRound5Mix4Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix4OneMem I)
    (startGas := 27155)
    (round5Mix4OneMem_size hlen)
    hprefix

end Blake2f
