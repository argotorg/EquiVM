import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix0

/-!
# BLAKE2F fallback positive-round traces: round-5 second `mixG` argument setup

This module continues the path with at least six rounds from PC `1693`. For round 5, the
bytecode extracts SIGMA indices `2` and `3`, loads message words `m[6]` and `m[10]`, and jumps to
the next shared `mixG` body at PC `1739`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-5 SIGMA index `2` selects bytecode memory offset `832`, i.e. `m[6]`. -/
theorem sigmaRound5Offset2 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨47⟩)
    ⟨480⟩ = (⟨832⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `3` selects bytecode memory offset `960`, i.e. `m[10]`. -/
theorem sigmaRound5Offset3 : UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨43⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨960⟩ : UInt256) := by
  native_decide

abbrev round5M6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 832 32))

abbrev round5M10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 960 32))

abbrev round5M6Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M6Load mem) u64MaskWord

abbrev round5M10Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M10Load mem) u64MaskWord

private theorem round5Mix1ArgsMloadM6 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨47⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨47⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨47⟩) ⟨480⟩).toNat 32))) =
      round5M6Load mem := by
  rw [sigmaRound5Offset2]
  unfold round5M6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨832⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix1ArgsMloadM10 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨43⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M10Load mem := by
  rw [sigmaRound5Offset3]
  unfold round5M10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨960⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix1ArgsFromRound5Mix0Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1693⟩
        [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round5M10Arg mem, round5M6Arg mem, ⟨1923⟩, sigmaRound5Word,
        ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1693⟩ := hprefix
  have hmloadM6 := round5Mix1ArgsMloadM6 hmem
  have hmloadM10 := round5Mix1ArgsMloadM10 hmem
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
    raw mload 0 (round5M6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM6
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨43⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M10Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M6Arg, round5M10Arg] using rd1739⟩

def round5Mix0ZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix0Mem3 (round4DoneZeroMem I)

def round5Mix0OneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix0Mem3 (round4DoneOneMem I)

theorem round5Mix0ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix0ZeroMem I).size = 1984 := by
  unfold round5Mix0ZeroMem
  exact round5Mix0Mem3_size (round4DoneZeroMem_size hlen)

theorem round5Mix0OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix0OneMem I).size = 1984 := by
  unfold round5Mix0OneMem
  exact round5Mix0Mem3_size (round4DoneOneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the second round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix1ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1739⟩
      [round5M10Arg (round5Mix0ZeroMem I),
        round5M6Arg (round5Mix0ZeroMem I),
        ⟨1923⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix0ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 25571 := by
  have hprefix := validPositiveRound5Mix0DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix1ArgsFromRound5Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix0ZeroMem I)
    (startGas := 25478)
    (round5Mix0ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the second round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix1ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1739⟩
      [round5M10Arg (round5Mix0OneMem I),
        round5M6Arg (round5Mix0OneMem I),
        ⟨1923⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix0OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 25598 := by
  have hprefix := validPositiveRound5Mix0DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix1ArgsFromRound5Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix0OneMem I)
    (startGas := 25505)
    (round5Mix0OneMem_size hlen)
    hprefix

end Blake2f
