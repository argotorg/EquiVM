import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix0

/-!
# BLAKE2F fallback positive-round traces: round-3 second `mixG` argument setup

This module continues the path with at least four rounds from PC `1693`. For round 3, the
bytecode extracts SIGMA indices `2` and `3`, loads message words `m[3]` and `m[1]`, and jumps to
the next shared `mixG` body at PC `1739`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-3 SIGMA index `2` selects bytecode memory offset `736`, i.e. `m[3]`. -/
theorem sigmaRound3Offset2 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨47⟩)
    ⟨480⟩ = (⟨736⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `3` selects bytecode memory offset `672`, i.e. `m[1]`. -/
theorem sigmaRound3Offset3 : UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨43⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨672⟩ : UInt256) := by
  native_decide

abbrev round3M3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 736 32))

abbrev round3M1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 672 32))

abbrev round3M3Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M3Load mem) u64MaskWord

abbrev round3M1Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M1Load mem) u64MaskWord

private theorem round3Mix1ArgsMloadM3 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨47⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨47⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨47⟩) ⟨480⟩).toNat 32))) =
      round3M3Load mem := by
  rw [sigmaRound3Offset2]
  unfold round3M3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨736⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix1ArgsMloadM1 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨43⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M1Load mem := by
  rw [sigmaRound3Offset3]
  unfold round3M1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix1ArgsFromRound3Mix0Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1693⟩
        [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round3M1Arg mem, round3M3Arg mem, ⟨1923⟩, sigmaRound3Word,
        ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1693⟩ := hprefix
  have hmloadM3 := round3Mix1ArgsMloadM3 hmem
  have hmloadM1 := round3Mix1ArgsMloadM1 hmem
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
    raw mload 0 (round3M3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM3
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨43⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M1Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M3Arg, round3M1Arg] using rd1739⟩

def round3Mix0ZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix0Mem3 (round2DoneZeroMem I)

def round3Mix0OneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix0Mem3 (round2DoneOneMem I)

theorem round3Mix0ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix0ZeroMem I).size = 1984 := by
  unfold round3Mix0ZeroMem
  exact round3Mix0Mem3_size (round2DoneZeroMem_size hlen)

theorem round3Mix0OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix0OneMem I).size = 1984 := by
  unfold round3Mix0OneMem
  exact round3Mix0Mem3_size (round2DoneOneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the second round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix1ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round3M1Arg (round3Mix0ZeroMem I),
        round3M3Arg (round3Mix0ZeroMem I),
        ⟨1923⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix0ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 18571 := by
  have hprefix := validPositiveRound3Mix0DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix1ArgsFromRound3Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix0ZeroMem I)
    (startGas := 18478)
    (round3Mix0ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the second round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix1ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round3M1Arg (round3Mix0OneMem I),
        round3M3Arg (round3Mix0OneMem I),
        ⟨1923⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix0OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 18598 := by
  have hprefix := validPositiveRound3Mix0DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix1ArgsFromRound3Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix0OneMem I)
    (startGas := 18505)
    (round3Mix0OneMem_size hlen)
    hprefix

end Blake2f
