import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix2

/-!
# BLAKE2F fallback positive-round traces: round-5 fourth `mixG` argument setup

This module continues the path with at least six rounds from PC `2153`. For round 5, the
bytecode extracts SIGMA indices `6` and `7`, loads message words `m[8]` and `m[3]`, and jumps to
the next shared `mixG` body at PC `2199`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-5 SIGMA index `6` selects bytecode memory offset `896`, i.e. `m[8]`. -/
theorem sigmaRound5Offset6 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨31⟩)
    ⟨480⟩ = (⟨896⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `7` selects bytecode memory offset `736`, i.e. `m[3]`. -/
theorem sigmaRound5Offset7 : UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨27⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨736⟩ : UInt256) := by
  native_decide

abbrev round5M8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 896 32))

abbrev round5M3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 736 32))

abbrev round5M8Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M8Load mem) u64MaskWord

abbrev round5M3Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M3Load mem) u64MaskWord

private theorem round5Mix3ArgsMloadM8 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨31⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨31⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨31⟩) ⟨480⟩).toNat 32))) =
      round5M8Load mem := by
  rw [sigmaRound5Offset6]
  unfold round5M8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨896⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix3ArgsMloadM3 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨27⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M3Load mem := by
  rw [sigmaRound5Offset7]
  unfold round5M3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨736⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix3ArgsFromRound5Mix2Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2153⟩
        [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round5M3Arg mem, round5M8Arg mem, ⟨2383⟩, sigmaRound5Word,
        ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2153⟩ := hprefix
  have hmloadM8 := round5Mix3ArgsMloadM8 hmem
  have hmloadM3 := round5Mix3ArgsMloadM3 hmem
  have rd2199 := evm_run rd2153 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2383⟩,
    push2 ⟨2199⟩,
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
    push1 ⟨31⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round5M8Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM8
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨27⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M3Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M8Arg, round5M3Arg] using rd2199⟩

def round5Mix2ZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix2Mem3 (round5Mix1ZeroMem I)

def round5Mix2OneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix2Mem3 (round5Mix1OneMem I)

theorem round5Mix2ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix2ZeroMem I).size = 1984 := by
  unfold round5Mix2ZeroMem
  exact round5Mix2Mem3_size (round5Mix1ZeroMem_size hlen)

theorem round5Mix2OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix2OneMem I).size = 1984 := by
  unfold round5Mix2OneMem
  exact round5Mix2Mem3_size (round5Mix1OneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the fourth round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix3ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2199⟩
      [round5M3Arg (round5Mix2ZeroMem I),
        round5M8Arg (round5Mix2ZeroMem I),
        ⟨2383⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix2ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 26399 := by
  have hprefix := validPositiveRound5Mix2DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix3ArgsFromRound5Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix2ZeroMem I)
    (startGas := 26306)
    (round5Mix2ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the fourth round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix3ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2199⟩
      [round5M3Arg (round5Mix2OneMem I),
        round5M8Arg (round5Mix2OneMem I),
        ⟨2383⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix2OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 26426 := by
  have hprefix := validPositiveRound5Mix2DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix3ArgsFromRound5Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix2OneMem I)
    (startGas := 26333)
    (round5Mix2OneMem_size hlen)
    hprefix

end Blake2f
