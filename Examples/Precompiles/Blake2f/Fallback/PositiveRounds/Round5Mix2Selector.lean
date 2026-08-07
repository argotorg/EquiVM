import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix1

/-!
# BLAKE2F fallback positive-round traces: round-5 third `mixG` argument setup

This module continues the path with at least six rounds from PC `1923`. For round 5, the
bytecode extracts SIGMA indices `4` and `5`, loads message words `m[0]` and `m[11]`, and jumps to
the next shared `mixG` body at PC `1969`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-5 SIGMA index `4` selects bytecode memory offset `640`, i.e. `m[0]`. -/
theorem sigmaRound5Offset4 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨39⟩)
    ⟨480⟩ = (⟨640⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `5` selects bytecode memory offset `992`, i.e. `m[11]`. -/
theorem sigmaRound5Offset5 : UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨35⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨992⟩ : UInt256) := by
  native_decide

abbrev round5M0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 640 32))

abbrev round5M11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 992 32))

abbrev round5M0Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M0Load mem) u64MaskWord

abbrev round5M11Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M11Load mem) u64MaskWord

private theorem round5Mix2ArgsMloadM0 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨39⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨39⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨39⟩) ⟨480⟩).toNat 32))) =
      round5M0Load mem := by
  rw [sigmaRound5Offset4]
  unfold round5M0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix2ArgsMloadM11 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨35⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M11Load mem := by
  rw [sigmaRound5Offset5]
  unfold round5M11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix2ArgsFromRound5Mix1Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1923⟩
        [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round5M11Arg mem, round5M0Arg mem, ⟨2153⟩, sigmaRound5Word,
        ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1923⟩ := hprefix
  have hmloadM0 := round5Mix2ArgsMloadM0 hmem
  have hmloadM11 := round5Mix2ArgsMloadM11 hmem
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
    raw mload 0 (round5M0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨35⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM11
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M0Arg, round5M11Arg] using rd1969⟩

def round5Mix1ZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix1Mem3 (round5Mix0ZeroMem I)

def round5Mix1OneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix1Mem3 (round5Mix0OneMem I)

theorem round5Mix1ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix1ZeroMem I).size = 1984 := by
  unfold round5Mix1ZeroMem
  exact round5Mix1Mem3_size (round5Mix0ZeroMem_size hlen)

theorem round5Mix1OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix1OneMem I).size = 1984 := by
  unfold round5Mix1OneMem
  exact round5Mix1Mem3_size (round5Mix0OneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the third round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix2ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1969⟩
      [round5M11Arg (round5Mix1ZeroMem I),
        round5M0Arg (round5Mix1ZeroMem I),
        ⟨2153⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix1ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 25985 := by
  have hprefix := validPositiveRound5Mix1DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix2ArgsFromRound5Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix1ZeroMem I)
    (startGas := 25892)
    (round5Mix1ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the third round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix2ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1969⟩
      [round5M11Arg (round5Mix1OneMem I),
        round5M0Arg (round5Mix1OneMem I),
        ⟨2153⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix1OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 26012 := by
  have hprefix := validPositiveRound5Mix1DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix2ArgsFromRound5Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix1OneMem I)
    (startGas := 25919)
    (round5Mix1OneMem_size hlen)
    hprefix

end Blake2f
