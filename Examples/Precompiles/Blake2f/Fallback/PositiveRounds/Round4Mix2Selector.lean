import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round4Mix1

/-!
# BLAKE2F fallback positive-round traces: round-4 third `mixG` argument setup

This module continues the path with at least five rounds from PC `1923`. For round 4, the
bytecode extracts SIGMA indices `4` and `5`, loads message words `m[2]` and `m[4]`, and jumps to
the next shared `mixG` body at PC `1969`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-4 SIGMA index `4` selects bytecode memory offset `704`, i.e. `m[2]`. -/
theorem sigmaRound4Offset4 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨39⟩)
    ⟨480⟩ = (⟨704⟩ : UInt256) := by
  native_decide

/-- Round-4 SIGMA index `5` selects bytecode memory offset `768`, i.e. `m[4]`. -/
theorem sigmaRound4Offset5 : UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨35⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨768⟩ : UInt256) := by
  native_decide

abbrev round4M2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

abbrev round4M4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 768 32))

abbrev round4M2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M2Load mem) u64MaskWord

abbrev round4M4Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M4Load mem) u64MaskWord

private theorem round4Mix2ArgsMloadM2 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨39⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨39⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨39⟩) ⟨480⟩).toNat 32))) =
      round4M2Load mem := by
  rw [sigmaRound4Offset4]
  unfold round4M2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix2ArgsMloadM4 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨35⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round4M4Load mem := by
  rw [sigmaRound4Offset5]
  unfold round4M4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨768⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix2ArgsFromRound4Mix1Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1923⟩
        [sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round4M4Arg mem, round4M2Arg mem, ⟨2153⟩, sigmaRound4Word,
        ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1923⟩ := hprefix
  have hmloadM2 := round4Mix2ArgsMloadM2 hmem
  have hmloadM4 := round4Mix2ArgsMloadM4 hmem
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
    raw mload 0 (round4M2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM2
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨35⟩,
    shr,
    and,
    add,
    raw mload 0 (round4M4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM4
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound4Word, u64MaskWord, round4M2Arg, round4M4Arg] using rd1969⟩

def round4Mix1ZeroMem (I : ExecutionEnv) : ByteArray :=
  round4Mix1Mem3 (round4Mix0ZeroMem I)

def round4Mix1OneMem (I : ExecutionEnv) : ByteArray :=
  round4Mix1Mem3 (round4Mix0OneMem I)

theorem round4Mix1ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix1ZeroMem I).size = 1984 := by
  unfold round4Mix1ZeroMem
  exact round4Mix1Mem3_size (round4Mix0ZeroMem_size hlen)

theorem round4Mix1OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix1OneMem I).size = 1984 := by
  unfold round4Mix1OneMem
  exact round4Mix1Mem3_size (round4Mix0OneMem_size hlen)

/-- Final-flag-`0`, at least five rounds: the third round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix2ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1969⟩
      [round4M4Arg (round4Mix1ZeroMem I),
        round4M2Arg (round4Mix1ZeroMem I),
        ⟨2153⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix1ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 22474 := by
  have hprefix := validPositiveRound4Mix1DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix2ArgsFromRound4Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix1ZeroMem I)
    (startGas := 22381)
    (round4Mix1ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least five rounds: the third round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix2ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1969⟩
      [round4M4Arg (round4Mix1OneMem I),
        round4M2Arg (round4Mix1OneMem I),
        ⟨2153⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix1OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 22501 := by
  have hprefix := validPositiveRound4Mix1DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix2ArgsFromRound4Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix1OneMem I)
    (startGas := 22408)
    (round4Mix1OneMem_size hlen)
    hprefix

end Blake2f
