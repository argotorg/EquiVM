import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix1

/-!
# BLAKE2F fallback positive-round traces: round-3 third `mixG` argument setup

This module continues the path with at least four rounds from PC `1923`. For round 3, the
bytecode extracts SIGMA indices `4` and `5`, loads message words `m[13]` and `m[12]`, and jumps to
the next shared `mixG` body at PC `1969`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-3 SIGMA index `4` selects bytecode memory offset `1056`, i.e. `m[13]`. -/
theorem sigmaRound3Offset4 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨39⟩)
    ⟨480⟩ = (⟨1056⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `5` selects bytecode memory offset `1024`, i.e. `m[12]`. -/
theorem sigmaRound3Offset5 : UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨35⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1024⟩ : UInt256) := by
  native_decide

abbrev round3M13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1056 32))

abbrev round3M12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1024 32))

abbrev round3M13Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M13Load mem) u64MaskWord

abbrev round3M12Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M12Load mem) u64MaskWord

private theorem round3Mix2ArgsMloadM13 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨39⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨39⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨39⟩) ⟨480⟩).toNat 32))) =
      round3M13Load mem := by
  rw [sigmaRound3Offset4]
  unfold round3M13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1056⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix2ArgsMloadM12 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨35⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨35⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M12Load mem := by
  rw [sigmaRound3Offset5]
  unfold round3M12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix2ArgsFromRound3Mix1Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1923⟩
        [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round3M12Arg mem, round3M13Arg mem, ⟨2153⟩, sigmaRound3Word,
        ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1923⟩ := hprefix
  have hmloadM13 := round3Mix2ArgsMloadM13 hmem
  have hmloadM12 := round3Mix2ArgsMloadM12 hmem
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
    raw mload 0 (round3M13Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM13
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨35⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M13Arg, round3M12Arg] using rd1969⟩

def round3Mix1ZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix1Mem3 (round3Mix0ZeroMem I)

def round3Mix1OneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix1Mem3 (round3Mix0OneMem I)

theorem round3Mix1ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix1ZeroMem I).size = 1984 := by
  unfold round3Mix1ZeroMem
  exact round3Mix1Mem3_size (round3Mix0ZeroMem_size hlen)

theorem round3Mix1OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix1OneMem I).size = 1984 := by
  unfold round3Mix1OneMem
  exact round3Mix1Mem3_size (round3Mix0OneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the third round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix2ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round3M12Arg (round3Mix1ZeroMem I),
        round3M13Arg (round3Mix1ZeroMem I),
        ⟨2153⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix1ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 18985 := by
  have hprefix := validPositiveRound3Mix1DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix2ArgsFromRound3Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix1ZeroMem I)
    (startGas := 18892)
    (round3Mix1ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the third round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix2ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1969⟩
      [round3M12Arg (round3Mix1OneMem I),
        round3M13Arg (round3Mix1OneMem I),
        ⟨2153⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix1OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 19012 := by
  have hprefix := validPositiveRound3Mix1DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix2ArgsFromRound3Mix1Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix1OneMem I)
    (startGas := 18919)
    (round3Mix1OneMem_size hlen)
    hprefix

end Blake2f
