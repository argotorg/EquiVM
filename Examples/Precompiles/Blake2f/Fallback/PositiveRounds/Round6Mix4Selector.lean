import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round6Mix3

/-!
# BLAKE2F fallback positive-round traces: round-6 first diagonal `mixG` argument setup

This module continues the path with at least seven rounds from PC `2383`. For round 6, the
bytecode extracts SIGMA indices `8` and `9`, loads message words `m[0]` and `m[7]`, and jumps to
the first diagonal shared `mixG` body at PC `2429`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-6 SIGMA index `8` selects bytecode memory offset `640`, i.e. `m[0]`. -/
theorem sigmaRound6Offset8 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨23⟩)
    ⟨480⟩ = (⟨640⟩ : UInt256) := by
  native_decide

/-- Round-6 SIGMA index `9` selects bytecode memory offset `864`, i.e. `m[7]`. -/
theorem sigmaRound6Offset9 : UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨19⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨864⟩ : UInt256) := by
  native_decide

abbrev round6M0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 640 32))

abbrev round6M7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 864 32))

abbrev round6M0Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M0Load mem) u64MaskWord

abbrev round6M7Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M7Load mem) u64MaskWord

private theorem round6Mix4ArgsMloadM0 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨23⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨23⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨23⟩) ⟨480⟩).toNat 32))) =
      round6M0Load mem := by
  rw [sigmaRound6Offset8]
  unfold round6M0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix4ArgsMloadM7 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨19⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round6M7Load mem := by
  rw [sigmaRound6Offset9]
  unfold round6M7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix4ArgsFromRound6Mix3Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2383⟩
        [sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round6M7Arg mem, round6M0Arg mem, ⟨2610⟩, sigmaRound6Word,
        ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2383⟩ := hprefix
  have hmloadM0 := round6Mix4ArgsMloadM0 hmem
  have hmloadM7 := round6Mix4ArgsMloadM7 hmem
  have rd2429 := evm_run rd2383 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2610⟩,
    push2 ⟨2429⟩,
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
    push1 ⟨23⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round6M0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨19⟩,
    shr,
    and,
    add,
    raw mload 0 (round6M7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM7
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound6Word, u64MaskWord, round6M0Arg, round6M7Arg] using rd2429⟩

def round6Mix3ZeroMem (I : ExecutionEnv) : ByteArray :=
  round6Mix3Mem3 (round6Mix2ZeroMem I)

def round6Mix3OneMem (I : ExecutionEnv) : ByteArray :=
  round6Mix3Mem3 (round6Mix2OneMem I)

theorem round6Mix3ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round6Mix3ZeroMem I).size = 1984 := by
  unfold round6Mix3ZeroMem
  exact round6Mix3Mem3_size (round6Mix2ZeroMem_size hlen)

theorem round6Mix3OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round6Mix3OneMem I).size = 1984 := by
  unfold round6Mix3OneMem
  exact round6Mix3Mem3_size (round6Mix2OneMem_size hlen)

/-- Final-flag-`0`, at least seven rounds: the first diagonal round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix4ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round6M7Arg (round6Mix3ZeroMem I),
        round6M0Arg (round6Mix3ZeroMem I),
        ⟨2610⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix3ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 30346 := by
  have hprefix := validPositiveRound6Mix3DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix4ArgsFromRound6Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round6Mix3ZeroMem I)
    (startGas := 30253)
    (round6Mix3ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least seven rounds: the first diagonal round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix4ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round6M7Arg (round6Mix3OneMem I),
        round6M0Arg (round6Mix3OneMem I),
        ⟨2610⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix3OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 30373 := by
  have hprefix := validPositiveRound6Mix3DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix4ArgsFromRound6Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round6Mix3OneMem I)
    (startGas := 30280)
    (round6Mix3OneMem_size hlen)
    hprefix

end Blake2f
