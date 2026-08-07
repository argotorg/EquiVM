import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix3

/-!
# BLAKE2F fallback positive-round traces: round-3 first diagonal `mixG` argument setup

This module continues the path with at least four rounds from PC `2383`. For round 3, the
bytecode extracts SIGMA indices `8` and `9`, loads message words `m[2]` and `m[6]`, and jumps to
the first diagonal shared `mixG` body at PC `2429`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-3 SIGMA index `8` selects bytecode memory offset `704`, i.e. `m[2]`. -/
theorem sigmaRound3Offset8 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨23⟩)
    ⟨480⟩ = (⟨704⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `9` selects bytecode memory offset `832`, i.e. `m[6]`. -/
theorem sigmaRound3Offset9 : UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨19⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨832⟩ : UInt256) := by
  native_decide

abbrev round3M2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

abbrev round3M6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 832 32))

abbrev round3M2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M2Load mem) u64MaskWord

abbrev round3M6Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M6Load mem) u64MaskWord

private theorem round3Mix4ArgsMloadM2 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨23⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨23⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨23⟩) ⟨480⟩).toNat 32))) =
      round3M2Load mem := by
  rw [sigmaRound3Offset8]
  unfold round3M2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix4ArgsMloadM6 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨19⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M6Load mem := by
  rw [sigmaRound3Offset9]
  unfold round3M6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨832⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix4ArgsFromRound3Mix3Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2383⟩
        [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round3M6Arg mem, round3M2Arg mem, ⟨2610⟩, sigmaRound3Word,
        ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2383⟩ := hprefix
  have hmloadM2 := round3Mix4ArgsMloadM2 hmem
  have hmloadM6 := round3Mix4ArgsMloadM6 hmem
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
    raw mload 0 (round3M2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM2
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨19⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM6
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M2Arg, round3M6Arg] using rd2429⟩

def round3Mix3ZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix3Mem3 (round3Mix2ZeroMem I)

def round3Mix3OneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix3Mem3 (round3Mix2OneMem I)

theorem round3Mix3ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix3ZeroMem I).size = 1984 := by
  unfold round3Mix3ZeroMem
  exact round3Mix3Mem3_size (round3Mix2ZeroMem_size hlen)

theorem round3Mix3OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix3OneMem I).size = 1984 := by
  unfold round3Mix3OneMem
  exact round3Mix3Mem3_size (round3Mix2OneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the first diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix4ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round3M6Arg (round3Mix3ZeroMem I),
        round3M2Arg (round3Mix3ZeroMem I),
        ⟨2610⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix3ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 19813 := by
  have hprefix := validPositiveRound3Mix3DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix4ArgsFromRound3Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix3ZeroMem I)
    (startGas := 19720)
    (round3Mix3ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the first diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix4ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round3M6Arg (round3Mix3OneMem I),
        round3M2Arg (round3Mix3OneMem I),
        ⟨2610⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix3OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 19840 := by
  have hprefix := validPositiveRound3Mix3DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix4ArgsFromRound3Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix3OneMem I)
    (startGas := 19747)
    (round3Mix3OneMem_size hlen)
    hprefix

end Blake2f
