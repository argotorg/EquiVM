import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round2Mix6

/-!
# BLAKE2F fallback positive-round traces: round-2 fourth diagonal `mixG` argument setup

This module continues the path with at least three rounds from PC `3070`. For round 2, the
bytecode extracts SIGMA indices `14` and `15`, loads message words `m[9]` and `m[4]`, and jumps to
the last diagonal shared `mixG` body at PC `3109`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-2 SIGMA index `14` selects bytecode memory offset `928`, i.e. `m[9]`. -/
theorem sigmaRound2Offset14 : ⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨1⟩)
    ⟨480⟩ = (⟨928⟩ : UInt256) := by
  native_decide

/-- Round-2 SIGMA index `15` selects bytecode memory offset `768`, i.e. `m[4]`. -/
theorem sigmaRound2Offset15 : UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨5⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨768⟩ : UInt256) := by
  native_decide

abbrev round2M9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 928 32))

abbrev round2M4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 768 32))

abbrev round2M9Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M9Load mem) u64MaskWord

abbrev round2M4Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M4Load mem) u64MaskWord

private theorem round2Mix7ArgsMloadM9 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨1⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨1⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨1⟩) ⟨480⟩).toNat 32))) =
      round2M9Load mem := by
  rw [sigmaRound2Offset14]
  unfold round2M9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix7ArgsMloadM4 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨5⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftLeft sigmaRound2Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round2M4Load mem := by
  rw [sigmaRound2Offset15]
  unfold round2M4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨768⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix7ArgsFromRound2Mix6Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3070⟩
        [sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round2M4Arg mem, round2M9Arg mem, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 84) := by
  obtain ⟨k0, rd3070⟩ := hprefix
  have hmloadM9 := round2Mix7ArgsMloadM9 hmem
  have hmloadM4 := round2Mix7ArgsMloadM4 hmem
  have rd3109 := evm_run rd3070 with [
    raw jumpdest (by decide) (by evm_ov),
    dup6,
    push8 ⟨18446744073709551615⟩,
    swap1,
    swap3,
    swap2,
    swap3,
    push2 ⟨480⟩,
    dup3,
    dup2,
    dup7,
    push1 ⟨1⟩,
    shl,
    and,
    dup4,
    add,
    raw mload 0 (round2M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨5⟩,
    shl,
    and,
    add,
    raw mload 0 (round2M4Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound2Word, u64MaskWord, round2M9Arg, round2M4Arg] using rd3109⟩

def round2Mix6ZeroMem (I : ExecutionEnv) : ByteArray :=
  round2Mix6Mem3 (round2Mix5ZeroMem I)

def round2Mix6OneMem (I : ExecutionEnv) : ByteArray :=
  round2Mix6Mem3 (round2Mix5OneMem I)

theorem round2Mix6ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix6ZeroMem I).size = 1984 := by
  unfold round2Mix6ZeroMem
  exact round2Mix6Mem3_size (round2Mix5ZeroMem_size hlen)

theorem round2Mix6OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2Mix6OneMem I).size = 1984 := by
  unfold round2Mix6OneMem
  exact round2Mix6Mem3_size (round2Mix5OneMem_size hlen)

/-- Final-flag-`0`, at least three rounds: the fourth diagonal round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix7ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round2M4Arg (round2Mix6ZeroMem I),
        round2M9Arg (round2Mix6ZeroMem I),
        ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix6ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17573 := by
  have hprefix := validPositiveRound2Mix6DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix7ArgsFromRound2Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix6ZeroMem I)
    (startGas := 17489)
    (round2Mix6ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least three rounds: the fourth diagonal round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix7ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round2M4Arg (round2Mix6OneMem I),
        round2M9Arg (round2Mix6OneMem I),
        ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix6OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17600 := by
  have hprefix := validPositiveRound2Mix6DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix7ArgsFromRound2Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix6OneMem I)
    (startGas := 17516)
    (round2Mix6OneMem_size hlen)
    hprefix

end Blake2f
