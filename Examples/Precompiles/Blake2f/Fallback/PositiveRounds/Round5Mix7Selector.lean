import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix6

/-!
# BLAKE2F fallback positive-round traces: round-5 fourth diagonal `mixG` argument setup

This module continues the path with at least six rounds from PC `3070`. For round 5, the
bytecode extracts SIGMA indices `14` and `15`, loads message words `m[1]` and `m[9]`, and jumps
to the last diagonal shared `mixG` body at PC `3109`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-5 SIGMA index `14` selects bytecode memory offset `672`, i.e. `m[1]`. -/
theorem sigmaRound5Offset14 : ⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨1⟩)
    ⟨480⟩ = (⟨672⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `15` selects bytecode memory offset `928`, i.e. `m[9]`. -/
theorem sigmaRound5Offset15 : UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨5⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨928⟩ : UInt256) := by
  native_decide

abbrev round5M1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 672 32))

abbrev round5M9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 928 32))

abbrev round5M1Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M1Load mem) u64MaskWord

abbrev round5M9Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M9Load mem) u64MaskWord

private theorem round5Mix7ArgsMloadM1 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨1⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨1⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨1⟩) ⟨480⟩).toNat 32))) =
      round5M1Load mem := by
  rw [sigmaRound5Offset14]
  unfold round5M1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix7ArgsMloadM9 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨5⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftLeft sigmaRound5Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M9Load mem := by
  rw [sigmaRound5Offset15]
  unfold round5M9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix7ArgsFromRound5Mix6Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3070⟩
        [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round5M9Arg mem, round5M1Arg mem, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 84) := by
  obtain ⟨k0, rd3070⟩ := hprefix
  have hmloadM1 := round5Mix7ArgsMloadM1 hmem
  have hmloadM9 := round5Mix7ArgsMloadM9 hmem
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
    raw mload 0 (round5M1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM1
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨5⟩,
    shl,
    and,
    add,
    raw mload 0 (round5M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M1Arg, round5M9Arg] using rd3109⟩

def round5Mix6ZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix6Mem3 (round5Mix5ZeroMem I)

def round5Mix6OneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix6Mem3 (round5Mix5OneMem I)

theorem round5Mix6ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix6ZeroMem I).size = 1984 := by
  unfold round5Mix6ZeroMem
  exact round5Mix6Mem3_size (round5Mix5ZeroMem_size hlen)

theorem round5Mix6OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix6OneMem I).size = 1984 := by
  unfold round5Mix6OneMem
  exact round5Mix6Mem3_size (round5Mix5OneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the fourth diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix7ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨3109⟩
      [round5M9Arg (round5Mix6ZeroMem I),
        round5M1Arg (round5Mix6ZeroMem I),
        ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix6ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28040 := by
  have hprefix := validPositiveRound5Mix6DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix7ArgsFromRound5Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix6ZeroMem I)
    (startGas := 27956)
    (round5Mix6ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the fourth diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix7ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨3109⟩
      [round5M9Arg (round5Mix6OneMem I),
        round5M1Arg (round5Mix6OneMem I),
        ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix6OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28067 := by
  have hprefix := validPositiveRound5Mix6DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix7ArgsFromRound5Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix6OneMem I)
    (startGas := 27983)
    (round5Mix6OneMem_size hlen)
    hprefix

end Blake2f
