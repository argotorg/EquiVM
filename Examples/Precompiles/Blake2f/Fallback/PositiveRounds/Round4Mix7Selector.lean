import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round4Mix6

/-!
# BLAKE2F fallback positive-round traces: round-4 fourth diagonal `mixG` argument setup

This module continues the path with at least five rounds from PC `3070`. For round 4, the
bytecode extracts SIGMA indices `14` and `15`, loads message words `m[3]` and `m[13]`, and jumps
to the last diagonal shared `mixG` body at PC `3109`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-4 SIGMA index `14` selects bytecode memory offset `736`, i.e. `m[3]`. -/
theorem sigmaRound4Offset14 : ⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨1⟩)
    ⟨480⟩ = (⟨736⟩ : UInt256) := by
  native_decide

/-- Round-4 SIGMA index `15` selects bytecode memory offset `1056`, i.e. `m[13]`. -/
theorem sigmaRound4Offset15 : UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨5⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1056⟩ : UInt256) := by
  native_decide

abbrev round4M3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 736 32))

abbrev round4M13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1056 32))

abbrev round4M3Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M3Load mem) u64MaskWord

abbrev round4M13Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M13Load mem) u64MaskWord

private theorem round4Mix7ArgsMloadM3 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨1⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨1⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨1⟩) ⟨480⟩).toNat 32))) =
      round4M3Load mem := by
  rw [sigmaRound4Offset14]
  unfold round4M3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨736⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix7ArgsMloadM13 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨5⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftLeft sigmaRound4Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round4M13Load mem := by
  rw [sigmaRound4Offset15]
  unfold round4M13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1056⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix7ArgsFromRound4Mix6Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3070⟩
        [sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round4M13Arg mem, round4M3Arg mem, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 84) := by
  obtain ⟨k0, rd3070⟩ := hprefix
  have hmloadM3 := round4Mix7ArgsMloadM3 hmem
  have hmloadM13 := round4Mix7ArgsMloadM13 hmem
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
    raw mload 0 (round4M3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM3
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨5⟩,
    shl,
    and,
    add,
    raw mload 0 (round4M13Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM13
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound4Word, u64MaskWord, round4M3Arg, round4M13Arg] using rd3109⟩

def round4Mix6ZeroMem (I : ExecutionEnv) : ByteArray :=
  round4Mix6Mem3 (round4Mix5ZeroMem I)

def round4Mix6OneMem (I : ExecutionEnv) : ByteArray :=
  round4Mix6Mem3 (round4Mix5OneMem I)

theorem round4Mix6ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix6ZeroMem I).size = 1984 := by
  unfold round4Mix6ZeroMem
  exact round4Mix6Mem3_size (round4Mix5ZeroMem_size hlen)

theorem round4Mix6OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix6OneMem I).size = 1984 := by
  unfold round4Mix6OneMem
  exact round4Mix6Mem3_size (round4Mix5OneMem_size hlen)

/-- Final-flag-`0`, at least five rounds: the fourth diagonal round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix7ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨3109⟩
      [round4M13Arg (round4Mix6ZeroMem I),
        round4M3Arg (round4Mix6ZeroMem I),
        ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix6ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 24529 := by
  have hprefix := validPositiveRound4Mix6DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix7ArgsFromRound4Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix6ZeroMem I)
    (startGas := 24445)
    (round4Mix6ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least five rounds: the fourth diagonal round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix7ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨3109⟩
      [round4M13Arg (round4Mix6OneMem I),
        round4M3Arg (round4Mix6OneMem I),
        ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix6OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 24556 := by
  have hprefix := validPositiveRound4Mix6DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix7ArgsFromRound4Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix6OneMem I)
    (startGas := 24472)
    (round4Mix6OneMem_size hlen)
    hprefix

end Blake2f
