import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix6

/-!
# BLAKE2F fallback positive-round traces: round-1 fourth diagonal `mixG` argument setup

This module continues the multi-round path from PC `3070`.  For round 1, the bytecode extracts
SIGMA indices `14` and `15`, loads message words `m[5]` and `m[3]`, and jumps to the last
diagonal shared `mixG` body at PC `3109`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-1 SIGMA index `14` selects bytecode memory offset `800`, i.e. `m[5]`. -/
theorem sigmaRound1Offset14 : ⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨1⟩)
    ⟨480⟩ = (⟨800⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `15` selects bytecode memory offset `736`, i.e. `m[3]`. -/
theorem sigmaRound1Offset15 : UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨5⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨736⟩ : UInt256) := by
  native_decide

abbrev round1M5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 800 32))

abbrev round1M3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 736 32))

abbrev round1M5Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M5Load mem) u64MaskWord

abbrev round1M3Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M3Load mem) u64MaskWord

private theorem round1Mix7ArgsMloadM5 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨1⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨1⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨1⟩) ⟨480⟩).toNat 32))) =
      round1M5Load mem := by
  rw [sigmaRound1Offset14]
  unfold round1M5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix7ArgsMloadM3 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨5⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftLeft sigmaRound1Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round1M3Load mem := by
  rw [sigmaRound1Offset15]
  unfold round1M3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨736⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix7ArgsFromRound1Mix6Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3070⟩
        [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round1M3Arg mem, round1M5Arg mem, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 84) := by
  obtain ⟨k0, rd3070⟩ := hprefix
  have hmloadM5 := round1Mix7ArgsMloadM5 hmem
  have hmloadM3 := round1Mix7ArgsMloadM3 hmem
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
    raw mload 0 (round1M5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM5
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨5⟩,
    shl,
    and,
    add,
    raw mload 0 (round1M3Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, round1M5Arg, round1M3Arg] using rd3109⟩

def round1Mix6ZeroMem (I : ExecutionEnv) : ByteArray :=
  round1Mix6Mem3 (round1Mix5ZeroMem I)

def round1Mix6OneMem (I : ExecutionEnv) : ByteArray :=
  round1Mix6Mem3 (round1Mix5OneMem I)

theorem round1Mix6ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1Mix6ZeroMem I).size = 1984 := by
  unfold round1Mix6ZeroMem
  exact round1Mix6Mem3_size (round1Mix5ZeroMem_size hlen)

theorem round1Mix6OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1Mix6OneMem I).size = 1984 := by
  unfold round1Mix6OneMem
  exact round1Mix6Mem3_size (round1Mix5OneMem_size hlen)

/-- Final-flag-`0`, at least two rounds: the fourth diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix7ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round1M3Arg (round1Mix6ZeroMem I),
        round1M5Arg (round1Mix6ZeroMem I),
        ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix6ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (((((13216 + 93) + 321) + 93) + 321) + 84) := by
  have hprefix := validPositiveRound1Mix6DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix7ArgsFromRound1Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix6ZeroMem I)
    (startGas := (((13216 + 93) + 321) + 93) + 321)
    (round1Mix6ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least two rounds: the fourth diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix7ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round1M3Arg (round1Mix6OneMem I),
        round1M5Arg (round1Mix6OneMem I),
        ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix6OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (((((13243 + 93) + 321) + 93) + 321) + 84) := by
  have hprefix := validPositiveRound1Mix6DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix7ArgsFromRound1Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix6OneMem I)
    (startGas := (((13243 + 93) + 321) + 93) + 321)
    (round1Mix6OneMem_size hlen)
    hprefix

end Blake2f
