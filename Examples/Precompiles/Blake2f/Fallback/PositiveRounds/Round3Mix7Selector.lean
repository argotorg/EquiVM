import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix6

/-!
# BLAKE2F fallback positive-round traces: round-3 fourth diagonal `mixG` argument setup

This module continues the path with at least four rounds from PC `3070`. For round 3, the
bytecode extracts SIGMA indices `14` and `15`, loads message words `m[15]` and `m[8]`, and jumps
to the last diagonal shared `mixG` body at PC `3109`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-3 SIGMA index `14` selects bytecode memory offset `1120`, i.e. `m[15]`. -/
theorem sigmaRound3Offset14 : ⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨1⟩)
    ⟨480⟩ = (⟨1120⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `15` selects bytecode memory offset `896`, i.e. `m[8]`. -/
theorem sigmaRound3Offset15 : UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨5⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨896⟩ : UInt256) := by
  native_decide

abbrev round3M15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1120 32))

abbrev round3M8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 896 32))

abbrev round3M15Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M15Load mem) u64MaskWord

abbrev round3M8Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M8Load mem) u64MaskWord

private theorem round3Mix7ArgsMloadM15 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨1⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨1⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨1⟩) ⟨480⟩).toNat 32))) =
      round3M15Load mem := by
  rw [sigmaRound3Offset14]
  unfold round3M15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1120⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix7ArgsMloadM8 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨5⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftLeft sigmaRound3Word ⟨5⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M8Load mem := by
  rw [sigmaRound3Offset15]
  unfold round3M8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨896⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix7ArgsFromRound3Mix6Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3070⟩
        [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round3M8Arg mem, round3M15Arg mem, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 84) := by
  obtain ⟨k0, rd3070⟩ := hprefix
  have hmloadM15 := round3Mix7ArgsMloadM15 hmem
  have hmloadM8 := round3Mix7ArgsMloadM8 hmem
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
    raw mload 0 (round3M15Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM15
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨5⟩,
    shl,
    and,
    add,
    raw mload 0 (round3M8Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM8
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M15Arg, round3M8Arg] using rd3109⟩

def round3Mix6ZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix6Mem3 (round3Mix5ZeroMem I)

def round3Mix6OneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix6Mem3 (round3Mix5OneMem I)

theorem round3Mix6ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix6ZeroMem I).size = 1984 := by
  unfold round3Mix6ZeroMem
  exact round3Mix6Mem3_size (round3Mix5ZeroMem_size hlen)

theorem round3Mix6OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix6OneMem I).size = 1984 := by
  unfold round3Mix6OneMem
  exact round3Mix6Mem3_size (round3Mix5OneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the fourth diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix7ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round3M8Arg (round3Mix6ZeroMem I),
        round3M15Arg (round3Mix6ZeroMem I),
        ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix6ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 21040 := by
  have hprefix := validPositiveRound3Mix6DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix7ArgsFromRound3Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix6ZeroMem I)
    (startGas := 20956)
    (round3Mix6ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the fourth diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix7ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3109⟩
      [round3M8Arg (round3Mix6OneMem I),
        round3M15Arg (round3Mix6OneMem I),
        ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix6OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 21067 := by
  have hprefix := validPositiveRound3Mix6DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix7ArgsFromRound3Mix6Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix6OneMem I)
    (startGas := 20983)
    (round3Mix6OneMem_size hlen)
    hprefix

end Blake2f
