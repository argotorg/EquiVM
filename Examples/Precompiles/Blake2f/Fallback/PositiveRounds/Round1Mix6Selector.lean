import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix5

/-!
# BLAKE2F fallback positive-round traces: round-1 third diagonal `mixG` argument setup

This module continues the multi-round path from PC `2840`.  For round 1, the bytecode extracts
SIGMA indices `12` and `13`, loads message words `m[11]` and `m[7]`, and jumps to the third
diagonal shared `mixG` body at PC `2886`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-1 SIGMA index `12` selects bytecode memory offset `992`, i.e. `m[11]`. -/
theorem sigmaRound1Offset12 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨7⟩)
    ⟨480⟩ = (⟨992⟩ : UInt256) := by
  native_decide

/-- Round-1 SIGMA index `13` selects bytecode memory offset `864`, i.e. `m[7]`. -/
theorem sigmaRound1Offset13 : UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨3⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨864⟩ : UInt256) := by
  native_decide

abbrev round1M11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 992 32))

abbrev round1M7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 864 32))

abbrev round1M11Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M11Load mem) u64MaskWord

abbrev round1M7Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round1M7Load mem) u64MaskWord

private theorem round1Mix6ArgsMloadM11 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨7⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨7⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨7⟩) ⟨480⟩).toNat 32))) =
      round1M11Load mem := by
  rw [sigmaRound1Offset12]
  unfold round1M11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix6ArgsMloadM7 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨3⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound1Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round1M7Load mem := by
  rw [sigmaRound1Offset13]
  unfold round1M7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix6ArgsFromRound1Mix5Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2840⟩
        [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round1M7Arg mem, round1M11Arg mem, ⟨3070⟩, sigmaRound1Word,
        ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2840⟩ := hprefix
  have hmloadM11 := round1Mix6ArgsMloadM11 hmem
  have hmloadM7 := round1Mix6ArgsMloadM7 hmem
  have rd2886 := evm_run rd2840 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨3070⟩,
    push2 ⟨2886⟩,
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
    push1 ⟨7⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round1M11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM11
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨3⟩,
    shr,
    and,
    add,
    raw mload 0 (round1M7Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound1Word, u64MaskWord, round1M11Arg, round1M7Arg] using rd2886⟩

def round1Mix5ZeroMem (I : ExecutionEnv) : ByteArray :=
  round1Mix5Mem3 (round1Mix4ZeroMem I)

def round1Mix5OneMem (I : ExecutionEnv) : ByteArray :=
  round1Mix5Mem3 (round1Mix4OneMem I)

theorem round1Mix5ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1Mix5ZeroMem I).size = 1984 := by
  unfold round1Mix5ZeroMem
  exact round1Mix5Mem3_size (round1Mix4ZeroMem_size hlen)

theorem round1Mix5OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1Mix5OneMem I).size = 1984 := by
  unfold round1Mix5OneMem
  exact round1Mix5Mem3_size (round1Mix4OneMem_size hlen)

/-- Final-flag-`0`, at least two rounds: the third diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix6ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round1M7Arg (round1Mix5ZeroMem I),
        round1M11Arg (round1Mix5ZeroMem I),
        ⟨3070⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix5ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (((13216 + 93) + 321) + 93) := by
  have hprefix := validPositiveRound1Mix5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix6ArgsFromRound1Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix5ZeroMem I)
    (startGas := (13216 + 93) + 321)
    (round1Mix5ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least two rounds: the third diagonal round-1 `mixG` call is prepared. -/
theorem validPositiveRound1Mix6ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round1M7Arg (round1Mix5OneMem I),
        round1M11Arg (round1Mix5OneMem I),
        ⟨3070⟩, sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix5OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (((13243 + 93) + 321) + 93) := by
  have hprefix := validPositiveRound1Mix5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix6ArgsFromRound1Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix5OneMem I)
    (startGas := (13243 + 93) + 321)
    (round1Mix5OneMem_size hlen)
    hprefix

end Blake2f
