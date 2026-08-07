import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix5

/-!
# BLAKE2F fallback positive-round traces: round-3 third diagonal `mixG` argument setup

This module continues the path with at least four rounds from PC `2840`. For round 3, the
bytecode extracts SIGMA indices `12` and `13`, loads message words `m[4]` and `m[0]`, and jumps to
the third diagonal shared `mixG` body at PC `2886`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-3 SIGMA index `12` selects bytecode memory offset `768`, i.e. `m[4]`. -/
theorem sigmaRound3Offset12 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨7⟩)
    ⟨480⟩ = (⟨768⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `13` selects bytecode memory offset `640`, i.e. `m[0]`. -/
theorem sigmaRound3Offset13 : UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨3⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨640⟩ : UInt256) := by
  native_decide

abbrev round3M4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 768 32))

abbrev round3M0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 640 32))

abbrev round3M4Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M4Load mem) u64MaskWord

abbrev round3M0Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M0Load mem) u64MaskWord

private theorem round3Mix6ArgsMloadM4 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨7⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨7⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨7⟩) ⟨480⟩).toNat 32))) =
      round3M4Load mem := by
  rw [sigmaRound3Offset12]
  unfold round3M4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨768⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix6ArgsMloadM0 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨3⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨3⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M0Load mem := by
  rw [sigmaRound3Offset13]
  unfold round3M0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix6ArgsFromRound3Mix5Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2840⟩
        [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round3M0Arg mem, round3M4Arg mem, ⟨3070⟩, sigmaRound3Word,
        ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2840⟩ := hprefix
  have hmloadM4 := round3Mix6ArgsMloadM4 hmem
  have hmloadM0 := round3Mix6ArgsMloadM0 hmem
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
    raw mload 0 (round3M4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM4
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨3⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M4Arg, round3M0Arg] using rd2886⟩

def round3Mix5ZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix5Mem3 (round3Mix4ZeroMem I)

def round3Mix5OneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix5Mem3 (round3Mix4OneMem I)

theorem round3Mix5ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix5ZeroMem I).size = 1984 := by
  unfold round3Mix5ZeroMem
  exact round3Mix5Mem3_size (round3Mix4ZeroMem_size hlen)

theorem round3Mix5OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix5OneMem I).size = 1984 := by
  unfold round3Mix5OneMem
  exact round3Mix5Mem3_size (round3Mix4OneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the third diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix6ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round3M0Arg (round3Mix5ZeroMem I),
        round3M4Arg (round3Mix5ZeroMem I),
        ⟨3070⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix5ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 20635 := by
  have hprefix := validPositiveRound3Mix5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix6ArgsFromRound3Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix5ZeroMem I)
    (startGas := 20542)
    (round3Mix5ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the third diagonal round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix6ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2886⟩
      [round3M0Arg (round3Mix5OneMem I),
        round3M4Arg (round3Mix5OneMem I),
        ⟨3070⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix5OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 20662 := by
  have hprefix := validPositiveRound3Mix5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix6ArgsFromRound3Mix5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix5OneMem I)
    (startGas := 20569)
    (round3Mix5OneMem_size hlen)
    hprefix

end Blake2f
