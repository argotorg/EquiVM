import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round4Mix2

/-!
# BLAKE2F fallback positive-round traces: round-4 fourth `mixG` argument setup

This module continues the path with at least five rounds from PC `2153`. For round 4, the
bytecode extracts SIGMA indices `6` and `7`, loads message words `m[10]` and `m[15]`, and jumps to
the next shared `mixG` body at PC `2199`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-4 SIGMA index `6` selects bytecode memory offset `960`, i.e. `m[10]`. -/
theorem sigmaRound4Offset6 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨31⟩)
    ⟨480⟩ = (⟨960⟩ : UInt256) := by
  native_decide

/-- Round-4 SIGMA index `7` selects bytecode memory offset `1120`, i.e. `m[15]`. -/
theorem sigmaRound4Offset7 : UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨27⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1120⟩ : UInt256) := by
  native_decide

abbrev round4M10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 960 32))

abbrev round4M15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1120 32))

abbrev round4M10Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M10Load mem) u64MaskWord

abbrev round4M15Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M15Load mem) u64MaskWord

private theorem round4Mix3ArgsMloadM10 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨31⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨31⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨31⟩) ⟨480⟩).toNat 32))) =
      round4M10Load mem := by
  rw [sigmaRound4Offset6]
  unfold round4M10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨960⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix3ArgsMloadM15 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨27⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round4M15Load mem := by
  rw [sigmaRound4Offset7]
  unfold round4M15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1120⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix3ArgsFromRound4Mix2Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2153⟩
        [sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round4M15Arg mem, round4M10Arg mem, ⟨2383⟩, sigmaRound4Word,
        ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2153⟩ := hprefix
  have hmloadM10 := round4Mix3ArgsMloadM10 hmem
  have hmloadM15 := round4Mix3ArgsMloadM15 hmem
  have rd2199 := evm_run rd2153 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2383⟩,
    push2 ⟨2199⟩,
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
    push1 ⟨31⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round4M10Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM10
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨27⟩,
    shr,
    and,
    add,
    raw mload 0 (round4M15Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM15
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound4Word, u64MaskWord, round4M10Arg, round4M15Arg] using rd2199⟩

def round4Mix2ZeroMem (I : ExecutionEnv) : ByteArray :=
  round4Mix2Mem3 (round4Mix1ZeroMem I)

def round4Mix2OneMem (I : ExecutionEnv) : ByteArray :=
  round4Mix2Mem3 (round4Mix1OneMem I)

theorem round4Mix2ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix2ZeroMem I).size = 1984 := by
  unfold round4Mix2ZeroMem
  exact round4Mix2Mem3_size (round4Mix1ZeroMem_size hlen)

theorem round4Mix2OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix2OneMem I).size = 1984 := by
  unfold round4Mix2OneMem
  exact round4Mix2Mem3_size (round4Mix1OneMem_size hlen)

/-- Final-flag-`0`, at least five rounds: the fourth round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix3ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2199⟩
      [round4M15Arg (round4Mix2ZeroMem I),
        round4M10Arg (round4Mix2ZeroMem I),
        ⟨2383⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix2ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 22888 := by
  have hprefix := validPositiveRound4Mix2DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix3ArgsFromRound4Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix2ZeroMem I)
    (startGas := 22795)
    (round4Mix2ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least five rounds: the fourth round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix3ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2199⟩
      [round4M15Arg (round4Mix2OneMem I),
        round4M10Arg (round4Mix2OneMem I),
        ⟨2383⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix2OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 22915 := by
  have hprefix := validPositiveRound4Mix2DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix3ArgsFromRound4Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix2OneMem I)
    (startGas := 22822)
    (round4Mix2OneMem_size hlen)
    hprefix

end Blake2f
