import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix2

/-!
# BLAKE2F fallback positive-round traces: round-3 fourth `mixG` argument setup

This module continues the path with at least four rounds from PC `2153`. For round 3, the
bytecode extracts SIGMA indices `6` and `7`, loads message words `m[11]` and `m[14]`, and jumps to
the next shared `mixG` body at PC `2199`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-3 SIGMA index `6` selects bytecode memory offset `992`, i.e. `m[11]`. -/
theorem sigmaRound3Offset6 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨31⟩)
    ⟨480⟩ = (⟨992⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `7` selects bytecode memory offset `1088`, i.e. `m[14]`. -/
theorem sigmaRound3Offset7 : UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨27⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1088⟩ : UInt256) := by
  native_decide

abbrev round3M11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 992 32))

abbrev round3M14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1088 32))

abbrev round3M11Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M11Load mem) u64MaskWord

abbrev round3M14Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M14Load mem) u64MaskWord

private theorem round3Mix3ArgsMloadM11 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨31⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨31⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨31⟩) ⟨480⟩).toNat 32))) =
      round3M11Load mem := by
  rw [sigmaRound3Offset6]
  unfold round3M11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix3ArgsMloadM14 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨27⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨27⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M14Load mem := by
  rw [sigmaRound3Offset7]
  unfold round3M14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1088⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix3ArgsFromRound3Mix2Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2153⟩
        [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round3M14Arg mem, round3M11Arg mem, ⟨2383⟩, sigmaRound3Word,
        ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2153⟩ := hprefix
  have hmloadM11 := round3Mix3ArgsMloadM11 hmem
  have hmloadM14 := round3Mix3ArgsMloadM14 hmem
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
    raw mload 0 (round3M11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM11
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨27⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M14Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM14
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M11Arg, round3M14Arg] using rd2199⟩

def round3Mix2ZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix2Mem3 (round3Mix1ZeroMem I)

def round3Mix2OneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix2Mem3 (round3Mix1OneMem I)

theorem round3Mix2ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix2ZeroMem I).size = 1984 := by
  unfold round3Mix2ZeroMem
  exact round3Mix2Mem3_size (round3Mix1ZeroMem_size hlen)

theorem round3Mix2OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3Mix2OneMem I).size = 1984 := by
  unfold round3Mix2OneMem
  exact round3Mix2Mem3_size (round3Mix1OneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the fourth round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix3ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round3M14Arg (round3Mix2ZeroMem I),
        round3M11Arg (round3Mix2ZeroMem I),
        ⟨2383⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix2ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 19399 := by
  have hprefix := validPositiveRound3Mix2DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix3ArgsFromRound3Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix2ZeroMem I)
    (startGas := 19306)
    (round3Mix2ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the fourth round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix3ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2199⟩
      [round3M14Arg (round3Mix2OneMem I),
        round3M11Arg (round3Mix2OneMem I),
        ⟨2383⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix2OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 19426 := by
  have hprefix := validPositiveRound3Mix2DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix3ArgsFromRound3Mix2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix2OneMem I)
    (startGas := 19333)
    (round3Mix2OneMem_size hlen)
    hprefix

end Blake2f
