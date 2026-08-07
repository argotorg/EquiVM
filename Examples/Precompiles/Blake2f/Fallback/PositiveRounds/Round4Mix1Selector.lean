import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round4Mix0

/-!
# BLAKE2F fallback positive-round traces: round-4 second `mixG` argument setup

This module continues the path with at least five rounds from PC `1693`. For round 4, the
bytecode extracts SIGMA indices `2` and `3`, loads message words `m[5]` and `m[7]`, and jumps to
the next shared `mixG` body at PC `1739`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-4 SIGMA index `2` selects bytecode memory offset `800`, i.e. `m[5]`. -/
theorem sigmaRound4Offset2 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨47⟩)
    ⟨480⟩ = (⟨800⟩ : UInt256) := by
  native_decide

/-- Round-4 SIGMA index `3` selects bytecode memory offset `864`, i.e. `m[7]`. -/
theorem sigmaRound4Offset3 : UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨43⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨864⟩ : UInt256) := by
  native_decide

abbrev round4M5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 800 32))

abbrev round4M7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 864 32))

abbrev round4M5Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M5Load mem) u64MaskWord

abbrev round4M7Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M7Load mem) u64MaskWord

private theorem round4Mix1ArgsMloadM3 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨47⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨47⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨47⟩) ⟨480⟩).toNat 32))) =
      round4M5Load mem := by
  rw [sigmaRound4Offset2]
  unfold round4M5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix1ArgsMloadM1 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨43⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨43⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round4M7Load mem := by
  rw [sigmaRound4Offset3]
  unfold round4M7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix1ArgsFromRound4Mix0Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1693⟩
        [sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1739⟩
      [round4M7Arg mem, round4M5Arg mem, ⟨1923⟩, sigmaRound4Word,
        ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd1693⟩ := hprefix
  have hmloadM3 := round4Mix1ArgsMloadM3 hmem
  have hmloadM1 := round4Mix1ArgsMloadM1 hmem
  have rd1739 := evm_run rd1693 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1923⟩,
    push2 ⟨1739⟩,
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
    push1 ⟨47⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round4M5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM3
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨43⟩,
    shr,
    and,
    add,
    raw mload 0 (round4M7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM1
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound4Word, u64MaskWord, round4M5Arg, round4M7Arg] using rd1739⟩

def round4Mix0ZeroMem (I : ExecutionEnv) : ByteArray :=
  round4Mix0Mem3 (round3DoneZeroMem I)

def round4Mix0OneMem (I : ExecutionEnv) : ByteArray :=
  round4Mix0Mem3 (round3DoneOneMem I)

theorem round4Mix0ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix0ZeroMem I).size = 1984 := by
  unfold round4Mix0ZeroMem
  exact round4Mix0Mem3_size (round3DoneZeroMem_size hlen)

theorem round4Mix0OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix0OneMem I).size = 1984 := by
  unfold round4Mix0OneMem
  exact round4Mix0Mem3_size (round3DoneOneMem_size hlen)

/-- Final-flag-`0`, at least five rounds: the second round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix1ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1739⟩
      [round4M7Arg (round4Mix0ZeroMem I),
        round4M5Arg (round4Mix0ZeroMem I),
        ⟨1923⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix0ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 22060 := by
  have hprefix := validPositiveRound4Mix0DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix1ArgsFromRound4Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix0ZeroMem I)
    (startGas := 21967)
    (round4Mix0ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least five rounds: the second round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix1ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1739⟩
      [round4M7Arg (round4Mix0OneMem I),
        round4M5Arg (round4Mix0OneMem I),
        ⟨1923⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix0OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 22087 := by
  have hprefix := validPositiveRound4Mix0DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix1ArgsFromRound4Mix0Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix0OneMem I)
    (startGas := 21994)
    (round4Mix0OneMem_size hlen)
    hprefix

end Blake2f
