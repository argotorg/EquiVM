import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix3

/-!
# BLAKE2F fallback positive-round traces: round-5 first diagonal `mixG` argument setup

This module continues the path with at least six rounds from PC `2383`. For round 5, the
bytecode extracts SIGMA indices `8` and `9`, loads message words `m[4]` and `m[13]`, and jumps to
the first diagonal shared `mixG` body at PC `2429`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-5 SIGMA index `8` selects bytecode memory offset `768`, i.e. `m[4]`. -/
theorem sigmaRound5Offset8 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨23⟩)
    ⟨480⟩ = (⟨768⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `9` selects bytecode memory offset `1056`, i.e. `m[13]`. -/
theorem sigmaRound5Offset9 : UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨19⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1056⟩ : UInt256) := by
  native_decide

abbrev round5M4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 768 32))

abbrev round5M13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1056 32))

abbrev round5M4Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M4Load mem) u64MaskWord

abbrev round5M13Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M13Load mem) u64MaskWord

private theorem round5Mix4ArgsMloadM4 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨23⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨23⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨23⟩) ⟨480⟩).toNat 32))) =
      round5M4Load mem := by
  rw [sigmaRound5Offset8]
  unfold round5M4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨768⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix4ArgsMloadM13 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨19⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M13Load mem := by
  rw [sigmaRound5Offset9]
  unfold round5M13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1056⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix4ArgsFromRound5Mix3Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2383⟩
        [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round5M13Arg mem, round5M4Arg mem, ⟨2610⟩, sigmaRound5Word,
        ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2383⟩ := hprefix
  have hmloadM4 := round5Mix4ArgsMloadM4 hmem
  have hmloadM13 := round5Mix4ArgsMloadM13 hmem
  have rd2429 := evm_run rd2383 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨2610⟩,
    push2 ⟨2429⟩,
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
    push1 ⟨23⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round5M4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM4
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨19⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M13Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M4Arg, round5M13Arg] using rd2429⟩

def round5Mix3ZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix3Mem3 (round5Mix2ZeroMem I)

def round5Mix3OneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix3Mem3 (round5Mix2OneMem I)

theorem round5Mix3ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix3ZeroMem I).size = 1984 := by
  unfold round5Mix3ZeroMem
  exact round5Mix3Mem3_size (round5Mix2ZeroMem_size hlen)

theorem round5Mix3OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5Mix3OneMem I).size = 1984 := by
  unfold round5Mix3OneMem
  exact round5Mix3Mem3_size (round5Mix2OneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the first diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix4ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2429⟩
      [round5M13Arg (round5Mix3ZeroMem I),
        round5M4Arg (round5Mix3ZeroMem I),
        ⟨2610⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix3ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 26813 := by
  have hprefix := validPositiveRound5Mix3DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix4ArgsFromRound5Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix3ZeroMem I)
    (startGas := 26720)
    (round5Mix3ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the first diagonal round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix4ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2429⟩
      [round5M13Arg (round5Mix3OneMem I),
        round5M4Arg (round5Mix3OneMem I),
        ⟨2610⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix3OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 26840 := by
  have hprefix := validPositiveRound5Mix3DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix4ArgsFromRound5Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix3OneMem I)
    (startGas := 26747)
    (round5Mix3OneMem_size hlen)
    hprefix

end Blake2f
