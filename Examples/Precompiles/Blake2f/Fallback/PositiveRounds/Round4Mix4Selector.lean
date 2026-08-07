import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round4Mix3

/-!
# BLAKE2F fallback positive-round traces: round-4 first diagonal `mixG` argument setup

This module continues the path with at least five rounds from PC `2383`. For round 4, the
bytecode extracts SIGMA indices `8` and `9`, loads message words `m[14]` and `m[1]`, and jumps to
the first diagonal shared `mixG` body at PC `2429`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Round-4 SIGMA index `8` selects bytecode memory offset `1088`, i.e. `m[14]`. -/
theorem sigmaRound4Offset8 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨23⟩)
    ⟨480⟩ = (⟨1088⟩ : UInt256) := by
  native_decide

/-- Round-4 SIGMA index `9` selects bytecode memory offset `672`, i.e. `m[1]`. -/
theorem sigmaRound4Offset9 : UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨19⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨672⟩ : UInt256) := by
  native_decide

abbrev round4M14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1088 32))

abbrev round4M1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 672 32))

abbrev round4M14Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M14Load mem) u64MaskWord

abbrev round4M1Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M1Load mem) u64MaskWord

private theorem round4Mix4ArgsMloadM14 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨23⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨23⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨23⟩) ⟨480⟩).toNat 32))) =
      round4M14Load mem := by
  rw [sigmaRound4Offset8]
  unfold round4M14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1088⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix4ArgsMloadM1 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨19⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨19⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round4M1Load mem := by
  rw [sigmaRound4Offset9]
  unfold round4M1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix4ArgsFromRound4Mix3Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2383⟩
        [sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2429⟩
      [round4M1Arg mem, round4M14Arg mem, ⟨2610⟩, sigmaRound4Word,
        ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 93) := by
  obtain ⟨k0, rd2383⟩ := hprefix
  have hmloadM14 := round4Mix4ArgsMloadM14 hmem
  have hmloadM1 := round4Mix4ArgsMloadM1 hmem
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
    raw mload 0 (round4M14Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM14
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨19⟩,
    shr,
    and,
    add,
    raw mload 0 (round4M1Load mem) (UInt256.ofNat 62)
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
  exact ⟨_, by simpa [sigmaRound4Word, u64MaskWord, round4M14Arg, round4M1Arg] using rd2429⟩

def round4Mix3ZeroMem (I : ExecutionEnv) : ByteArray :=
  round4Mix3Mem3 (round4Mix2ZeroMem I)

def round4Mix3OneMem (I : ExecutionEnv) : ByteArray :=
  round4Mix3Mem3 (round4Mix2OneMem I)

theorem round4Mix3ZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix3ZeroMem I).size = 1984 := by
  unfold round4Mix3ZeroMem
  exact round4Mix3Mem3_size (round4Mix2ZeroMem_size hlen)

theorem round4Mix3OneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4Mix3OneMem I).size = 1984 := by
  unfold round4Mix3OneMem
  exact round4Mix3Mem3_size (round4Mix2OneMem_size hlen)

/-- Final-flag-`0`, at least five rounds: the first diagonal round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix4ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2429⟩
      [round4M1Arg (round4Mix3ZeroMem I),
        round4M14Arg (round4Mix3ZeroMem I),
        ⟨2610⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix3ZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 23302 := by
  have hprefix := validPositiveRound4Mix3DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix4ArgsFromRound4Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix3ZeroMem I)
    (startGas := 23209)
    (round4Mix3ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least five rounds: the first diagonal round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix4ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2429⟩
      [round4M1Arg (round4Mix3OneMem I),
        round4M14Arg (round4Mix3OneMem I),
        ⟨2610⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4Mix3OneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 23329 := by
  have hprefix := validPositiveRound4Mix3DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix4ArgsFromRound4Mix3Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4Mix3OneMem I)
    (startGas := 23236)
    (round4Mix3OneMem_size hlen)
    hprefix

end Blake2f
