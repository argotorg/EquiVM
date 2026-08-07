import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round2Mix4Selector

/-!
# BLAKE2F fallback positive-round traces: round-2 first diagonal `mixG`

This module continues the path with at least three rounds from PC `2429`, the first diagonal
`mixG` routine for round-2 vector slots `v[0]`, `v[5]`, `v[10]`, and `v[15]`, using message words
`m[10]` and `m[14]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round2Mix4V0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev round2Mix4V5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev round2Mix4V10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))

abbrev round2Mix4V15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev round2Mix4A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round2Mix4V0Load mem + round2Mix4V5Load mem + round2M10Arg mem)

abbrev round2Mix4D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round2Mix4V15Load mem) (round2Mix4A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round2Mix4C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round2Mix4V10Load mem + round2Mix4D0 mem)

abbrev round2Mix4B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round2Mix4V5Load mem) (round2Mix4C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round2Mix4A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round2Mix4A0 mem + round2Mix4B0 mem + round2M14Arg mem)

abbrev round2Mix4D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round2Mix4D0 mem) (round2Mix4A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round2Mix4C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round2Mix4C0 mem + round2Mix4D1 mem)

abbrev round2Mix4B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round2Mix4B0 mem) (round2Mix4C1 mem)) ⟨63⟩ ⟨1⟩

def round2Mix4Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round2Mix4A1 mem)).write 0 mem
    (⟨1472⟩ : UInt256).toNat 32

def round2Mix4Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round2Mix4B1 mem)).write 0 (round2Mix4Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨160⟩).toNat 32

def round2Mix4Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round2Mix4C1 mem)).write 0 (round2Mix4Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨320⟩).toNat 32

def round2Mix4Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round2Mix4D1 mem)).write 0 (round2Mix4Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨480⟩).toNat 32

theorem round2Mix4Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round2Mix4Mem0 mem).size = 1984 := by
  unfold round2Mix4Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round2Mix4Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round2Mix4Mem1 mem).size = 1984 := by
  unfold round2Mix4Mem1
  apply toByteArray_write32_size_of_le
  · exact round2Mix4Mem0_size hmem
  · rw [round2Mix4Mem0_size hmem]
    decide
  · native_decide

theorem round2Mix4Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round2Mix4Mem2 mem).size = 1984 := by
  unfold round2Mix4Mem2
  apply toByteArray_write32_size_of_le
  · exact round2Mix4Mem1_size hmem
  · rw [round2Mix4Mem1_size hmem]
    decide
  · native_decide

theorem round2Mix4Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round2Mix4Mem3 mem).size = 1984 := by
  unfold round2Mix4Mem3
  apply toByteArray_write32_size_of_le
  · exact round2Mix4Mem2_size hmem
  · rw [round2Mix4Mem2_size hmem]
    decide
  · native_decide

private theorem round2Mix4Mload1472 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
      round2Mix4V0Load mem := by
  unfold round2Mix4V0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix4Mload1632 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1632⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1632⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))) =
      round2Mix4V5Load mem := by
  unfold round2Mix4V5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1632⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix4Mload1792 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1792⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1792⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))) =
      round2Mix4V10Load mem := by
  unfold round2Mix4V10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1792⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix4Mload1952 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
      round2Mix4V15Load mem := by
  unfold round2Mix4V15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix4BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2429⟩
        [round2M14Arg mem, round2M10Arg mem, ⟨2610⟩, sigmaRound2Word,
          ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix4Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 315) := by
  obtain ⟨k0, rd2429⟩ := hprefix
  have hmload1472 := round2Mix4Mload1472 hmem
  have hmload1632 := round2Mix4Mload1632 hmem
  have hmload1792 := round2Mix4Mload1792 hmem
  have hmload1952 := round2Mix4Mload1952 hmem
  have rd2610 := evm_run rd2429 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨480⟩,
    dup13,
    add,
    push2 ⟨320⟩,
    dup14,
    add,
    dup14,
    push1 ⟨160⟩,
    dup2,
    add,
    swap1,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (round2Mix4V0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round2Mix4V5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1632
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round2Mix4V10Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1792
      (by native_decide) (by evm_ov),
    swap2,
    dup9,
    dup9,
    raw mload 0 (round2Mix4V15Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1952
      (by native_decide) (by evm_ov),
    swap8,
    add,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap7,
    xor,
    dup1,
    push1 ⟨32⟩,
    shl,
    swap1,
    push1 ⟨32⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    dup1,
    swap3,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap9,
    xor,
    dup1,
    push1 ⟨40⟩,
    shl,
    swap1,
    push1 ⟨24⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    dup1,
    swap7,
    add,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap2,
    xor,
    dup1,
    push1 ⟨48⟩,
    shl,
    swap1,
    push1 ⟨16⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    dup1,
    swap8,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap6,
    xor,
    swap2,
    raw mstore 0 (round2Mix4Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round2Mix4Mem0
        simp [round2Mix4A1, round2Mix4B0, round2Mix4C0, round2Mix4D0, round2Mix4A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    shl,
    swap1,
    push1 ⟨63⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    swap1,
    raw mstore 0 (round2Mix4Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round2Mix4Mem1
        simp [round2Mix4B1, round2Mix4C1, round2Mix4D1, round2Mix4A1, round2Mix4B0,
          round2Mix4C0, round2Mix4D0, round2Mix4A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round2Mix4Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round2Mix4Mem2
        simp [round2Mix4C1, round2Mix4D1, round2Mix4A1, round2Mix4B0, round2Mix4C0,
          round2Mix4D0, round2Mix4A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round2Mix4Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round2Mix4Mem3
        simp [round2Mix4D1, round2Mix4A1, round2Mix4B0, round2Mix4C0, round2Mix4D0,
          round2Mix4A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round2Mix4A0, round2Mix4D0, round2Mix4C0, round2Mix4B0, round2Mix4A1,
      round2Mix4D1, round2Mix4C1, round2Mix4B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd2610⟩

/-- Final-flag-`0`, at least three rounds: the first diagonal round-2 `mixG` call is complete. -/
theorem validPositiveRound2Mix4DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix4Mem3 (round2Mix3ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 16661 := by
  have hprefix := validPositiveRound2Mix4ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix4BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix3ZeroMem I)
    (startGas := 16346)
    (round2Mix3ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least three rounds: the first diagonal round-2 `mixG` call is complete. -/
theorem validPositiveRound2Mix4DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix4Mem3 (round2Mix3OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 16688 := by
  have hprefix := validPositiveRound2Mix4ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  simpa using round2Mix4BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix3OneMem I)
    (startGas := 16373)
    (round2Mix3OneMem_size hlen)
    hprefix

end Blake2f
