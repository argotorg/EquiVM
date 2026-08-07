import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix5Selector

/-!
# BLAKE2F fallback positive-round traces: round-5 second diagonal `mixG`

This module continues the path with at least six rounds from PC `2656`, the second diagonal
`mixG` routine for round-5 vector slots `v[1]`, `v[6]`, `v[11]`, and `v[12]`, using message words
`m[7]` and `m[5]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round5Mix5V1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))

abbrev round5Mix5V6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))

abbrev round5Mix5V11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))

abbrev round5Mix5V12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))

abbrev round5Mix5A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix5V1Load mem + round5Mix5V6Load mem + round5M7Arg mem)

abbrev round5Mix5D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix5V12Load mem) (round5Mix5A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round5Mix5C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix5V11Load mem + round5Mix5D0 mem)

abbrev round5Mix5B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix5V6Load mem) (round5Mix5C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round5Mix5A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix5A0 mem + round5Mix5B0 mem + round5M5Arg mem)

abbrev round5Mix5D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix5D0 mem) (round5Mix5A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round5Mix5C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix5C0 mem + round5Mix5D1 mem)

abbrev round5Mix5B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix5B0 mem) (round5Mix5C1 mem)) ⟨63⟩ ⟨1⟩

def round5Mix5Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix5A1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨32⟩).toNat 32

def round5Mix5Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix5B1 mem)).write 0 (round5Mix5Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨192⟩).toNat 32

def round5Mix5Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix5C1 mem)).write 0 (round5Mix5Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨352⟩).toNat 32

def round5Mix5Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix5D1 mem)).write 0 (round5Mix5Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨384⟩).toNat 32

theorem round5Mix5Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix5Mem0 mem).size = 1984 := by
  unfold round5Mix5Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round5Mix5Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix5Mem1 mem).size = 1984 := by
  unfold round5Mix5Mem1
  apply toByteArray_write32_size_of_le
  · exact round5Mix5Mem0_size hmem
  · rw [round5Mix5Mem0_size hmem]
    decide
  · native_decide

theorem round5Mix5Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix5Mem2 mem).size = 1984 := by
  unfold round5Mix5Mem2
  apply toByteArray_write32_size_of_le
  · exact round5Mix5Mem1_size hmem
  · rw [round5Mix5Mem1_size hmem]
    decide
  · native_decide

theorem round5Mix5Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix5Mem3 mem).size = 1984 := by
  unfold round5Mix5Mem3
  apply toByteArray_write32_size_of_le
  · exact round5Mix5Mem2_size hmem
  · rw [round5Mix5Mem2_size hmem]
    decide
  · native_decide

private theorem round5Mix5Mload1504 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1504⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1504⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))) =
      round5Mix5V1Load mem := by
  unfold round5Mix5V1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1504⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix5Mload1664 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1664⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1664⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))) =
      round5Mix5V6Load mem := by
  unfold round5Mix5V6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1664⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix5Mload1824 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1824⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1824⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))) =
      round5Mix5V11Load mem := by
  unfold round5Mix5V11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1824⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix5Mload1856 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1856⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1856⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))) =
      round5Mix5V12Load mem := by
  unfold round5Mix5V12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1856⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix5BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2656⟩
        [round5M5Arg mem, round5M7Arg mem, ⟨2840⟩, sigmaRound5Word,
          ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2840⟩
      [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix5Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd2656⟩ := hprefix
  have hmload1504 := round5Mix5Mload1504 hmem
  have hmload1664 := round5Mix5Mload1664 hmem
  have hmload1824 := round5Mix5Mload1824 hmem
  have hmload1856 := round5Mix5Mload1856 hmem
  have rd2840 := evm_run rd2656 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨384⟩,
    dup13,
    add,
    push2 ⟨352⟩,
    dup14,
    add,
    dup14,
    push1 ⟨32⟩,
    push1 ⟨192⟩,
    dup3,
    add,
    swap2,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (round5Mix5V1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1504
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round5Mix5V6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1664
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round5Mix5V11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1824
      (by native_decide) (by evm_ov),
    swap2,
    dup9,
    dup9,
    raw mload 0 (round5Mix5V12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1856
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
    raw mstore 0 (round5Mix5Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix5Mem0
        simp [round5Mix5A1, round5Mix5B0, round5Mix5C0, round5Mix5D0, round5Mix5A0,
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
    raw mstore 0 (round5Mix5Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix5Mem1
        simp [round5Mix5B1, round5Mix5C1, round5Mix5D1, round5Mix5A1, round5Mix5B0,
          round5Mix5C0, round5Mix5D0, round5Mix5A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round5Mix5Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix5Mem2
        simp [round5Mix5C1, round5Mix5D1, round5Mix5A1, round5Mix5B0, round5Mix5C0,
          round5Mix5D0, round5Mix5A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round5Mix5Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix5Mem3
        simp [round5Mix5D1, round5Mix5A1, round5Mix5B0, round5Mix5C0, round5Mix5D0,
          round5Mix5A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round5Mix5A0, round5Mix5D0, round5Mix5C0, round5Mix5B0, round5Mix5A1,
      round5Mix5D1, round5Mix5C1, round5Mix5B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd2840⟩

/-- Final-flag-`0`, at least six rounds: the second diagonal round-5 `mixG` call is complete. -/
theorem validPositiveRound5Mix5DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2840⟩
      [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix5Mem3 (round5Mix4ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 27542 := by
  have hprefix := validPositiveRound5Mix5ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix5BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix4ZeroMem I)
    (startGas := 27221)
    (round5Mix4ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the second diagonal round-5 `mixG` call is complete. -/
theorem validPositiveRound5Mix5DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨2840⟩
      [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix5Mem3 (round5Mix4OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 27569 := by
  have hprefix := validPositiveRound5Mix5ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix5BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix4OneMem I)
    (startGas := 27248)
    (round5Mix4OneMem_size hlen)
    hprefix

end Blake2f
