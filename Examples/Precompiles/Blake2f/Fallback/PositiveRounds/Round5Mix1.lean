import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5Mix1Selector

/-!
# BLAKE2F fallback positive-round traces: round-5 second `mixG`

This module continues the path with at least six rounds from PC `1739`. The second round-5 call
updates bytecode vector slots `v[1]`, `v[5]`, `v[9]`, and `v[13]` using message words `m[6]` and
`m[10]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round5Mix1V1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))

abbrev round5Mix1V5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev round5Mix1V9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))

abbrev round5Mix1V13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))

abbrev round5Mix1A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix1V1Load mem + round5Mix1V5Load mem + round5M6Arg mem)

abbrev round5Mix1D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix1V13Load mem) (round5Mix1A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round5Mix1C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix1V9Load mem + round5Mix1D0 mem)

abbrev round5Mix1B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix1V5Load mem) (round5Mix1C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round5Mix1A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix1A0 mem + round5Mix1B0 mem + round5M10Arg mem)

abbrev round5Mix1D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix1D0 mem) (round5Mix1A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round5Mix1C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round5Mix1C0 mem + round5Mix1D1 mem)

abbrev round5Mix1B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round5Mix1B0 mem) (round5Mix1C1 mem)) ⟨63⟩ ⟨1⟩

def round5Mix1Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix1A1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨32⟩).toNat 32

def round5Mix1Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix1B1 mem)).write 0 (round5Mix1Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨160⟩).toNat 32

def round5Mix1Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix1C1 mem)).write 0 (round5Mix1Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨288⟩).toNat 32

def round5Mix1Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round5Mix1D1 mem)).write 0 (round5Mix1Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨416⟩).toNat 32

theorem round5Mix1Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix1Mem0 mem).size = 1984 := by
  unfold round5Mix1Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round5Mix1Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix1Mem1 mem).size = 1984 := by
  unfold round5Mix1Mem1
  apply toByteArray_write32_size_of_le
  · exact round5Mix1Mem0_size hmem
  · rw [round5Mix1Mem0_size hmem]
    decide
  · native_decide

theorem round5Mix1Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix1Mem2 mem).size = 1984 := by
  unfold round5Mix1Mem2
  apply toByteArray_write32_size_of_le
  · exact round5Mix1Mem1_size hmem
  · rw [round5Mix1Mem1_size hmem]
    decide
  · native_decide

theorem round5Mix1Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round5Mix1Mem3 mem).size = 1984 := by
  unfold round5Mix1Mem3
  apply toByteArray_write32_size_of_le
  · exact round5Mix1Mem2_size hmem
  · rw [round5Mix1Mem2_size hmem]
    decide
  · native_decide

private theorem round5Mix1Mload1504 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1504⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1504⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))) =
      round5Mix1V1Load mem := by
  unfold round5Mix1V1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1504⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix1Mload1632 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1632⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1632⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))) =
      round5Mix1V5Load mem := by
  unfold round5Mix1V5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1632⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix1Mload1760 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1760⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1760⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))) =
      round5Mix1V9Load mem := by
  unfold round5Mix1V9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1760⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix1Mload1888 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1888⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1888⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))) =
      round5Mix1V13Load mem := by
  unfold round5Mix1V13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1888⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix1BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1739⟩
        [round5M10Arg mem, round5M6Arg mem, ⟨1923⟩, sigmaRound5Word,
          ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1923⟩
      [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix1Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd1739⟩ := hprefix
  have hmload1504 := round5Mix1Mload1504 hmem
  have hmload1632 := round5Mix1Mload1632 hmem
  have hmload1760 := round5Mix1Mload1760 hmem
  have hmload1888 := round5Mix1Mload1888 hmem
  have rd1923 := evm_run rd1739 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨416⟩,
    dup13,
    add,
    push2 ⟨288⟩,
    dup14,
    add,
    dup14,
    push1 ⟨32⟩,
    push1 ⟨160⟩,
    dup3,
    add,
    swap2,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (round5Mix1V1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1504
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round5Mix1V5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1632
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round5Mix1V9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1760
      (by native_decide) (by evm_ov),
    swap2,
    dup9,
    dup9,
    raw mload 0 (round5Mix1V13Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1888
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
    raw mstore 0 (round5Mix1Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix1Mem0
        simp [round5Mix1A1, round5Mix1B0, round5Mix1C0, round5Mix1D0, round5Mix1A0,
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
    raw mstore 0 (round5Mix1Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix1Mem1
        simp [round5Mix1B1, round5Mix1C1, round5Mix1D1, round5Mix1A1, round5Mix1B0,
          round5Mix1C0, round5Mix1D0, round5Mix1A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round5Mix1Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix1Mem2
        simp [round5Mix1C1, round5Mix1D1, round5Mix1A1, round5Mix1B0, round5Mix1C0,
          round5Mix1D0, round5Mix1A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round5Mix1Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round5Mix1Mem3
        simp [round5Mix1D1, round5Mix1A1, round5Mix1B0, round5Mix1C0, round5Mix1D0,
          round5Mix1A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round5Mix1A0, round5Mix1D0, round5Mix1C0, round5Mix1B0, round5Mix1A1,
      round5Mix1D1, round5Mix1C1, round5Mix1B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd1923⟩

/-- Final-flag-`0`, at least six rounds: the second round-5 `mixG` call is complete. -/
theorem validPositiveRound5Mix1DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1923⟩
      [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix1Mem3 (round5Mix0ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 25892 := by
  have hprefix := validPositiveRound5Mix1ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix1BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix0ZeroMem I)
    (startGas := 25571)
    (round5Mix0ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the second round-5 `mixG` call is complete. -/
theorem validPositiveRound5Mix1DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1923⟩
      [sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix1Mem3 (round5Mix0OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 25919 := by
  have hprefix := validPositiveRound5Mix1ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix1BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix0OneMem I)
    (startGas := 25598)
    (round5Mix0OneMem_size hlen)
    hprefix

end Blake2f
