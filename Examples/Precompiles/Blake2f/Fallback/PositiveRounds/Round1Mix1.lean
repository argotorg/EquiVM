import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix1Selector

/-!
# BLAKE2F fallback positive-round traces: round-1 second `mixG`

This module continues the multi-round path from PC `1739`.  The second round-1 call updates
bytecode vector slots `v[1]`, `v[5]`, `v[9]`, and `v[13]` using message words `m[4]` and `m[8]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round1Mix1V1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))

abbrev round1Mix1V5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev round1Mix1V9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))

abbrev round1Mix1V13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))

abbrev round1Mix1A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix1V1Load mem + round1Mix1V5Load mem + secondRoundM4Arg mem)

abbrev round1Mix1D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix1V13Load mem) (round1Mix1A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round1Mix1C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix1V9Load mem + round1Mix1D0 mem)

abbrev round1Mix1B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix1V5Load mem) (round1Mix1C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round1Mix1A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix1A0 mem + round1Mix1B0 mem + secondRoundM8Arg mem)

abbrev round1Mix1D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix1D0 mem) (round1Mix1A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round1Mix1C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix1C0 mem + round1Mix1D1 mem)

abbrev round1Mix1B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix1B0 mem) (round1Mix1C1 mem)) ⟨63⟩ ⟨1⟩

def round1Mix1Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix1A1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨32⟩).toNat 32

def round1Mix1Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix1B1 mem)).write 0 (round1Mix1Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨160⟩).toNat 32

def round1Mix1Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix1C1 mem)).write 0 (round1Mix1Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨288⟩).toNat 32

def round1Mix1Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix1D1 mem)).write 0 (round1Mix1Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨416⟩).toNat 32

theorem round1Mix1Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix1Mem0 mem).size = 1984 := by
  unfold round1Mix1Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round1Mix1Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix1Mem1 mem).size = 1984 := by
  unfold round1Mix1Mem1
  apply toByteArray_write32_size_of_le
  · exact round1Mix1Mem0_size hmem
  · rw [round1Mix1Mem0_size hmem]
    decide
  · native_decide

theorem round1Mix1Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix1Mem2 mem).size = 1984 := by
  unfold round1Mix1Mem2
  apply toByteArray_write32_size_of_le
  · exact round1Mix1Mem1_size hmem
  · rw [round1Mix1Mem1_size hmem]
    decide
  · native_decide

theorem round1Mix1Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix1Mem3 mem).size = 1984 := by
  unfold round1Mix1Mem3
  apply toByteArray_write32_size_of_le
  · exact round1Mix1Mem2_size hmem
  · rw [round1Mix1Mem2_size hmem]
    decide
  · native_decide

private theorem round1Mix1Mload1504 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1504⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1504⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))) =
      round1Mix1V1Load mem := by
  unfold round1Mix1V1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1504⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix1Mload1632 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1632⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1632⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))) =
      round1Mix1V5Load mem := by
  unfold round1Mix1V5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1632⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix1Mload1760 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1760⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1760⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))) =
      round1Mix1V9Load mem := by
  unfold round1Mix1V9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1760⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix1Mload1888 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1888⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1888⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))) =
      round1Mix1V13Load mem := by
  unfold round1Mix1V13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1888⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix1BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1739⟩
        [secondRoundM8Arg mem, secondRoundM4Arg mem, ⟨1923⟩, sigmaRound1Word,
          ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1923⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix1Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd1739⟩ := hprefix
  have hmload1504 := round1Mix1Mload1504 hmem
  have hmload1632 := round1Mix1Mload1632 hmem
  have hmload1760 := round1Mix1Mload1760 hmem
  have hmload1888 := round1Mix1Mload1888 hmem
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
    raw mload 0 (round1Mix1V1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1504
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round1Mix1V5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1632
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round1Mix1V9Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (round1Mix1V13Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (round1Mix1Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix1Mem0
        simp [round1Mix1A1, round1Mix1B0, round1Mix1C0, round1Mix1D0, round1Mix1A0,
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
    raw mstore 0 (round1Mix1Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix1Mem1
        simp [round1Mix1B1, round1Mix1C1, round1Mix1D1, round1Mix1A1, round1Mix1B0,
          round1Mix1C0, round1Mix1D0, round1Mix1A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix1Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix1Mem2
        simp [round1Mix1C1, round1Mix1D1, round1Mix1A1, round1Mix1B0, round1Mix1C0,
          round1Mix1D0, round1Mix1A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix1Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix1Mem3
        simp [round1Mix1D1, round1Mix1A1, round1Mix1B0, round1Mix1C0, round1Mix1D0,
          round1Mix1A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round1Mix1A0, round1Mix1D0, round1Mix1C0, round1Mix1B0, round1Mix1A1,
      round1Mix1D1, round1Mix1C1, round1Mix1B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd1923⟩

/-- Final-flag-`0`, at least two rounds: the second round-1 `mixG` call is complete. -/
theorem validPositiveRound1Mix1DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1923⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix1Mem3
        (round1Mix0Mem3
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 11980 := by
  have hprefix := validPositiveRound1Mix1ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix1BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix0Mem3
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))
    (startGas := 11659)
    (round1Mix0Mem3_size
      (eighthMixMem3_size
        (seventhMixMem3_size
          (sixthMixMem3_size
            (fifthMixMem3_size
              (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))))))))
    hprefix

/-- Final-flag-`1`, at least two rounds: the second round-1 `mixG` call is complete. -/
theorem validPositiveRound1Mix1DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1923⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix1Mem3
        (round1Mix0Mem3
          (eighthMixMem3
            (seventhMixMem3
              (sixthMixMem3
                (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 12007 := by
  have hprefix := validPositiveRound1Mix1ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix1BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix0Mem3
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))
    (startGas := 11686)
    (round1Mix0Mem3_size
      (eighthMixMem3_size
        (seventhMixMem3_size
          (sixthMixMem3_size
            (fifthMixMem3_size
              (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))))))))
    hprefix

end Blake2f
