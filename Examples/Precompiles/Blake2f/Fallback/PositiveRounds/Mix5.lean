import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix5Selector

/-!
# BLAKE2F fallback positive-round traces: sixth `mixG`

This module continues the first positive-round body from PC `2656`, the second diagonal `mixG`
routine for round-0 vector slots `v[1]`, `v[6]`, `v[11]`, and `v[12]`, using message words
`m[10]` and `m[11]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev sixthMixV1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))

abbrev sixthMixV6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))

abbrev sixthMixV11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))

abbrev sixthMixV12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))

abbrev sixthMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (sixthMixV1Load mem + sixthMixV6Load mem + firstRoundM10Arg mem)

abbrev sixthMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (sixthMixV12Load mem) (sixthMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev sixthMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (sixthMixV11Load mem + sixthMixD0 mem)

abbrev sixthMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (sixthMixV6Load mem) (sixthMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev sixthMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (sixthMixA0 mem + sixthMixB0 mem + firstRoundM11Arg mem)

abbrev sixthMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (sixthMixD0 mem) (sixthMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev sixthMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (sixthMixC0 mem + sixthMixD1 mem)

abbrev sixthMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (sixthMixB0 mem) (sixthMixC1 mem)) ⟨63⟩ ⟨1⟩

def sixthMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (sixthMixA1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨32⟩).toNat 32

def sixthMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (sixthMixB1 mem)).write 0 (sixthMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨192⟩).toNat 32

def sixthMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (sixthMixC1 mem)).write 0 (sixthMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨352⟩).toNat 32

def sixthMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (sixthMixD1 mem)).write 0 (sixthMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨384⟩).toNat 32

theorem sixthMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (sixthMixMem0 mem).size = 1984 := by
  unfold sixthMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem sixthMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (sixthMixMem1 mem).size = 1984 := by
  unfold sixthMixMem1
  apply toByteArray_write32_size_of_le
  · exact sixthMixMem0_size hmem
  · rw [sixthMixMem0_size hmem]
    decide
  · native_decide

theorem sixthMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (sixthMixMem2 mem).size = 1984 := by
  unfold sixthMixMem2
  apply toByteArray_write32_size_of_le
  · exact sixthMixMem1_size hmem
  · rw [sixthMixMem1_size hmem]
    decide
  · native_decide

theorem sixthMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (sixthMixMem3 mem).size = 1984 := by
  unfold sixthMixMem3
  apply toByteArray_write32_size_of_le
  · exact sixthMixMem2_size hmem
  · rw [sixthMixMem2_size hmem]
    decide
  · native_decide

private theorem sixthMixMload1504 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1504⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1504⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))) =
      sixthMixV1Load mem := by
  unfold sixthMixV1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1504⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem sixthMixMload1664 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1664⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1664⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))) =
      sixthMixV6Load mem := by
  unfold sixthMixV6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1664⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem sixthMixMload1824 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1824⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1824⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))) =
      sixthMixV11Load mem := by
  unfold sixthMixV11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1824⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem sixthMixMload1856 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1856⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1856⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))) =
      sixthMixV12Load mem := by
  unfold sixthMixV12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1856⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem sixthMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2656⟩
        [firstRoundM11Arg mem, firstRoundM10Arg mem, ⟨2840⟩, sigmaRound0Word,
          ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2840⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (sixthMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd2656⟩ := hprefix
  have hmload1504 := sixthMixMload1504 hmem
  have hmload1664 := sixthMixMload1664 hmem
  have hmload1824 := sixthMixMload1824 hmem
  have hmload1856 := sixthMixMload1856 hmem
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
    raw mload 0 (sixthMixV1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1504
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (sixthMixV6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1664
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (sixthMixV11Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (sixthMixV12Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (sixthMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold sixthMixMem0
        simp [sixthMixA1, sixthMixB0, sixthMixC0, sixthMixD0, sixthMixA0,
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
    raw mstore 0 (sixthMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold sixthMixMem1
        simp [sixthMixB1, sixthMixC1, sixthMixD1, sixthMixA1, sixthMixB0,
          sixthMixC0, sixthMixD0, sixthMixA0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (sixthMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold sixthMixMem2
        simp [sixthMixC1, sixthMixD1, sixthMixA1, sixthMixB0, sixthMixC0,
          sixthMixD0, sixthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (sixthMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold sixthMixMem3
        simp [sixthMixD1, sixthMixA1, sixthMixB0, sixthMixC0, sixthMixD0,
          sixthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [sixthMixA0, sixthMixD0, sixthMixC0, sixthMixB0, sixthMixA1, sixthMixD1,
      sixthMixC1, sixthMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord,
      Nat.add_assoc] using rd2840⟩

/-- Final-flag-`0` positive-round inputs have completed the second diagonal round-0 `mixG`. -/
theorem validPositiveRoundMix5DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2840⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10207 := by
  have hprefix := validPositiveRoundMix5ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using sixthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))
    (startGas := 9886)
    (fifthMixMem3_size
      (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))))
    hprefix

/-- Final-flag-`1` positive-round inputs have completed the second diagonal round-0 `mixG`. -/
theorem validPositiveRoundMix5DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2840⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10234 := by
  have hprefix := validPositiveRoundMix5ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using sixthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))
    (startGas := 9913)
    (fifthMixMem3_size
      (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))))
    hprefix

end Blake2f
