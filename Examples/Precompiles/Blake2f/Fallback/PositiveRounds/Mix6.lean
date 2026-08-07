import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix6Selector

/-!
# BLAKE2F fallback positive-round traces: seventh `mixG`

This module continues the first positive-round body from PC `2886`, the third diagonal `mixG`
routine for round-0 vector slots `v[2]`, `v[7]`, `v[8]`, and `v[13]`, using message words
`m[12]` and `m[13]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev seventhMixV2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))

abbrev seventhMixV7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))

abbrev seventhMixV8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))

abbrev seventhMixV13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))

abbrev seventhMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (seventhMixV2Load mem + seventhMixV7Load mem + firstRoundM12Arg mem)

abbrev seventhMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (seventhMixV13Load mem) (seventhMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev seventhMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (seventhMixV8Load mem + seventhMixD0 mem)

abbrev seventhMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (seventhMixV7Load mem) (seventhMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev seventhMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (seventhMixA0 mem + seventhMixB0 mem + firstRoundM13Arg mem)

abbrev seventhMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (seventhMixD0 mem) (seventhMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev seventhMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (seventhMixC0 mem + seventhMixD1 mem)

abbrev seventhMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (seventhMixB0 mem) (seventhMixC1 mem)) ⟨63⟩ ⟨1⟩

def seventhMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (seventhMixA1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨64⟩).toNat 32

def seventhMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (seventhMixB1 mem)).write 0 (seventhMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨224⟩).toNat 32

def seventhMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (seventhMixC1 mem)).write 0 (seventhMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨256⟩).toNat 32

def seventhMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (seventhMixD1 mem)).write 0 (seventhMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨416⟩).toNat 32

theorem seventhMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (seventhMixMem0 mem).size = 1984 := by
  unfold seventhMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem seventhMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (seventhMixMem1 mem).size = 1984 := by
  unfold seventhMixMem1
  apply toByteArray_write32_size_of_le
  · exact seventhMixMem0_size hmem
  · rw [seventhMixMem0_size hmem]
    decide
  · native_decide

theorem seventhMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (seventhMixMem2 mem).size = 1984 := by
  unfold seventhMixMem2
  apply toByteArray_write32_size_of_le
  · exact seventhMixMem1_size hmem
  · rw [seventhMixMem1_size hmem]
    decide
  · native_decide

theorem seventhMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (seventhMixMem3 mem).size = 1984 := by
  unfold seventhMixMem3
  apply toByteArray_write32_size_of_le
  · exact seventhMixMem2_size hmem
  · rw [seventhMixMem2_size hmem]
    decide
  · native_decide

private theorem seventhMixMload1536 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1536⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1536⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))) =
      seventhMixV2Load mem := by
  unfold seventhMixV2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1536⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem seventhMixMload1696 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1696⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1696⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))) =
      seventhMixV7Load mem := by
  unfold seventhMixV7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1696⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem seventhMixMload1728 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1728⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1728⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))) =
      seventhMixV8Load mem := by
  unfold seventhMixV8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1728⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem seventhMixMload1888 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1888⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1888⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))) =
      seventhMixV13Load mem := by
  unfold seventhMixV13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1888⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem seventhMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2886⟩
        [firstRoundM13Arg mem, firstRoundM12Arg mem, ⟨3070⟩, sigmaRound0Word,
          ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3070⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (seventhMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd2886⟩ := hprefix
  have hmload1536 := seventhMixMload1536 hmem
  have hmload1696 := seventhMixMload1696 hmem
  have hmload1728 := seventhMixMload1728 hmem
  have hmload1888 := seventhMixMload1888 hmem
  have rd3070 := evm_run rd2886 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨416⟩,
    dup13,
    add,
    push2 ⟨256⟩,
    dup14,
    add,
    dup14,
    push1 ⟨64⟩,
    push1 ⟨224⟩,
    dup3,
    add,
    swap2,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (seventhMixV2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1536
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (seventhMixV7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1696
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (seventhMixV8Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1728
      (by native_decide) (by evm_ov),
    swap2,
    dup9,
    dup9,
    raw mload 0 (seventhMixV13Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (seventhMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold seventhMixMem0
        simp [seventhMixA1, seventhMixB0, seventhMixC0, seventhMixD0, seventhMixA0,
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
    raw mstore 0 (seventhMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold seventhMixMem1
        simp [seventhMixB1, seventhMixC1, seventhMixD1, seventhMixA1, seventhMixB0,
          seventhMixC0, seventhMixD0, seventhMixA0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (seventhMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold seventhMixMem2
        simp [seventhMixC1, seventhMixD1, seventhMixA1, seventhMixB0, seventhMixC0,
          seventhMixD0, seventhMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (seventhMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold seventhMixMem3
        simp [seventhMixD1, seventhMixA1, seventhMixB0, seventhMixC0, seventhMixD0,
          seventhMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [seventhMixA0, seventhMixD0, seventhMixC0, seventhMixB0, seventhMixA1, seventhMixD1,
      seventhMixC1, seventhMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord,
      Nat.add_assoc] using rd3070⟩

/-- Final-flag-`0` positive-round inputs have completed the third diagonal round-0 `mixG`. -/
theorem validPositiveRoundMix6DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3070⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (seventhMixMem3
        (sixthMixMem3
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10621 := by
  have hprefix := validPositiveRoundMix6ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using seventhMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := sixthMixMem3
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))
    (startGas := 10300)
    (sixthMixMem3_size
      (fifthMixMem3_size
        (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))))))
    hprefix

/-- Final-flag-`1` positive-round inputs have completed the third diagonal round-0 `mixG`. -/
theorem validPositiveRoundMix6DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3070⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (seventhMixMem3
        (sixthMixMem3
          (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 10648 := by
  have hprefix := validPositiveRoundMix6ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using seventhMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := sixthMixMem3
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))
    (startGas := 10327)
    (sixthMixMem3_size
      (fifthMixMem3_size
        (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))))))
    hprefix

end Blake2f
