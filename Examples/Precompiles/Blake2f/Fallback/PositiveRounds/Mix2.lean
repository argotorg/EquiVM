import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix2Selector

/-!
# BLAKE2F fallback positive-round traces: third `mixG`

This module continues the first positive-round body from PC `1969`, the shared `mixG` routine for
round-0 vector slots `v[2]`, `v[6]`, `v[10]`, and `v[14]`, using message words `m[4]` and `m[5]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev thirdMixV2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))

abbrev thirdMixV6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))

abbrev thirdMixV10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))

abbrev thirdMixV14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))

abbrev thirdMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (thirdMixV2Load mem + thirdMixV6Load mem + firstRoundM4Arg mem)

abbrev thirdMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (thirdMixV14Load mem) (thirdMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev thirdMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (thirdMixV10Load mem + thirdMixD0 mem)

abbrev thirdMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (thirdMixV6Load mem) (thirdMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev thirdMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (thirdMixA0 mem + thirdMixB0 mem + firstRoundM5Arg mem)

abbrev thirdMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (thirdMixD0 mem) (thirdMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev thirdMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (thirdMixC0 mem + thirdMixD1 mem)

abbrev thirdMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (thirdMixB0 mem) (thirdMixC1 mem)) ⟨63⟩ ⟨1⟩

def thirdMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (thirdMixA1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨64⟩).toNat 32

def thirdMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (thirdMixB1 mem)).write 0 (thirdMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨192⟩).toNat 32

def thirdMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (thirdMixC1 mem)).write 0 (thirdMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨320⟩).toNat 32

def thirdMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (thirdMixD1 mem)).write 0 (thirdMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨448⟩).toNat 32

theorem thirdMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (thirdMixMem0 mem).size = 1984 := by
  unfold thirdMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem thirdMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (thirdMixMem1 mem).size = 1984 := by
  unfold thirdMixMem1
  apply toByteArray_write32_size_of_le
  · exact thirdMixMem0_size hmem
  · rw [thirdMixMem0_size hmem]
    decide
  · native_decide

theorem thirdMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (thirdMixMem2 mem).size = 1984 := by
  unfold thirdMixMem2
  apply toByteArray_write32_size_of_le
  · exact thirdMixMem1_size hmem
  · rw [thirdMixMem1_size hmem]
    decide
  · native_decide

theorem thirdMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (thirdMixMem3 mem).size = 1984 := by
  unfold thirdMixMem3
  apply toByteArray_write32_size_of_le
  · exact thirdMixMem2_size hmem
  · rw [thirdMixMem2_size hmem]
    decide
  · native_decide

private theorem thirdMixMload1536 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1536⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1536⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))) =
      thirdMixV2Load mem := by
  unfold thirdMixV2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1536⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem thirdMixMload1664 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1664⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1664⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))) =
      thirdMixV6Load mem := by
  unfold thirdMixV6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1664⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem thirdMixMload1792 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1792⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1792⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))) =
      thirdMixV10Load mem := by
  unfold thirdMixV10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1792⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem thirdMixMload1920 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1920⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1920⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))) =
      thirdMixV14Load mem := by
  unfold thirdMixV14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1920⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem thirdMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1969⟩
        [firstRoundM5Arg mem, firstRoundM4Arg mem, ⟨2153⟩, sigmaRound0Word,
          ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2153⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (thirdMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd1969⟩ := hprefix
  have hmload1536 := thirdMixMload1536 hmem
  have hmload1664 := thirdMixMload1664 hmem
  have hmload1792 := thirdMixMload1792 hmem
  have hmload1920 := thirdMixMload1920 hmem
  have rd2153 := evm_run rd1969 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨448⟩,
    dup13,
    add,
    push2 ⟨320⟩,
    dup14,
    add,
    dup14,
    push1 ⟨64⟩,
    push1 ⟨192⟩,
    dup3,
    add,
    swap2,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (thirdMixV2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1536
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (thirdMixV6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1664
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (thirdMixV10Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (thirdMixV14Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1920
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
    raw mstore 0 (thirdMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold thirdMixMem0
        simp [thirdMixA1, thirdMixB0, thirdMixC0, thirdMixD0, thirdMixA0,
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
    raw mstore 0 (thirdMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold thirdMixMem1
        simp [thirdMixB1, thirdMixC1, thirdMixD1, thirdMixA1, thirdMixB0,
          thirdMixC0, thirdMixD0, thirdMixA0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (thirdMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold thirdMixMem2
        simp [thirdMixC1, thirdMixD1, thirdMixA1, thirdMixB0, thirdMixC0,
          thirdMixD0, thirdMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (thirdMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold thirdMixMem3
        simp [thirdMixD1, thirdMixA1, thirdMixB0, thirdMixC0, thirdMixD0,
          thirdMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [thirdMixA0, thirdMixD0, thirdMixC0, thirdMixB0, thirdMixA1, thirdMixD1,
      thirdMixC1, thirdMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord,
      Nat.add_assoc] using rd2153⟩

/-- Final-flag-`0` positive-round inputs have completed the third round-0 `mixG`. -/
theorem validPositiveRoundMix2DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2153⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8971 := by
  have hprefix := validPositiveRoundMix2ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using thirdMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := secondMixMem3 (firstMixMem3 (v13MixedMem I))) (startGas := 8650)
    (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))) hprefix

/-- Final-flag-`1` positive-round inputs have completed the third round-0 `mixG`. -/
theorem validPositiveRoundMix2DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2153⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8998 := by
  have hprefix := validPositiveRoundMix2ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using thirdMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))) (startGas := 8677)
    (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))) hprefix

end Blake2f
