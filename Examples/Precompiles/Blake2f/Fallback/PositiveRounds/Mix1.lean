import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix1Selector

/-!
# BLAKE2F fallback positive-round traces: second `mixG`

This module continues the first positive-round body from PC `1739`, the shared `mixG` routine for
round-0 vector slots `v[1]`, `v[5]`, `v[9]`, and `v[13]`, using message words `m[2]` and `m[3]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev secondMixV1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))

abbrev secondMixV5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev secondMixV9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))

abbrev secondMixV13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))

abbrev secondMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (secondMixV1Load mem + secondMixV5Load mem + firstRoundM2Arg mem)

abbrev secondMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (secondMixV13Load mem) (secondMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev secondMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (secondMixV9Load mem + secondMixD0 mem)

abbrev secondMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (secondMixV5Load mem) (secondMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev secondMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (secondMixA0 mem + secondMixB0 mem + firstRoundM3Arg mem)

abbrev secondMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (secondMixD0 mem) (secondMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev secondMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (secondMixC0 mem + secondMixD1 mem)

abbrev secondMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (secondMixB0 mem) (secondMixC1 mem)) ⟨63⟩ ⟨1⟩

def secondMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (secondMixA1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨32⟩).toNat 32

def secondMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (secondMixB1 mem)).write 0 (secondMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨160⟩).toNat 32

def secondMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (secondMixC1 mem)).write 0 (secondMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨288⟩).toNat 32

def secondMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (secondMixD1 mem)).write 0 (secondMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨416⟩).toNat 32

theorem secondMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (secondMixMem0 mem).size = 1984 := by
  unfold secondMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem secondMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (secondMixMem1 mem).size = 1984 := by
  unfold secondMixMem1
  apply toByteArray_write32_size_of_le
  · exact secondMixMem0_size hmem
  · rw [secondMixMem0_size hmem]
    decide
  · native_decide

theorem secondMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (secondMixMem2 mem).size = 1984 := by
  unfold secondMixMem2
  apply toByteArray_write32_size_of_le
  · exact secondMixMem1_size hmem
  · rw [secondMixMem1_size hmem]
    decide
  · native_decide

theorem secondMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (secondMixMem3 mem).size = 1984 := by
  unfold secondMixMem3
  apply toByteArray_write32_size_of_le
  · exact secondMixMem2_size hmem
  · rw [secondMixMem2_size hmem]
    decide
  · native_decide

private theorem secondMixMload1504 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1504⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1504⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))) =
      secondMixV1Load mem := by
  unfold secondMixV1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1504⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem secondMixMload1632 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1632⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1632⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))) =
      secondMixV5Load mem := by
  unfold secondMixV5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1632⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem secondMixMload1760 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1760⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1760⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))) =
      secondMixV9Load mem := by
  unfold secondMixV9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1760⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem secondMixMload1888 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1888⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1888⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))) =
      secondMixV13Load mem := by
  unfold secondMixV13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1888⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem secondMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1739⟩
        [firstRoundM3Arg mem, firstRoundM2Arg mem, ⟨1923⟩, sigmaRound0Word,
          ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1923⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (secondMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd1739⟩ := hprefix
  have hmload1504 := secondMixMload1504 hmem
  have hmload1632 := secondMixMload1632 hmem
  have hmload1760 := secondMixMload1760 hmem
  have hmload1888 := secondMixMload1888 hmem
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
    raw mload 0 (secondMixV1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1504
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (secondMixV5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1632
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (secondMixV9Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (secondMixV13Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (secondMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold secondMixMem0
        simp [secondMixA1, secondMixB0, secondMixC0, secondMixD0, secondMixA0,
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
    raw mstore 0 (secondMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold secondMixMem1
        simp [secondMixB1, secondMixC1, secondMixD1, secondMixA1, secondMixB0,
          secondMixC0, secondMixD0, secondMixA0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (secondMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold secondMixMem2
        simp [secondMixC1, secondMixD1, secondMixA1, secondMixB0, secondMixC0,
          secondMixD0, secondMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (secondMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold secondMixMem3
        simp [secondMixD1, secondMixA1, secondMixB0, secondMixC0, secondMixD0,
          secondMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [secondMixA0, secondMixD0, secondMixC0, secondMixB0, secondMixA1, secondMixD1,
      secondMixC1, secondMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord,
      Nat.add_assoc] using rd1923⟩

/-- Final-flag-`0` positive-round inputs have completed the second round-0 `mixG`. -/
theorem validPositiveRoundMix1DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1923⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (secondMixMem3 (firstMixMem3 (v13MixedMem I)))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8557 := by
  have hprefix := validPositiveRoundMix1ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using secondMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := firstMixMem3 (v13MixedMem I)) (startGas := 8236)
    (firstMixMem3_size (v13MixedMem_size I hlen)) hprefix

/-- Final-flag-`1` positive-round inputs have completed the second round-0 `mixG`. -/
theorem validPositiveRoundMix1DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1923⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8584 := by
  have hprefix := validPositiveRoundMix1ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using secondMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := firstMixMem3 (v14FinalFlagMem I)) (startGas := 8263)
    (firstMixMem3_size (v14FinalFlagMem_size I hlen)) hprefix

end Blake2f
