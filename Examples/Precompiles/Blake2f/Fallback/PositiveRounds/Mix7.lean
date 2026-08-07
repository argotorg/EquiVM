import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix7Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.ProofSupportExact

/-!
# BLAKE2F fallback positive-round traces: eighth `mixG`

This module continues the first positive-round body from PC `3109`, the last diagonal `mixG`
routine for round-0 vector slots `v[3]`, `v[4]`, `v[9]`, and `v[14]`, using message words
`m[14]` and `m[15]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev eighthMixV3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))

abbrev eighthMixV4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))

abbrev eighthMixV9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))

abbrev eighthMixV14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))

abbrev eighthMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (eighthMixV3Load mem + eighthMixV4Load mem + firstRoundM14Arg mem)

abbrev eighthMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (eighthMixV14Load mem) (eighthMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev eighthMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (eighthMixV9Load mem + eighthMixD0 mem)

abbrev eighthMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (eighthMixV4Load mem) (eighthMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev eighthMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (eighthMixA0 mem + eighthMixB0 mem + firstRoundM15Arg mem)

abbrev eighthMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (eighthMixD0 mem) (eighthMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev eighthMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (eighthMixC0 mem + eighthMixD1 mem)

abbrev eighthMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (eighthMixB0 mem) (eighthMixC1 mem)) ⟨63⟩ ⟨1⟩

def eighthMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (eighthMixA1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨96⟩).toNat 32

def eighthMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (eighthMixB1 mem)).write 0 (eighthMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨128⟩).toNat 32

def eighthMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (eighthMixC1 mem)).write 0 (eighthMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨288⟩).toNat 32

def eighthMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (eighthMixD1 mem)).write 0 (eighthMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨448⟩).toNat 32

theorem eighthMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (eighthMixMem0 mem).size = 1984 := by
  unfold eighthMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem eighthMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (eighthMixMem1 mem).size = 1984 := by
  unfold eighthMixMem1
  apply toByteArray_write32_size_of_le
  · exact eighthMixMem0_size hmem
  · rw [eighthMixMem0_size hmem]
    decide
  · native_decide

theorem eighthMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (eighthMixMem2 mem).size = 1984 := by
  unfold eighthMixMem2
  apply toByteArray_write32_size_of_le
  · exact eighthMixMem1_size hmem
  · rw [eighthMixMem1_size hmem]
    decide
  · native_decide

theorem eighthMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (eighthMixMem3 mem).size = 1984 := by
  unfold eighthMixMem3
  apply toByteArray_write32_size_of_le
  · exact eighthMixMem2_size hmem
  · rw [eighthMixMem2_size hmem]
    decide
  · native_decide

private theorem eighthMixMload1568 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1568⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1568⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))) =
      eighthMixV3Load mem := by
  unfold eighthMixV3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1568⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem eighthMixMload1600 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1600⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1600⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))) =
      eighthMixV4Load mem := by
  unfold eighthMixV4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1600⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem eighthMixMload1760 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1760⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1760⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))) =
      eighthMixV9Load mem := by
  unfold eighthMixV9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1760⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem eighthMixMload1920 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1920⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1920⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))) =
      eighthMixV14Load mem := by
  unfold eighthMixV14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1920⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem eighthMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3109⟩
        [firstRoundM15Arg mem, firstRoundM14Arg mem, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3292⟩
      [⟨0⟩, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (eighthMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 318) := by
  obtain ⟨k0, rd3109⟩ := hprefix
  have hmload1568 := eighthMixMload1568 hmem
  have hmload1600 := eighthMixMload1600 hmem
  have hmload1760 := eighthMixMload1760 hmem
  have hmload1920 := eighthMixMload1920 hmem
  have rd3292 := evm_run rd3109 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨448⟩,
    dup10,
    add,
    push2 ⟨288⟩,
    dup11,
    add,
    push1 ⟨128⟩,
    dup12,
    add,
    push1 ⟨96⟩,
    dup13,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (eighthMixV3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1568
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (eighthMixV4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1600
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (eighthMixV9Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (eighthMixV14Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (eighthMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold eighthMixMem0
        simp [eighthMixA1, eighthMixB0, eighthMixC0, eighthMixD0, eighthMixA0,
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
    raw mstore 0 (eighthMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold eighthMixMem1
        simp [eighthMixB1, eighthMixC1, eighthMixD1, eighthMixA1, eighthMixB0,
          eighthMixC0, eighthMixD0, eighthMixA0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (eighthMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold eighthMixMem2
        simp [eighthMixC1, eighthMixD1, eighthMixA1, eighthMixB0, eighthMixC0,
          eighthMixD0, eighthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (eighthMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold eighthMixMem3
        simp [eighthMixD1, eighthMixA1, eighthMixB0, eighthMixC0, eighthMixD0,
          eighthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [eighthMixA0, eighthMixD0, eighthMixC0, eighthMixB0, eighthMixA1, eighthMixD1,
      eighthMixC1, eighthMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord,
      Nat.add_assoc] using rd3292⟩

/-- Final-flag-`0` positive-round inputs have completed all eight round-0 `mixG` calls. -/
theorem validPositiveRoundMix7DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3292⟩
      [⟨0⟩, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 11023 := by
  have hprefix := validPositiveRoundMix7ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using eighthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := seventhMixMem3
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))
    (startGas := 10705)
    (seventhMixMem3_size
      (sixthMixMem3_size
        (fifthMixMem3_size
          (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))))))
    hprefix

/-- Final-flag-`1` positive-round inputs have completed all eight round-0 `mixG` calls. -/
theorem validPositiveRoundMix7DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3292⟩
      [⟨0⟩, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (eighthMixMem3
        (seventhMixMem3
          (sixthMixMem3
            (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 11050 := by
  have hprefix := validPositiveRoundMix7ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using eighthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := seventhMixMem3
      (sixthMixMem3
        (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))
    (startGas := 10732)
    (seventhMixMem3_size
      (sixthMixMem3_size
        (fifthMixMem3_size
          (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))))))
    hprefix

end Blake2f
