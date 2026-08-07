import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix3Selector

/-!
# BLAKE2F fallback positive-round traces: fourth `mixG`

This module continues the first positive-round body from PC `2199`, the shared `mixG` routine for
round-0 vector slots `v[3]`, `v[7]`, `v[11]`, and `v[15]`, using message words `m[6]` and `m[7]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev fourthMixV3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))

abbrev fourthMixV7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))

abbrev fourthMixV11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))

abbrev fourthMixV15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev fourthMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fourthMixV3Load mem + fourthMixV7Load mem + firstRoundM6Arg mem)

abbrev fourthMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fourthMixV15Load mem) (fourthMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev fourthMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fourthMixV11Load mem + fourthMixD0 mem)

abbrev fourthMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fourthMixV7Load mem) (fourthMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev fourthMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fourthMixA0 mem + fourthMixB0 mem + firstRoundM7Arg mem)

abbrev fourthMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fourthMixD0 mem) (fourthMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev fourthMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fourthMixC0 mem + fourthMixD1 mem)

abbrev fourthMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fourthMixB0 mem) (fourthMixC1 mem)) ⟨63⟩ ⟨1⟩

def fourthMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fourthMixA1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨96⟩).toNat 32

def fourthMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fourthMixB1 mem)).write 0 (fourthMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨224⟩).toNat 32

def fourthMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fourthMixC1 mem)).write 0 (fourthMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨352⟩).toNat 32

def fourthMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fourthMixD1 mem)).write 0 (fourthMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨480⟩).toNat 32

theorem fourthMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fourthMixMem0 mem).size = 1984 := by
  unfold fourthMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem fourthMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fourthMixMem1 mem).size = 1984 := by
  unfold fourthMixMem1
  apply toByteArray_write32_size_of_le
  · exact fourthMixMem0_size hmem
  · rw [fourthMixMem0_size hmem]
    decide
  · native_decide

theorem fourthMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fourthMixMem2 mem).size = 1984 := by
  unfold fourthMixMem2
  apply toByteArray_write32_size_of_le
  · exact fourthMixMem1_size hmem
  · rw [fourthMixMem1_size hmem]
    decide
  · native_decide

theorem fourthMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fourthMixMem3 mem).size = 1984 := by
  unfold fourthMixMem3
  apply toByteArray_write32_size_of_le
  · exact fourthMixMem2_size hmem
  · rw [fourthMixMem2_size hmem]
    decide
  · native_decide

private theorem fourthMixMload1568 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1568⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1568⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))) =
      fourthMixV3Load mem := by
  unfold fourthMixV3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1568⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fourthMixMload1696 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1696⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1696⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))) =
      fourthMixV7Load mem := by
  unfold fourthMixV7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1696⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fourthMixMload1824 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1824⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1824⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))) =
      fourthMixV11Load mem := by
  unfold fourthMixV11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1824⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fourthMixMload1952 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
      fourthMixV15Load mem := by
  unfold fourthMixV15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fourthMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2199⟩
        [firstRoundM7Arg mem, firstRoundM6Arg mem, ⟨2383⟩, sigmaRound0Word,
          ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2383⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fourthMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd2199⟩ := hprefix
  have hmload1568 := fourthMixMload1568 hmem
  have hmload1696 := fourthMixMload1696 hmem
  have hmload1824 := fourthMixMload1824 hmem
  have hmload1952 := fourthMixMload1952 hmem
  have rd2383 := evm_run rd2199 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨480⟩,
    dup13,
    add,
    push2 ⟨352⟩,
    dup14,
    add,
    dup14,
    push1 ⟨96⟩,
    push1 ⟨224⟩,
    dup3,
    add,
    swap2,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (fourthMixV3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1568
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (fourthMixV7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1696
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (fourthMixV11Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (fourthMixV15Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (fourthMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fourthMixMem0
        simp [fourthMixA1, fourthMixB0, fourthMixC0, fourthMixD0, fourthMixA0,
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
    raw mstore 0 (fourthMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fourthMixMem1
        simp [fourthMixB1, fourthMixC1, fourthMixD1, fourthMixA1, fourthMixB0,
          fourthMixC0, fourthMixD0, fourthMixA0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (fourthMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fourthMixMem2
        simp [fourthMixC1, fourthMixD1, fourthMixA1, fourthMixB0, fourthMixC0,
          fourthMixD0, fourthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (fourthMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fourthMixMem3
        simp [fourthMixD1, fourthMixA1, fourthMixB0, fourthMixC0, fourthMixD0,
          fourthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [fourthMixA0, fourthMixD0, fourthMixC0, fourthMixB0, fourthMixA1, fourthMixD1,
      fourthMixC1, fourthMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord,
      Nat.add_assoc] using rd2383⟩

/-- Final-flag-`0` positive-round inputs have completed the fourth round-0 `mixG`. -/
theorem validPositiveRoundMix3DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2383⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9385 := by
  have hprefix := validPositiveRoundMix3ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using fourthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))) (startGas := 9064)
    (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))) hprefix

/-- Final-flag-`1` positive-round inputs have completed the fourth round-0 `mixG`. -/
theorem validPositiveRoundMix3DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2383⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9412 := by
  have hprefix := validPositiveRoundMix3ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using fourthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))) (startGas := 9091)
    (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))) hprefix

end Blake2f
