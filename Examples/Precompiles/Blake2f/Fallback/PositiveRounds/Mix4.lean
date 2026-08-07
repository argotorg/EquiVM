import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Mix4Selector

/-!
# BLAKE2F fallback positive-round traces: fifth `mixG`

This module continues the first positive-round body from PC `2429`, the first diagonal `mixG`
routine for round-0 vector slots `v[0]`, `v[5]`, `v[10]`, and `v[15]`, using message words
`m[8]` and `m[9]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev fifthMixV0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev fifthMixV5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev fifthMixV10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))

abbrev fifthMixV15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev fifthMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fifthMixV0Load mem + fifthMixV5Load mem + firstRoundM8Arg mem)

abbrev fifthMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fifthMixV15Load mem) (fifthMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev fifthMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fifthMixV10Load mem + fifthMixD0 mem)

abbrev fifthMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fifthMixV5Load mem) (fifthMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev fifthMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fifthMixA0 mem + fifthMixB0 mem + firstRoundM9Arg mem)

abbrev fifthMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fifthMixD0 mem) (fifthMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev fifthMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (fifthMixC0 mem + fifthMixD1 mem)

abbrev fifthMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (fifthMixB0 mem) (fifthMixC1 mem)) ⟨63⟩ ⟨1⟩

def fifthMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fifthMixA1 mem)).write 0 mem
    (⟨1472⟩ : UInt256).toNat 32

def fifthMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fifthMixB1 mem)).write 0 (fifthMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨160⟩).toNat 32

def fifthMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fifthMixC1 mem)).write 0 (fifthMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨320⟩).toNat 32

def fifthMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (fifthMixD1 mem)).write 0 (fifthMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨480⟩).toNat 32

theorem fifthMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fifthMixMem0 mem).size = 1984 := by
  unfold fifthMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem fifthMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fifthMixMem1 mem).size = 1984 := by
  unfold fifthMixMem1
  apply toByteArray_write32_size_of_le
  · exact fifthMixMem0_size hmem
  · rw [fifthMixMem0_size hmem]
    decide
  · native_decide

theorem fifthMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fifthMixMem2 mem).size = 1984 := by
  unfold fifthMixMem2
  apply toByteArray_write32_size_of_le
  · exact fifthMixMem1_size hmem
  · rw [fifthMixMem1_size hmem]
    decide
  · native_decide

theorem fifthMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (fifthMixMem3 mem).size = 1984 := by
  unfold fifthMixMem3
  apply toByteArray_write32_size_of_le
  · exact fifthMixMem2_size hmem
  · rw [fifthMixMem2_size hmem]
    decide
  · native_decide

private theorem fifthMixMload1472 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
      fifthMixV0Load mem := by
  unfold fifthMixV0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fifthMixMload1632 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1632⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1632⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))) =
      fifthMixV5Load mem := by
  unfold fifthMixV5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1632⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fifthMixMload1792 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1792⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1792⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))) =
      fifthMixV10Load mem := by
  unfold fifthMixV10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1792⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fifthMixMload1952 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
      fifthMixV15Load mem := by
  unfold fifthMixV15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem fifthMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2429⟩
        [firstRoundM9Arg mem, firstRoundM8Arg mem, ⟨2610⟩, sigmaRound0Word,
          ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fifthMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 315) := by
  obtain ⟨k0, rd2429⟩ := hprefix
  have hmload1472 := fifthMixMload1472 hmem
  have hmload1632 := fifthMixMload1632 hmem
  have hmload1792 := fifthMixMload1792 hmem
  have hmload1952 := fifthMixMload1952 hmem
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
    raw mload 0 (fifthMixV0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (fifthMixV5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1632
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (fifthMixV10Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (fifthMixV15Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (fifthMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fifthMixMem0
        simp [fifthMixA1, fifthMixB0, fifthMixC0, fifthMixD0, fifthMixA0,
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
    raw mstore 0 (fifthMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fifthMixMem1
        simp [fifthMixB1, fifthMixC1, fifthMixD1, fifthMixA1, fifthMixB0,
          fifthMixC0, fifthMixD0, fifthMixA0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (fifthMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fifthMixMem2
        simp [fifthMixC1, fifthMixD1, fifthMixA1, fifthMixB0, fifthMixC0,
          fifthMixD0, fifthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (fifthMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold fifthMixMem3
        simp [fifthMixD1, fifthMixA1, fifthMixB0, fifthMixC0, fifthMixD0,
          fifthMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [fifthMixA0, fifthMixD0, fifthMixC0, fifthMixB0, fifthMixA1, fifthMixD1,
      fifthMixC1, fifthMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord,
      Nat.add_assoc] using rd2610⟩

/-- Final-flag-`0` positive-round inputs have completed the first diagonal round-0 `mixG`. -/
theorem validPositiveRoundMix4DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9793 := by
  have hprefix := validPositiveRoundMix4ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using fifthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))) (startGas := 9478)
    (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen))))) hprefix

/-- Final-flag-`1` positive-round inputs have completed the first diagonal round-0 `mixG`. -/
theorem validPositiveRoundMix4DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 9820 := by
  have hprefix := validPositiveRoundMix4ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using fifthMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))) (startGas := 9505)
    (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen))))) hprefix

end Blake2f
