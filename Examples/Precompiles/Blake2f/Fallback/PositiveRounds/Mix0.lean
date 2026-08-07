import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Selector

/-!
# BLAKE2F fallback positive-round traces: first `mixG`

This module continues the first positive-round body from PC `1512`, the shared `mixG` routine.
For round `0`, the first call updates bytecode vector slots `v[0]`, `v[4]`, `v[8]`, and `v[12]`
using message words `m[0]` and `m[1]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev firstMixV0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev firstMixV4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))

abbrev firstMixV8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))

abbrev firstMixV12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))

abbrev mask64Bytecode (x : UInt256) : UInt256 :=
  UInt256.land u64MaskWord x

abbrev rotr64Bytecode (x : UInt256) (right left : UInt256) : UInt256 :=
  mask64Bytecode (UInt256.lor (UInt256.shiftRight x right) (UInt256.shiftLeft x left))

abbrev firstMixA0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (firstMixV0Load mem + firstMixV4Load mem + firstRoundM0Arg mem)

abbrev firstMixD0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (firstMixV12Load mem) (firstMixA0 mem)) ⟨32⟩ ⟨32⟩

abbrev firstMixC0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (firstMixV8Load mem + firstMixD0 mem)

abbrev firstMixB0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (firstMixV4Load mem) (firstMixC0 mem)) ⟨24⟩ ⟨40⟩

abbrev firstMixA1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (firstMixA0 mem + firstMixB0 mem + firstRoundM1Arg mem)

abbrev firstMixD1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (firstMixD0 mem) (firstMixA1 mem)) ⟨16⟩ ⟨48⟩

abbrev firstMixC1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (firstMixC0 mem + firstMixD1 mem)

abbrev firstMixB1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (firstMixB0 mem) (firstMixC1 mem)) ⟨63⟩ ⟨1⟩

def firstMixMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (firstMixA1 mem)).write 0 mem (⟨1472⟩ : UInt256).toNat 32

def firstMixMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (firstMixB1 mem)).write 0 (firstMixMem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨128⟩).toNat 32

def firstMixMem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (firstMixC1 mem)).write 0 (firstMixMem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨256⟩).toNat 32

def firstMixMem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (firstMixD1 mem)).write 0 (firstMixMem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨384⟩).toNat 32

theorem firstMixMem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (firstMixMem0 mem).size = 1984 := by
  unfold firstMixMem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem firstMixMem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (firstMixMem1 mem).size = 1984 := by
  unfold firstMixMem1
  apply toByteArray_write32_size_of_le
  · exact firstMixMem0_size hmem
  · rw [firstMixMem0_size hmem]
    decide
  · native_decide

theorem firstMixMem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (firstMixMem2 mem).size = 1984 := by
  unfold firstMixMem2
  apply toByteArray_write32_size_of_le
  · exact firstMixMem1_size hmem
  · rw [firstMixMem1_size hmem]
    decide
  · native_decide

theorem firstMixMem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (firstMixMem3 mem).size = 1984 := by
  unfold firstMixMem3
  apply toByteArray_write32_size_of_le
  · exact firstMixMem2_size hmem
  · rw [firstMixMem2_size hmem]
    decide
  · native_decide

private theorem firstMixMload1472 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
      firstMixV0Load mem := by
  unfold firstMixV0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem firstMixMload1600 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1600⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1600⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))) =
      firstMixV4Load mem := by
  unfold firstMixV4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1600⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem firstMixMload1728 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1728⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1728⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))) =
      firstMixV8Load mem := by
  unfold firstMixV8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1728⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem firstMixMload1856 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1856⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1856⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))) =
      firstMixV12Load mem := by
  unfold firstMixV12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1856⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem firstMixBodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1512⟩
        [firstRoundM1Arg mem, firstRoundM0Arg mem, ⟨1693⟩, sigmaRound0Word,
          ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1693⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (firstMixMem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 315) := by
  obtain ⟨k0, rd1512⟩ := hprefix
  have hmload1472 := firstMixMload1472 hmem
  have hmload1600 := firstMixMload1600 hmem
  have hmload1728 := firstMixMload1728 hmem
  have hmload1856 := firstMixMload1856 hmem
  have rd1693 := evm_run rd1512 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨384⟩,
    dup13,
    add,
    push2 ⟨256⟩,
    dup14,
    add,
    dup14,
    push1 ⟨128⟩,
    dup2,
    add,
    swap1,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (firstMixV0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (firstMixV4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1600
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (firstMixV8Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (firstMixV12Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (firstMixMem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold firstMixMem0
        simp [firstMixA1, firstMixB0, firstMixC0, firstMixD0, firstMixA0, rotr64Bytecode,
          mask64Bytecode, u64MaskWord])
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
    raw mstore 0 (firstMixMem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold firstMixMem1
        simp [firstMixB1, firstMixC1, firstMixD1, firstMixA1, firstMixB0, firstMixC0,
          firstMixD0, firstMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (firstMixMem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold firstMixMem2
        simp [firstMixC1, firstMixD1, firstMixA1, firstMixB0, firstMixC0, firstMixD0,
          firstMixA0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (firstMixMem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold firstMixMem3
        simp [firstMixD1, firstMixA1, firstMixB0, firstMixC0, firstMixD0, firstMixA0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [firstMixA0, firstMixD0, firstMixC0, firstMixB0, firstMixA1, firstMixD1,
      firstMixC1, firstMixB1, rotr64Bytecode, mask64Bytecode, u64MaskWord, Nat.add_assoc] using rd1693⟩

/-- Final-flag-`0` positive-round inputs have completed the first round-0 `mixG`. -/
theorem validPositiveRoundMix0DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1693⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (firstMixMem3 (v13MixedMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8143 := by
  have hprefix := validPositiveRoundMix0ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using firstMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := v13MixedMem I) (startGas := 7828) (v13MixedMem_size I hlen) hprefix

/-- Final-flag-`1` positive-round inputs have completed the first round-0 `mixG`. -/
theorem validPositiveRoundMix0DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1693⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (firstMixMem3 (v14FinalFlagMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8170 := by
  have hprefix := validPositiveRoundMix0ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  simpa using firstMixBodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := v14FinalFlagMem I) (startGas := 7855) (v14FinalFlagMem_size I hlen) hprefix

end Blake2f
