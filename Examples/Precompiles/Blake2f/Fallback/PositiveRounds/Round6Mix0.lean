import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round6Selector

/-!
# BLAKE2F fallback positive-round traces: round-6 first `mixG`

This module continues the path with at least seven rounds from PC `1512`, the shared `mixG`
routine for round 6. The first round-6 call updates bytecode vector slots `v[0]`, `v[4]`,
`v[8]`, and `v[12]` using message words `m[12]` and `m[5]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round6Mix0V0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev round6Mix0V4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))

abbrev round6Mix0V8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))

abbrev round6Mix0V12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))

abbrev round6Mix0A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round6Mix0V0Load mem + round6Mix0V4Load mem + round6M12Arg mem)

abbrev round6Mix0D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round6Mix0V12Load mem) (round6Mix0A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round6Mix0C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round6Mix0V8Load mem + round6Mix0D0 mem)

abbrev round6Mix0B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round6Mix0V4Load mem) (round6Mix0C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round6Mix0A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round6Mix0A0 mem + round6Mix0B0 mem + round6M5Arg mem)

abbrev round6Mix0D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round6Mix0D0 mem) (round6Mix0A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round6Mix0C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round6Mix0C0 mem + round6Mix0D1 mem)

abbrev round6Mix0B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round6Mix0B0 mem) (round6Mix0C1 mem)) ⟨63⟩ ⟨1⟩

def round6Mix0Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round6Mix0A1 mem)).write 0 mem (⟨1472⟩ : UInt256).toNat 32

def round6Mix0Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round6Mix0B1 mem)).write 0 (round6Mix0Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨128⟩).toNat 32

def round6Mix0Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round6Mix0C1 mem)).write 0 (round6Mix0Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨256⟩).toNat 32

def round6Mix0Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round6Mix0D1 mem)).write 0 (round6Mix0Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨384⟩).toNat 32

theorem round6Mix0Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round6Mix0Mem0 mem).size = 1984 := by
  unfold round6Mix0Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round6Mix0Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round6Mix0Mem1 mem).size = 1984 := by
  unfold round6Mix0Mem1
  apply toByteArray_write32_size_of_le
  · exact round6Mix0Mem0_size hmem
  · rw [round6Mix0Mem0_size hmem]
    decide
  · native_decide

theorem round6Mix0Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round6Mix0Mem2 mem).size = 1984 := by
  unfold round6Mix0Mem2
  apply toByteArray_write32_size_of_le
  · exact round6Mix0Mem1_size hmem
  · rw [round6Mix0Mem1_size hmem]
    decide
  · native_decide

theorem round6Mix0Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round6Mix0Mem3 mem).size = 1984 := by
  unfold round6Mix0Mem3
  apply toByteArray_write32_size_of_le
  · exact round6Mix0Mem2_size hmem
  · rw [round6Mix0Mem2_size hmem]
    decide
  · native_decide

private theorem round6Mix0Mload1472 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
      round6Mix0V0Load mem := by
  unfold round6Mix0V0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix0Mload1600 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1600⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1600⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))) =
      round6Mix0V4Load mem := by
  unfold round6Mix0V4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1600⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix0Mload1728 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1728⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1728⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))) =
      round6Mix0V8Load mem := by
  unfold round6Mix0V8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1728⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix0Mload1856 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1856⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1856⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))) =
      round6Mix0V12Load mem := by
  unfold round6Mix0V12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1856⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix0BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1512⟩
        [round6M5Arg mem, round6M12Arg mem, ⟨1693⟩,
          sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1693⟩
      [sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix0Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 315) := by
  obtain ⟨k0, rd1512⟩ := hprefix
  have hmload1472 := round6Mix0Mload1472 hmem
  have hmload1600 := round6Mix0Mload1600 hmem
  have hmload1728 := round6Mix0Mload1728 hmem
  have hmload1856 := round6Mix0Mload1856 hmem
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
    raw mload 0 (round6Mix0V0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round6Mix0V4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1600
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round6Mix0V8Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (round6Mix0V12Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (round6Mix0Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round6Mix0Mem0
        simp [round6Mix0A1, round6Mix0B0, round6Mix0C0, round6Mix0D0, round6Mix0A0,
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
    raw mstore 0 (round6Mix0Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round6Mix0Mem1
        simp [round6Mix0B1, round6Mix0C1, round6Mix0D1, round6Mix0A1, round6Mix0B0,
          round6Mix0C0, round6Mix0D0, round6Mix0A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round6Mix0Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round6Mix0Mem2
        simp [round6Mix0C1, round6Mix0D1, round6Mix0A1, round6Mix0B0, round6Mix0C0,
          round6Mix0D0, round6Mix0A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round6Mix0Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round6Mix0Mem3
        simp [round6Mix0D1, round6Mix0A1, round6Mix0B0, round6Mix0C0, round6Mix0D0,
          round6Mix0A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round6Mix0A0, round6Mix0D0, round6Mix0C0, round6Mix0B0, round6Mix0A1,
      round6Mix0D1, round6Mix0C1, round6Mix0B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd1693⟩

/-- Final-flag-`0`, at least seven rounds: the first round-6 `mixG` call is complete. -/
theorem validPositiveRound6Mix0DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1693⟩
      [sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix0Mem3 (round5DoneZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 29011 := by
  have hprefix := validPositiveRound6Mix0ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix0BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5DoneZeroMem I)
    (startGas := 28696)
    (round5DoneZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least seven rounds: the first round-6 `mixG` call is complete. -/
theorem validPositiveRound6Mix0DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1693⟩
      [sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round6Mix0Mem3 (round5DoneOneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 29038 := by
  have hprefix := validPositiveRound6Mix0ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix0BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5DoneOneMem I)
    (startGas := 28723)
    (round5DoneOneMem_size hlen)
    hprefix

end Blake2f
