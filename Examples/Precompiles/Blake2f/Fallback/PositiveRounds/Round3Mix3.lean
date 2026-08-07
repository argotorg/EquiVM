import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round3Mix3Selector

/-!
# BLAKE2F fallback positive-round traces: round-3 fourth `mixG`

This module continues the path with at least four rounds from PC `2199`, the shared `mixG`
routine for round-3 vector slots `v[3]`, `v[7]`, `v[11]`, and `v[15]`, using message words
`m[11]` and `m[14]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round3Mix3V3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))

abbrev round3Mix3V7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))

abbrev round3Mix3V11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))

abbrev round3Mix3V15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev round3Mix3A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round3Mix3V3Load mem + round3Mix3V7Load mem + round3M11Arg mem)

abbrev round3Mix3D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round3Mix3V15Load mem) (round3Mix3A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round3Mix3C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round3Mix3V11Load mem + round3Mix3D0 mem)

abbrev round3Mix3B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round3Mix3V7Load mem) (round3Mix3C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round3Mix3A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round3Mix3A0 mem + round3Mix3B0 mem + round3M14Arg mem)

abbrev round3Mix3D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round3Mix3D0 mem) (round3Mix3A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round3Mix3C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round3Mix3C0 mem + round3Mix3D1 mem)

abbrev round3Mix3B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round3Mix3B0 mem) (round3Mix3C1 mem)) ⟨63⟩ ⟨1⟩

def round3Mix3Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round3Mix3A1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨96⟩).toNat 32

def round3Mix3Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round3Mix3B1 mem)).write 0 (round3Mix3Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨224⟩).toNat 32

def round3Mix3Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round3Mix3C1 mem)).write 0 (round3Mix3Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨352⟩).toNat 32

def round3Mix3Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round3Mix3D1 mem)).write 0 (round3Mix3Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨480⟩).toNat 32

theorem round3Mix3Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round3Mix3Mem0 mem).size = 1984 := by
  unfold round3Mix3Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round3Mix3Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round3Mix3Mem1 mem).size = 1984 := by
  unfold round3Mix3Mem1
  apply toByteArray_write32_size_of_le
  · exact round3Mix3Mem0_size hmem
  · rw [round3Mix3Mem0_size hmem]
    decide
  · native_decide

theorem round3Mix3Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round3Mix3Mem2 mem).size = 1984 := by
  unfold round3Mix3Mem2
  apply toByteArray_write32_size_of_le
  · exact round3Mix3Mem1_size hmem
  · rw [round3Mix3Mem1_size hmem]
    decide
  · native_decide

theorem round3Mix3Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round3Mix3Mem3 mem).size = 1984 := by
  unfold round3Mix3Mem3
  apply toByteArray_write32_size_of_le
  · exact round3Mix3Mem2_size hmem
  · rw [round3Mix3Mem2_size hmem]
    decide
  · native_decide

private theorem round3Mix3Mload1568 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1568⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1568⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))) =
      round3Mix3V3Load mem := by
  unfold round3Mix3V3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1568⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix3Mload1696 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1696⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1696⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))) =
      round3Mix3V7Load mem := by
  unfold round3Mix3V7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1696⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix3Mload1824 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1824⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1824⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))) =
      round3Mix3V11Load mem := by
  unfold round3Mix3V11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1824⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix3Mload1952 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
      round3Mix3V15Load mem := by
  unfold round3Mix3V15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix3BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2199⟩
        [round3M14Arg mem, round3M11Arg mem, ⟨2383⟩, sigmaRound3Word,
          ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2383⟩
      [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix3Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd2199⟩ := hprefix
  have hmload1568 := round3Mix3Mload1568 hmem
  have hmload1696 := round3Mix3Mload1696 hmem
  have hmload1824 := round3Mix3Mload1824 hmem
  have hmload1952 := round3Mix3Mload1952 hmem
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
    raw mload 0 (round3Mix3V3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1568
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round3Mix3V7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1696
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round3Mix3V11Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (round3Mix3V15Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (round3Mix3Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round3Mix3Mem0
        simp [round3Mix3A1, round3Mix3B0, round3Mix3C0, round3Mix3D0, round3Mix3A0,
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
    raw mstore 0 (round3Mix3Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round3Mix3Mem1
        simp [round3Mix3B1, round3Mix3C1, round3Mix3D1, round3Mix3A1, round3Mix3B0,
          round3Mix3C0, round3Mix3D0, round3Mix3A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round3Mix3Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round3Mix3Mem2
        simp [round3Mix3C1, round3Mix3D1, round3Mix3A1, round3Mix3B0, round3Mix3C0,
          round3Mix3D0, round3Mix3A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round3Mix3Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round3Mix3Mem3
        simp [round3Mix3D1, round3Mix3A1, round3Mix3B0, round3Mix3C0, round3Mix3D0,
          round3Mix3A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round3Mix3A0, round3Mix3D0, round3Mix3C0, round3Mix3B0, round3Mix3A1,
      round3Mix3D1, round3Mix3C1, round3Mix3B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd2383⟩

/-- Final-flag-`0`, at least four rounds: the fourth round-3 `mixG` call is complete. -/
theorem validPositiveRound3Mix3DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2383⟩
      [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix3Mem3 (round3Mix2ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 19720 := by
  have hprefix := validPositiveRound3Mix3ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix3BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix2ZeroMem I)
    (startGas := 19399)
    (round3Mix2ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the fourth round-3 `mixG` call is complete. -/
theorem validPositiveRound3Mix3DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2383⟩
      [sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3Mix3Mem3 (round3Mix2OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 19747 := by
  have hprefix := validPositiveRound3Mix3ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix3BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3Mix2OneMem I)
    (startGas := 19426)
    (round3Mix2OneMem_size hlen)
    hprefix

end Blake2f
