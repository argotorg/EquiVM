import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix7Selector
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.ProofSupportExact

/-!
# BLAKE2F fallback positive-round traces: round-1 fourth diagonal `mixG`

This module continues the multi-round path from PC `3109`, the last diagonal `mixG` routine for
round-1 vector slots `v[3]`, `v[4]`, `v[9]`, and `v[14]`, using message words `m[5]` and
`m[3]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round1Mix7V3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))

abbrev round1Mix7V4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))

abbrev round1Mix7V9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))

abbrev round1Mix7V14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))

abbrev round1Mix7A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix7V3Load mem + round1Mix7V4Load mem + round1M5Arg mem)

abbrev round1Mix7D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix7V14Load mem) (round1Mix7A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round1Mix7C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix7V9Load mem + round1Mix7D0 mem)

abbrev round1Mix7B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix7V4Load mem) (round1Mix7C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round1Mix7A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix7A0 mem + round1Mix7B0 mem + round1M3Arg mem)

abbrev round1Mix7D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix7D0 mem) (round1Mix7A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round1Mix7C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix7C0 mem + round1Mix7D1 mem)

abbrev round1Mix7B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix7B0 mem) (round1Mix7C1 mem)) ⟨63⟩ ⟨1⟩

def round1Mix7Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix7A1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨96⟩).toNat 32

def round1Mix7Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix7B1 mem)).write 0 (round1Mix7Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨128⟩).toNat 32

def round1Mix7Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix7C1 mem)).write 0 (round1Mix7Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨288⟩).toNat 32

def round1Mix7Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix7D1 mem)).write 0 (round1Mix7Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨448⟩).toNat 32

theorem round1Mix7Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix7Mem0 mem).size = 1984 := by
  unfold round1Mix7Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round1Mix7Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix7Mem1 mem).size = 1984 := by
  unfold round1Mix7Mem1
  apply toByteArray_write32_size_of_le
  · exact round1Mix7Mem0_size hmem
  · rw [round1Mix7Mem0_size hmem]
    decide
  · native_decide

theorem round1Mix7Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix7Mem2 mem).size = 1984 := by
  unfold round1Mix7Mem2
  apply toByteArray_write32_size_of_le
  · exact round1Mix7Mem1_size hmem
  · rw [round1Mix7Mem1_size hmem]
    decide
  · native_decide

theorem round1Mix7Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix7Mem3 mem).size = 1984 := by
  unfold round1Mix7Mem3
  apply toByteArray_write32_size_of_le
  · exact round1Mix7Mem2_size hmem
  · rw [round1Mix7Mem2_size hmem]
    decide
  · native_decide

private theorem round1Mix7Mload1568 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1568⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1568⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))) =
      round1Mix7V3Load mem := by
  unfold round1Mix7V3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1568⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix7Mload1600 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1600⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1600⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))) =
      round1Mix7V4Load mem := by
  unfold round1Mix7V4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1600⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix7Mload1760 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1760⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1760⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))) =
      round1Mix7V9Load mem := by
  unfold round1Mix7V9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1760⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix7Mload1920 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1920⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1920⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))) =
      round1Mix7V14Load mem := by
  unfold round1Mix7V14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1920⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix7BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3109⟩
        [round1M3Arg mem, round1M5Arg mem, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3292⟩
      [⟨1⟩, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix7Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 318) := by
  obtain ⟨k0, rd3109⟩ := hprefix
  have hmload1568 := round1Mix7Mload1568 hmem
  have hmload1600 := round1Mix7Mload1600 hmem
  have hmload1760 := round1Mix7Mload1760 hmem
  have hmload1920 := round1Mix7Mload1920 hmem
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
    raw mload 0 (round1Mix7V3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1568
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round1Mix7V4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1600
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round1Mix7V9Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (round1Mix7V14Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (round1Mix7Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix7Mem0
        simp [round1Mix7A1, round1Mix7B0, round1Mix7C0, round1Mix7D0, round1Mix7A0,
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
    raw mstore 0 (round1Mix7Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix7Mem1
        simp [round1Mix7B1, round1Mix7C1, round1Mix7D1, round1Mix7A1, round1Mix7B0,
          round1Mix7C0, round1Mix7D0, round1Mix7A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix7Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix7Mem2
        simp [round1Mix7C1, round1Mix7D1, round1Mix7A1, round1Mix7B0, round1Mix7C0,
          round1Mix7D0, round1Mix7A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix7Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix7Mem3
        simp [round1Mix7D1, round1Mix7A1, round1Mix7B0, round1Mix7C0, round1Mix7D0,
          round1Mix7A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round1Mix7A0, round1Mix7D0, round1Mix7C0, round1Mix7B0, round1Mix7A1,
      round1Mix7D1, round1Mix7C1, round1Mix7B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd3292⟩

/-- Final-flag-`0`, at least two rounds: all eight round-1 `mixG` calls are complete. -/
theorem validPositiveRound1Mix7DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3292⟩
      [⟨1⟩, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix7Mem3 (round1Mix6ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k ((((((13216 + 93) + 321) + 93) + 321) + 84) + 318) := by
  have hprefix := validPositiveRound1Mix7ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix7BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix6ZeroMem I)
    (startGas := (((((13216 + 93) + 321) + 93) + 321) + 84))
    (round1Mix6ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least two rounds: all eight round-1 `mixG` calls are complete. -/
theorem validPositiveRound1Mix7DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3292⟩
      [⟨1⟩, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix7Mem3 (round1Mix6OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k ((((((13243 + 93) + 321) + 93) + 321) + 84) + 318) := by
  have hprefix := validPositiveRound1Mix7ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix7BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix6OneMem I)
    (startGas := (((((13243 + 93) + 321) + 93) + 321) + 84))
    (round1Mix6OneMem_size hlen)
    hprefix

end Blake2f
