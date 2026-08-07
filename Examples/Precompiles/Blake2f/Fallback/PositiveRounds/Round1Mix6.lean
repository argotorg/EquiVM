import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix6Selector

/-!
# BLAKE2F fallback positive-round traces: round-1 third diagonal `mixG`

This module continues the multi-round path from PC `2886`, the third diagonal `mixG` routine for
round-1 vector slots `v[2]`, `v[7]`, `v[8]`, and `v[13]`, using message words `m[11]` and
`m[7]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round1Mix6V2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))

abbrev round1Mix6V7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))

abbrev round1Mix6V8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))

abbrev round1Mix6V13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))

abbrev round1Mix6A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix6V2Load mem + round1Mix6V7Load mem + round1M11Arg mem)

abbrev round1Mix6D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix6V13Load mem) (round1Mix6A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round1Mix6C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix6V8Load mem + round1Mix6D0 mem)

abbrev round1Mix6B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix6V7Load mem) (round1Mix6C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round1Mix6A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix6A0 mem + round1Mix6B0 mem + round1M7Arg mem)

abbrev round1Mix6D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix6D0 mem) (round1Mix6A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round1Mix6C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix6C0 mem + round1Mix6D1 mem)

abbrev round1Mix6B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix6B0 mem) (round1Mix6C1 mem)) ⟨63⟩ ⟨1⟩

def round1Mix6Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix6A1 mem)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨64⟩).toNat 32

def round1Mix6Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix6B1 mem)).write 0 (round1Mix6Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨224⟩).toNat 32

def round1Mix6Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix6C1 mem)).write 0 (round1Mix6Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨256⟩).toNat 32

def round1Mix6Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix6D1 mem)).write 0 (round1Mix6Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨416⟩).toNat 32

theorem round1Mix6Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix6Mem0 mem).size = 1984 := by
  unfold round1Mix6Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round1Mix6Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix6Mem1 mem).size = 1984 := by
  unfold round1Mix6Mem1
  apply toByteArray_write32_size_of_le
  · exact round1Mix6Mem0_size hmem
  · rw [round1Mix6Mem0_size hmem]
    decide
  · native_decide

theorem round1Mix6Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix6Mem2 mem).size = 1984 := by
  unfold round1Mix6Mem2
  apply toByteArray_write32_size_of_le
  · exact round1Mix6Mem1_size hmem
  · rw [round1Mix6Mem1_size hmem]
    decide
  · native_decide

theorem round1Mix6Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix6Mem3 mem).size = 1984 := by
  unfold round1Mix6Mem3
  apply toByteArray_write32_size_of_le
  · exact round1Mix6Mem2_size hmem
  · rw [round1Mix6Mem2_size hmem]
    decide
  · native_decide

private theorem round1Mix6Mload1536 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1536⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1536⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))) =
      round1Mix6V2Load mem := by
  unfold round1Mix6V2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1536⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix6Mload1696 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1696⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1696⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))) =
      round1Mix6V7Load mem := by
  unfold round1Mix6V7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1696⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix6Mload1728 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1728⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1728⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))) =
      round1Mix6V8Load mem := by
  unfold round1Mix6V8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1728⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix6Mload1888 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1888⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1888⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))) =
      round1Mix6V13Load mem := by
  unfold round1Mix6V13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1888⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix6BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2886⟩
        [round1M7Arg mem, round1M11Arg mem, ⟨3070⟩, sigmaRound1Word,
          ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3070⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix6Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 321) := by
  obtain ⟨k0, rd2886⟩ := hprefix
  have hmload1536 := round1Mix6Mload1536 hmem
  have hmload1696 := round1Mix6Mload1696 hmem
  have hmload1728 := round1Mix6Mload1728 hmem
  have hmload1888 := round1Mix6Mload1888 hmem
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
    raw mload 0 (round1Mix6V2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1536
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round1Mix6V7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1696
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round1Mix6V8Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (round1Mix6V13Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (round1Mix6Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix6Mem0
        simp [round1Mix6A1, round1Mix6B0, round1Mix6C0, round1Mix6D0, round1Mix6A0,
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
    raw mstore 0 (round1Mix6Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix6Mem1
        simp [round1Mix6B1, round1Mix6C1, round1Mix6D1, round1Mix6A1, round1Mix6B0,
          round1Mix6C0, round1Mix6D0, round1Mix6A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix6Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix6Mem2
        simp [round1Mix6C1, round1Mix6D1, round1Mix6A1, round1Mix6B0, round1Mix6C0,
          round1Mix6D0, round1Mix6A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix6Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix6Mem3
        simp [round1Mix6D1, round1Mix6A1, round1Mix6B0, round1Mix6C0, round1Mix6D0,
          round1Mix6A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round1Mix6A0, round1Mix6D0, round1Mix6C0, round1Mix6B0, round1Mix6A1,
      round1Mix6D1, round1Mix6C1, round1Mix6B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd3070⟩

/-- Final-flag-`0`, at least two rounds: the third diagonal round-1 `mixG` call is complete. -/
theorem validPositiveRound1Mix6DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3070⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix6Mem3 (round1Mix5ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k ((((13216 + 93) + 321) + 93) + 321) := by
  have hprefix := validPositiveRound1Mix6ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix6BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix5ZeroMem I)
    (startGas := ((13216 + 93) + 321) + 93)
    (round1Mix5ZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least two rounds: the third diagonal round-1 `mixG` call is complete. -/
theorem validPositiveRound1Mix6DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3070⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix6Mem3 (round1Mix5OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k ((((13243 + 93) + 321) + 93) + 321) := by
  have hprefix := validPositiveRound1Mix6ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1Mix6BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix5OneMem I)
    (startGas := ((13243 + 93) + 321) + 93)
    (round1Mix5OneMem_size hlen)
    hprefix

end Blake2f
