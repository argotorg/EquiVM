import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix5Selector

/-!
# BLAKE2F positive-round arbitrary second diagonal `mixG`

This file factors the second diagonal shared `mixG` body out of the concrete round-6 trace.  It is
parametric in the loop index `i`; the preceding selector supplies `SIGMA[i % 10][10]` and
`SIGMA[i % 10][11]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `2840`, immediately after completing the second diagonal `mixG` body. -/
def positiveRoundAfterMix5Stack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundAfterMix5Stack_length
    (I : ExecutionEnv) (i : Nat) :
    (positiveRoundAfterMix5Stack I i).length = 11 := by
  simp [positiveRoundAfterMix5Stack]

abbrev positiveRoundMix5V1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))

abbrev positiveRoundMix5V6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))

abbrev positiveRoundMix5V11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))

abbrev positiveRoundMix5V12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))

abbrev positiveRoundMix5A0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix5V1Load mem + positiveRoundMix5V6Load mem +
    sigmaMessageArg mem i 10)

abbrev positiveRoundMix5D0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix5V12Load mem) (positiveRoundMix5A0 mem i))
    ⟨32⟩ ⟨32⟩

abbrev positiveRoundMix5C0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix5V11Load mem + positiveRoundMix5D0 mem i)

abbrev positiveRoundMix5B0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix5V6Load mem) (positiveRoundMix5C0 mem i))
    ⟨24⟩ ⟨40⟩

abbrev positiveRoundMix5A1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix5A0 mem i + positiveRoundMix5B0 mem i +
    sigmaMessageArg mem i 11)

abbrev positiveRoundMix5D1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix5D0 mem i) (positiveRoundMix5A1 mem i))
    ⟨16⟩ ⟨48⟩

abbrev positiveRoundMix5C1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix5C0 mem i + positiveRoundMix5D1 mem i)

abbrev positiveRoundMix5B1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix5B0 mem i) (positiveRoundMix5C1 mem i))
    ⟨63⟩ ⟨1⟩

def positiveRoundMix5Mem0 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix5A1 mem i)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨32⟩).toNat 32

def positiveRoundMix5Mem1 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix5B1 mem i)).write 0 (positiveRoundMix5Mem0 i mem)
    ((⟨1472⟩ : UInt256) + ⟨192⟩).toNat 32

def positiveRoundMix5Mem2 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix5C1 mem i)).write 0 (positiveRoundMix5Mem1 i mem)
    ((⟨1472⟩ : UInt256) + ⟨352⟩).toNat 32

def positiveRoundMix5Mem3 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix5D1 mem i)).write 0 (positiveRoundMix5Mem2 i mem)
    ((⟨1472⟩ : UInt256) + ⟨384⟩).toNat 32

theorem positiveRoundMix5Mem0_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem0 i mem).size = 1984 := by
  unfold positiveRoundMix5Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem positiveRoundMix5Mem1_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem1 i mem).size = 1984 := by
  unfold positiveRoundMix5Mem1
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix5Mem0_size hmem
  · rw [positiveRoundMix5Mem0_size hmem]
    decide
  · native_decide

theorem positiveRoundMix5Mem2_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem2 i mem).size = 1984 := by
  unfold positiveRoundMix5Mem2
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix5Mem1_size hmem
  · rw [positiveRoundMix5Mem1_size hmem]
    decide
  · native_decide

theorem positiveRoundMix5Mem3_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix5Mem3 i mem).size = 1984 := by
  unfold positiveRoundMix5Mem3
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix5Mem2_size hmem
  · rw [positiveRoundMix5Mem2_size hmem]
    decide
  · native_decide

private theorem positiveRoundMix5Mload1504 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1504⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1504⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32))) =
      positiveRoundMix5V1Load mem := by
  unfold positiveRoundMix5V1Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1504⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix5Mload1664 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1664⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1664⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))) =
      positiveRoundMix5V6Load mem := by
  unfold positiveRoundMix5V6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1664⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix5Mload1824 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1824⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1824⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))) =
      positiveRoundMix5V11Load mem := by
  unfold positiveRoundMix5V11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1824⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix5Mload1856 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1856⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1856⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))) =
      positiveRoundMix5V12Load mem := by
  unfold positiveRoundMix5V12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1856⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

/-- Generic exact trace for the second diagonal shared `mixG` body, from PC `2656` to PC `2840`. -/
theorem positiveRoundMix5BodyFromEntryStackRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨2656⟩
      (positiveRoundMix5EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨2840⟩
      (positiveRoundAfterMix5Stack I i)
      (positiveRoundMix5Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 321) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨2656⟩
      [sigmaMessageArg mem i 11, sigmaMessageArg mem i 10, ⟨2840⟩, sigmaPackedWord i,
        ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundMix5EntryStack] using hprefix
  have hmload1504 := positiveRoundMix5Mload1504 hmem
  have hmload1664 := positiveRoundMix5Mload1664 hmem
  have hmload1824 := positiveRoundMix5Mload1824 hmem
  have hmload1856 := positiveRoundMix5Mload1856 hmem
  have rd2840 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨384⟩,
    dup13,
    add,
    push2 ⟨352⟩,
    dup14,
    add,
    dup14,
    push1 ⟨32⟩,
    push1 ⟨192⟩,
    dup3,
    add,
    swap2,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (positiveRoundMix5V1Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1504
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (positiveRoundMix5V6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1664
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (positiveRoundMix5V11Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (positiveRoundMix5V12Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (positiveRoundMix5Mem0 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix5Mem0
        simp [positiveRoundMix5A1, positiveRoundMix5B0, positiveRoundMix5C0,
          positiveRoundMix5D0, positiveRoundMix5A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
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
    raw mstore 0 (positiveRoundMix5Mem1 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix5Mem1
        simp [positiveRoundMix5B1, positiveRoundMix5C1, positiveRoundMix5D1,
          positiveRoundMix5A1, positiveRoundMix5B0, positiveRoundMix5C0,
          positiveRoundMix5D0, positiveRoundMix5A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix5Mem2 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix5Mem2
        simp [positiveRoundMix5C1, positiveRoundMix5D1, positiveRoundMix5A1,
          positiveRoundMix5B0, positiveRoundMix5C0, positiveRoundMix5D0,
          positiveRoundMix5A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix5Mem3 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix5Mem3
        simp [positiveRoundMix5D1, positiveRoundMix5A1, positiveRoundMix5B0,
          positiveRoundMix5C0, positiveRoundMix5D0, positiveRoundMix5A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundAfterMix5Stack, positiveRoundMix5A0, positiveRoundMix5D0,
      positiveRoundMix5C0, positiveRoundMix5B0, positiveRoundMix5A1,
      positiveRoundMix5D1, positiveRoundMix5C1, positiveRoundMix5B1, rotr64Bytecode,
      mask64Bytecode, u64MaskWord, Nat.add_assoc] using rd2840⟩

/-- Context-level wrapper for the generic second diagonal `mixG` body. -/
theorem positiveRoundMix5BodyFromEntryStack
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨2656⟩
          (positiveRoundMix5EntryStack ctx.executionEnv i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨2840⟩
            (positiveRoundAfterMix5Stack ctx.executionEnv i)
            (positiveRoundMix5Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 321) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix5BodyFromEntryStackRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
