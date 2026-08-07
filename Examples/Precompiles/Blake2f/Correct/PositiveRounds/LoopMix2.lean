import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix2Selector

/-!
# BLAKE2F positive-round arbitrary third `mixG`

This file factors the shared third `mixG` body out of the concrete round-6 trace.  It is
parametric in the loop index `i`; the preceding selector supplies `SIGMA[i % 10][4]` and
`SIGMA[i % 10][5]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `2153`, immediately after completing the third `mixG` body. -/
def positiveRoundAfterMix2Stack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundAfterMix2Stack_length
    (I : ExecutionEnv) (i : Nat) :
    (positiveRoundAfterMix2Stack I i).length = 11 := by
  simp [positiveRoundAfterMix2Stack]

abbrev positiveRoundMix2V2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))

abbrev positiveRoundMix2V6Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))

abbrev positiveRoundMix2V10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))

abbrev positiveRoundMix2V14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))

abbrev positiveRoundMix2A0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix2V2Load mem + positiveRoundMix2V6Load mem +
    sigmaMessageArg mem i 4)

abbrev positiveRoundMix2D0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix2V14Load mem) (positiveRoundMix2A0 mem i))
    ⟨32⟩ ⟨32⟩

abbrev positiveRoundMix2C0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix2V10Load mem + positiveRoundMix2D0 mem i)

abbrev positiveRoundMix2B0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix2V6Load mem) (positiveRoundMix2C0 mem i))
    ⟨24⟩ ⟨40⟩

abbrev positiveRoundMix2A1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix2A0 mem i + positiveRoundMix2B0 mem i +
    sigmaMessageArg mem i 5)

abbrev positiveRoundMix2D1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix2D0 mem i) (positiveRoundMix2A1 mem i))
    ⟨16⟩ ⟨48⟩

abbrev positiveRoundMix2C1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix2C0 mem i + positiveRoundMix2D1 mem i)

abbrev positiveRoundMix2B1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix2B0 mem i) (positiveRoundMix2C1 mem i))
    ⟨63⟩ ⟨1⟩

def positiveRoundMix2Mem0 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix2A1 mem i)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨64⟩).toNat 32

def positiveRoundMix2Mem1 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix2B1 mem i)).write 0 (positiveRoundMix2Mem0 i mem)
    ((⟨1472⟩ : UInt256) + ⟨192⟩).toNat 32

def positiveRoundMix2Mem2 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix2C1 mem i)).write 0 (positiveRoundMix2Mem1 i mem)
    ((⟨1472⟩ : UInt256) + ⟨320⟩).toNat 32

def positiveRoundMix2Mem3 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix2D1 mem i)).write 0 (positiveRoundMix2Mem2 i mem)
    ((⟨1472⟩ : UInt256) + ⟨448⟩).toNat 32

theorem positiveRoundMix2Mem0_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem0 i mem).size = 1984 := by
  unfold positiveRoundMix2Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem positiveRoundMix2Mem1_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem1 i mem).size = 1984 := by
  unfold positiveRoundMix2Mem1
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix2Mem0_size hmem
  · rw [positiveRoundMix2Mem0_size hmem]
    decide
  · native_decide

theorem positiveRoundMix2Mem2_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem2 i mem).size = 1984 := by
  unfold positiveRoundMix2Mem2
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix2Mem1_size hmem
  · rw [positiveRoundMix2Mem1_size hmem]
    decide
  · native_decide

theorem positiveRoundMix2Mem3_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix2Mem3 i mem).size = 1984 := by
  unfold positiveRoundMix2Mem3
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix2Mem2_size hmem
  · rw [positiveRoundMix2Mem2_size hmem]
    decide
  · native_decide

private theorem positiveRoundMix2Mload1536 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1536⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1536⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))) =
      positiveRoundMix2V2Load mem := by
  unfold positiveRoundMix2V2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1536⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix2Mload1664 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1664⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1664⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32))) =
      positiveRoundMix2V6Load mem := by
  unfold positiveRoundMix2V6Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1664⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix2Mload1792 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1792⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1792⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))) =
      positiveRoundMix2V10Load mem := by
  unfold positiveRoundMix2V10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1792⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix2Mload1920 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1920⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1920⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))) =
      positiveRoundMix2V14Load mem := by
  unfold positiveRoundMix2V14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1920⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

/-- Generic exact trace for the shared third `mixG` body, from PC `1969` to PC `2153`. -/
theorem positiveRoundMix2BodyFromEntryStackRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨1969⟩
      (positiveRoundMix2EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨2153⟩
      (positiveRoundAfterMix2Stack I i)
      (positiveRoundMix2Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 321) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1969⟩
      [sigmaMessageArg mem i 5, sigmaMessageArg mem i 4, ⟨2153⟩, sigmaPackedWord i,
        ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundMix2EntryStack] using hprefix
  have hmload1536 := positiveRoundMix2Mload1536 hmem
  have hmload1664 := positiveRoundMix2Mload1664 hmem
  have hmload1792 := positiveRoundMix2Mload1792 hmem
  have hmload1920 := positiveRoundMix2Mload1920 hmem
  have rd2153 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨448⟩,
    dup13,
    add,
    push2 ⟨320⟩,
    dup14,
    add,
    dup14,
    push1 ⟨64⟩,
    push1 ⟨192⟩,
    dup3,
    add,
    swap2,
    add,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (positiveRoundMix2V2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1536
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (positiveRoundMix2V6Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1664
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (positiveRoundMix2V10Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (positiveRoundMix2V14Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (positiveRoundMix2Mem0 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix2Mem0
        simp [positiveRoundMix2A1, positiveRoundMix2B0, positiveRoundMix2C0,
          positiveRoundMix2D0, positiveRoundMix2A0, rotr64Bytecode, mask64Bytecode,
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
    raw mstore 0 (positiveRoundMix2Mem1 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix2Mem1
        simp [positiveRoundMix2B1, positiveRoundMix2C1, positiveRoundMix2D1,
          positiveRoundMix2A1, positiveRoundMix2B0, positiveRoundMix2C0,
          positiveRoundMix2D0, positiveRoundMix2A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix2Mem2 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix2Mem2
        simp [positiveRoundMix2C1, positiveRoundMix2D1, positiveRoundMix2A1,
          positiveRoundMix2B0, positiveRoundMix2C0, positiveRoundMix2D0,
          positiveRoundMix2A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix2Mem3 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix2Mem3
        simp [positiveRoundMix2D1, positiveRoundMix2A1, positiveRoundMix2B0,
          positiveRoundMix2C0, positiveRoundMix2D0, positiveRoundMix2A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundAfterMix2Stack, positiveRoundMix2A0, positiveRoundMix2D0,
      positiveRoundMix2C0, positiveRoundMix2B0, positiveRoundMix2A1,
      positiveRoundMix2D1, positiveRoundMix2C1, positiveRoundMix2B1, rotr64Bytecode,
      mask64Bytecode, u64MaskWord, Nat.add_assoc] using rd2153⟩

/-- Context-level wrapper for the generic third `mixG` body. -/
theorem positiveRoundMix2BodyFromEntryStack
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨1969⟩
          (positiveRoundMix2EntryStack ctx.executionEnv i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨2153⟩
            (positiveRoundAfterMix2Stack ctx.executionEnv i)
            (positiveRoundMix2Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 321) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix2BodyFromEntryStackRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
