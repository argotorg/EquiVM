import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix6Selector

/-!
# BLAKE2F positive-round arbitrary third diagonal `mixG`

This file factors the third diagonal shared `mixG` body out of the concrete round-6 trace.  It is
parametric in the loop index `i`; the preceding selector supplies `SIGMA[i % 10][12]` and
`SIGMA[i % 10][13]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `3070`, immediately after completing the third diagonal `mixG` body. -/
def positiveRoundAfterMix6Stack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundAfterMix6Stack_length
    (I : ExecutionEnv) (i : Nat) :
    (positiveRoundAfterMix6Stack I i).length = 11 := by
  simp [positiveRoundAfterMix6Stack]

abbrev positiveRoundMix6V2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))

abbrev positiveRoundMix6V7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))

abbrev positiveRoundMix6V8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))

abbrev positiveRoundMix6V13Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))

abbrev positiveRoundMix6A0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix6V2Load mem + positiveRoundMix6V7Load mem +
    sigmaMessageArg mem i 12)

abbrev positiveRoundMix6D0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix6V13Load mem) (positiveRoundMix6A0 mem i))
    ⟨32⟩ ⟨32⟩

abbrev positiveRoundMix6C0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix6V8Load mem + positiveRoundMix6D0 mem i)

abbrev positiveRoundMix6B0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix6V7Load mem) (positiveRoundMix6C0 mem i))
    ⟨24⟩ ⟨40⟩

abbrev positiveRoundMix6A1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix6A0 mem i + positiveRoundMix6B0 mem i +
    sigmaMessageArg mem i 13)

abbrev positiveRoundMix6D1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix6D0 mem i) (positiveRoundMix6A1 mem i))
    ⟨16⟩ ⟨48⟩

abbrev positiveRoundMix6C1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix6C0 mem i + positiveRoundMix6D1 mem i)

abbrev positiveRoundMix6B1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix6B0 mem i) (positiveRoundMix6C1 mem i))
    ⟨63⟩ ⟨1⟩

def positiveRoundMix6Mem0 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix6A1 mem i)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨64⟩).toNat 32

def positiveRoundMix6Mem1 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix6B1 mem i)).write 0 (positiveRoundMix6Mem0 i mem)
    ((⟨1472⟩ : UInt256) + ⟨224⟩).toNat 32

def positiveRoundMix6Mem2 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix6C1 mem i)).write 0 (positiveRoundMix6Mem1 i mem)
    ((⟨1472⟩ : UInt256) + ⟨256⟩).toNat 32

def positiveRoundMix6Mem3 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix6D1 mem i)).write 0 (positiveRoundMix6Mem2 i mem)
    ((⟨1472⟩ : UInt256) + ⟨416⟩).toNat 32

theorem positiveRoundMix6Mem0_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem0 i mem).size = 1984 := by
  unfold positiveRoundMix6Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem positiveRoundMix6Mem1_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem1 i mem).size = 1984 := by
  unfold positiveRoundMix6Mem1
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix6Mem0_size hmem
  · rw [positiveRoundMix6Mem0_size hmem]
    decide
  · native_decide

theorem positiveRoundMix6Mem2_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem2 i mem).size = 1984 := by
  unfold positiveRoundMix6Mem2
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix6Mem1_size hmem
  · rw [positiveRoundMix6Mem1_size hmem]
    decide
  · native_decide

theorem positiveRoundMix6Mem3_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix6Mem3 i mem).size = 1984 := by
  unfold positiveRoundMix6Mem3
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix6Mem2_size hmem
  · rw [positiveRoundMix6Mem2_size hmem]
    decide
  · native_decide

private theorem positiveRoundMix6Mload1536 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1536⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1536⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32))) =
      positiveRoundMix6V2Load mem := by
  unfold positiveRoundMix6V2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1536⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix6Mload1696 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1696⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1696⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))) =
      positiveRoundMix6V7Load mem := by
  unfold positiveRoundMix6V7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1696⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix6Mload1728 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1728⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1728⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))) =
      positiveRoundMix6V8Load mem := by
  unfold positiveRoundMix6V8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1728⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix6Mload1888 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1888⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1888⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32))) =
      positiveRoundMix6V13Load mem := by
  unfold positiveRoundMix6V13Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1888⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

/-- Generic exact trace for the third diagonal shared `mixG` body, from PC `2886` to PC `3070`. -/
theorem positiveRoundMix6BodyFromEntryStackRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨2886⟩
      (positiveRoundMix6EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨3070⟩
      (positiveRoundAfterMix6Stack I i)
      (positiveRoundMix6Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 321) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨2886⟩
      [sigmaMessageArg mem i 13, sigmaMessageArg mem i 12, ⟨3070⟩, sigmaPackedWord i,
        ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundMix6EntryStack] using hprefix
  have hmload1536 := positiveRoundMix6Mload1536 hmem
  have hmload1696 := positiveRoundMix6Mload1696 hmem
  have hmload1728 := positiveRoundMix6Mload1728 hmem
  have hmload1888 := positiveRoundMix6Mload1888 hmem
  have rd3070 := evm_run hprefix' with [
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
    raw mload 0 (positiveRoundMix6V2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1536
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (positiveRoundMix6V7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1696
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (positiveRoundMix6V8Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (positiveRoundMix6V13Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (positiveRoundMix6Mem0 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix6Mem0
        simp [positiveRoundMix6A1, positiveRoundMix6B0, positiveRoundMix6C0,
          positiveRoundMix6D0, positiveRoundMix6A0, rotr64Bytecode, mask64Bytecode,
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
    raw mstore 0 (positiveRoundMix6Mem1 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix6Mem1
        simp [positiveRoundMix6B1, positiveRoundMix6C1, positiveRoundMix6D1,
          positiveRoundMix6A1, positiveRoundMix6B0, positiveRoundMix6C0,
          positiveRoundMix6D0, positiveRoundMix6A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix6Mem2 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix6Mem2
        simp [positiveRoundMix6C1, positiveRoundMix6D1, positiveRoundMix6A1,
          positiveRoundMix6B0, positiveRoundMix6C0, positiveRoundMix6D0,
          positiveRoundMix6A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix6Mem3 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix6Mem3
        simp [positiveRoundMix6D1, positiveRoundMix6A1, positiveRoundMix6B0,
          positiveRoundMix6C0, positiveRoundMix6D0, positiveRoundMix6A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundAfterMix6Stack, positiveRoundMix6A0, positiveRoundMix6D0,
      positiveRoundMix6C0, positiveRoundMix6B0, positiveRoundMix6A1,
      positiveRoundMix6D1, positiveRoundMix6C1, positiveRoundMix6B1, rotr64Bytecode,
      mask64Bytecode, u64MaskWord, Nat.add_assoc] using rd3070⟩

/-- Context-level wrapper for the generic third diagonal `mixG` body. -/
theorem positiveRoundMix6BodyFromEntryStack
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨2886⟩
          (positiveRoundMix6EntryStack ctx.executionEnv i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨3070⟩
            (positiveRoundAfterMix6Stack ctx.executionEnv i)
            (positiveRoundMix6Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 321) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix6BodyFromEntryStackRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
