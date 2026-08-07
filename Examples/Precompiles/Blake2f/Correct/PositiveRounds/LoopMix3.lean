import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix3Selector

/-!
# BLAKE2F positive-round arbitrary fourth `mixG`

This file factors the shared fourth `mixG` body out of the concrete round-6 trace.  It is
parametric in the loop index `i`; the preceding selector supplies `SIGMA[i % 10][6]` and
`SIGMA[i % 10][7]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `2383`, immediately after completing the fourth `mixG` body. -/
def positiveRoundAfterMix3Stack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundAfterMix3Stack_length
    (I : ExecutionEnv) (i : Nat) :
    (positiveRoundAfterMix3Stack I i).length = 11 := by
  simp [positiveRoundAfterMix3Stack]

abbrev positiveRoundMix3V3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))

abbrev positiveRoundMix3V7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))

abbrev positiveRoundMix3V11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))

abbrev positiveRoundMix3V15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev positiveRoundMix3A0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix3V3Load mem + positiveRoundMix3V7Load mem +
    sigmaMessageArg mem i 6)

abbrev positiveRoundMix3D0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix3V15Load mem) (positiveRoundMix3A0 mem i))
    ⟨32⟩ ⟨32⟩

abbrev positiveRoundMix3C0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix3V11Load mem + positiveRoundMix3D0 mem i)

abbrev positiveRoundMix3B0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix3V7Load mem) (positiveRoundMix3C0 mem i))
    ⟨24⟩ ⟨40⟩

abbrev positiveRoundMix3A1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix3A0 mem i + positiveRoundMix3B0 mem i +
    sigmaMessageArg mem i 7)

abbrev positiveRoundMix3D1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix3D0 mem i) (positiveRoundMix3A1 mem i))
    ⟨16⟩ ⟨48⟩

abbrev positiveRoundMix3C1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix3C0 mem i + positiveRoundMix3D1 mem i)

abbrev positiveRoundMix3B1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix3B0 mem i) (positiveRoundMix3C1 mem i))
    ⟨63⟩ ⟨1⟩

def positiveRoundMix3Mem0 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix3A1 mem i)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨96⟩).toNat 32

def positiveRoundMix3Mem1 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix3B1 mem i)).write 0 (positiveRoundMix3Mem0 i mem)
    ((⟨1472⟩ : UInt256) + ⟨224⟩).toNat 32

def positiveRoundMix3Mem2 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix3C1 mem i)).write 0 (positiveRoundMix3Mem1 i mem)
    ((⟨1472⟩ : UInt256) + ⟨352⟩).toNat 32

def positiveRoundMix3Mem3 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix3D1 mem i)).write 0 (positiveRoundMix3Mem2 i mem)
    ((⟨1472⟩ : UInt256) + ⟨480⟩).toNat 32

theorem positiveRoundMix3Mem0_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem0 i mem).size = 1984 := by
  unfold positiveRoundMix3Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem positiveRoundMix3Mem1_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem1 i mem).size = 1984 := by
  unfold positiveRoundMix3Mem1
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix3Mem0_size hmem
  · rw [positiveRoundMix3Mem0_size hmem]
    decide
  · native_decide

theorem positiveRoundMix3Mem2_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem2 i mem).size = 1984 := by
  unfold positiveRoundMix3Mem2
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix3Mem1_size hmem
  · rw [positiveRoundMix3Mem1_size hmem]
    decide
  · native_decide

theorem positiveRoundMix3Mem3_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix3Mem3 i mem).size = 1984 := by
  unfold positiveRoundMix3Mem3
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix3Mem2_size hmem
  · rw [positiveRoundMix3Mem2_size hmem]
    decide
  · native_decide

private theorem positiveRoundMix3Mload1568 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1568⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1568⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))) =
      positiveRoundMix3V3Load mem := by
  unfold positiveRoundMix3V3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1568⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix3Mload1696 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1696⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1696⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32))) =
      positiveRoundMix3V7Load mem := by
  unfold positiveRoundMix3V7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1696⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix3Mload1824 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1824⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1824⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32))) =
      positiveRoundMix3V11Load mem := by
  unfold positiveRoundMix3V11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1824⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix3Mload1952 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
      positiveRoundMix3V15Load mem := by
  unfold positiveRoundMix3V15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

/-- Generic exact trace for the shared fourth `mixG` body, from PC `2199` to PC `2383`. -/
theorem positiveRoundMix3BodyFromEntryStackRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨2199⟩
      (positiveRoundMix3EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨2383⟩
      (positiveRoundAfterMix3Stack I i)
      (positiveRoundMix3Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 321) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨2199⟩
      [sigmaMessageArg mem i 7, sigmaMessageArg mem i 6, ⟨2383⟩, sigmaPackedWord i,
        ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundMix3EntryStack] using hprefix
  have hmload1568 := positiveRoundMix3Mload1568 hmem
  have hmload1696 := positiveRoundMix3Mload1696 hmem
  have hmload1824 := positiveRoundMix3Mload1824 hmem
  have hmload1952 := positiveRoundMix3Mload1952 hmem
  have rd2383 := evm_run hprefix' with [
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
    raw mload 0 (positiveRoundMix3V3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1568
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (positiveRoundMix3V7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1696
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (positiveRoundMix3V11Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (positiveRoundMix3V15Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (positiveRoundMix3Mem0 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix3Mem0
        simp [positiveRoundMix3A1, positiveRoundMix3B0, positiveRoundMix3C0,
          positiveRoundMix3D0, positiveRoundMix3A0, rotr64Bytecode, mask64Bytecode,
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
    raw mstore 0 (positiveRoundMix3Mem1 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix3Mem1
        simp [positiveRoundMix3B1, positiveRoundMix3C1, positiveRoundMix3D1,
          positiveRoundMix3A1, positiveRoundMix3B0, positiveRoundMix3C0,
          positiveRoundMix3D0, positiveRoundMix3A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix3Mem2 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix3Mem2
        simp [positiveRoundMix3C1, positiveRoundMix3D1, positiveRoundMix3A1,
          positiveRoundMix3B0, positiveRoundMix3C0, positiveRoundMix3D0,
          positiveRoundMix3A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix3Mem3 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix3Mem3
        simp [positiveRoundMix3D1, positiveRoundMix3A1, positiveRoundMix3B0,
          positiveRoundMix3C0, positiveRoundMix3D0, positiveRoundMix3A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundAfterMix3Stack, positiveRoundMix3A0, positiveRoundMix3D0,
      positiveRoundMix3C0, positiveRoundMix3B0, positiveRoundMix3A1,
      positiveRoundMix3D1, positiveRoundMix3C1, positiveRoundMix3B1, rotr64Bytecode,
      mask64Bytecode, u64MaskWord, Nat.add_assoc] using rd2383⟩

/-- Context-level wrapper for the generic fourth `mixG` body. -/
theorem positiveRoundMix3BodyFromEntryStack
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨2199⟩
          (positiveRoundMix3EntryStack ctx.executionEnv i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨2383⟩
            (positiveRoundAfterMix3Stack ctx.executionEnv i)
            (positiveRoundMix3Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 321) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix3BodyFromEntryStackRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
