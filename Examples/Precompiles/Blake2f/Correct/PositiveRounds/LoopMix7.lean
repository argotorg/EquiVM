import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix7Selector

/-!
# BLAKE2F positive-round arbitrary fourth diagonal `mixG`

This file factors the fourth diagonal shared `mixG` body out of the concrete round-6 trace.  It is
parametric in the loop index `i`; the preceding selector supplies `SIGMA[i % 10][14]` and
`SIGMA[i % 10][15]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `3292`, immediately after completing all eight `mixG` calls for loop index `i`. -/
def positiveRoundAfterMix7Stack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [UInt256.ofNat i, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
    ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundAfterMix7Stack_length
    (I : ExecutionEnv) (i : Nat) :
    (positiveRoundAfterMix7Stack I i).length = 8 := by
  simp [positiveRoundAfterMix7Stack]

abbrev positiveRoundMix7V3Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))

abbrev positiveRoundMix7V4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))

abbrev positiveRoundMix7V9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))

abbrev positiveRoundMix7V14Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))

abbrev positiveRoundMix7A0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix7V3Load mem + positiveRoundMix7V4Load mem +
    sigmaMessageArg mem i 14)

abbrev positiveRoundMix7D0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix7V14Load mem) (positiveRoundMix7A0 mem i))
    ⟨32⟩ ⟨32⟩

abbrev positiveRoundMix7C0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix7V9Load mem + positiveRoundMix7D0 mem i)

abbrev positiveRoundMix7B0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix7V4Load mem) (positiveRoundMix7C0 mem i))
    ⟨24⟩ ⟨40⟩

abbrev positiveRoundMix7A1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix7A0 mem i + positiveRoundMix7B0 mem i +
    sigmaMessageArg mem i 15)

abbrev positiveRoundMix7D1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix7D0 mem i) (positiveRoundMix7A1 mem i))
    ⟨16⟩ ⟨48⟩

abbrev positiveRoundMix7C1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix7C0 mem i + positiveRoundMix7D1 mem i)

abbrev positiveRoundMix7B1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix7B0 mem i) (positiveRoundMix7C1 mem i))
    ⟨63⟩ ⟨1⟩

def positiveRoundMix7Mem0 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix7A1 mem i)).write 0 mem
    ((⟨1472⟩ : UInt256) + ⟨96⟩).toNat 32

def positiveRoundMix7Mem1 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix7B1 mem i)).write 0 (positiveRoundMix7Mem0 i mem)
    ((⟨1472⟩ : UInt256) + ⟨128⟩).toNat 32

def positiveRoundMix7Mem2 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix7C1 mem i)).write 0 (positiveRoundMix7Mem1 i mem)
    ((⟨1472⟩ : UInt256) + ⟨288⟩).toNat 32

def positiveRoundMix7Mem3 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix7D1 mem i)).write 0 (positiveRoundMix7Mem2 i mem)
    ((⟨1472⟩ : UInt256) + ⟨448⟩).toNat 32

theorem positiveRoundMix7Mem0_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem0 i mem).size = 1984 := by
  unfold positiveRoundMix7Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem positiveRoundMix7Mem1_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem1 i mem).size = 1984 := by
  unfold positiveRoundMix7Mem1
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix7Mem0_size hmem
  · rw [positiveRoundMix7Mem0_size hmem]
    decide
  · native_decide

theorem positiveRoundMix7Mem2_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem2 i mem).size = 1984 := by
  unfold positiveRoundMix7Mem2
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix7Mem1_size hmem
  · rw [positiveRoundMix7Mem1_size hmem]
    decide
  · native_decide

theorem positiveRoundMix7Mem3_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix7Mem3 i mem).size = 1984 := by
  unfold positiveRoundMix7Mem3
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix7Mem2_size hmem
  · rw [positiveRoundMix7Mem2_size hmem]
    decide
  · native_decide

private theorem positiveRoundMix7Mload1568 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1568⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1568⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32))) =
      positiveRoundMix7V3Load mem := by
  unfold positiveRoundMix7V3Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1568⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix7Mload1600 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1600⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1600⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))) =
      positiveRoundMix7V4Load mem := by
  unfold positiveRoundMix7V4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1600⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix7Mload1760 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1760⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1760⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32))) =
      positiveRoundMix7V9Load mem := by
  unfold positiveRoundMix7V9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1760⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix7Mload1920 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1920⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1920⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32))) =
      positiveRoundMix7V14Load mem := by
  unfold positiveRoundMix7V14Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1920⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

/-- Generic exact trace for the fourth diagonal `mixG` body, from PC `3109` to PC `3292`. -/
theorem positiveRoundMix7BodyFromEntryStackRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨3109⟩
      (positiveRoundMix7EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨3292⟩
      (positiveRoundAfterMix7Stack I i)
      (positiveRoundMix7Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 318) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨3109⟩
      [sigmaMessageArg mem i 15, sigmaMessageArg mem i 14, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩,
        ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundMix7EntryStack] using hprefix
  have hmload1568 := positiveRoundMix7Mload1568 hmem
  have hmload1600 := positiveRoundMix7Mload1600 hmem
  have hmload1760 := positiveRoundMix7Mload1760 hmem
  have hmload1920 := positiveRoundMix7Mload1920 hmem
  have rd3292 := evm_run hprefix' with [
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
    raw mload 0 (positiveRoundMix7V3Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1568
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (positiveRoundMix7V4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1600
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (positiveRoundMix7V9Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (positiveRoundMix7V14Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (positiveRoundMix7Mem0 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix7Mem0
        simp [positiveRoundMix7A1, positiveRoundMix7B0, positiveRoundMix7C0,
          positiveRoundMix7D0, positiveRoundMix7A0, rotr64Bytecode, mask64Bytecode,
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
    raw mstore 0 (positiveRoundMix7Mem1 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix7Mem1
        simp [positiveRoundMix7B1, positiveRoundMix7C1, positiveRoundMix7D1,
          positiveRoundMix7A1, positiveRoundMix7B0, positiveRoundMix7C0,
          positiveRoundMix7D0, positiveRoundMix7A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix7Mem2 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix7Mem2
        simp [positiveRoundMix7C1, positiveRoundMix7D1, positiveRoundMix7A1,
          positiveRoundMix7B0, positiveRoundMix7C0, positiveRoundMix7D0,
          positiveRoundMix7A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix7Mem3 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix7Mem3
        simp [positiveRoundMix7D1, positiveRoundMix7A1, positiveRoundMix7B0,
          positiveRoundMix7C0, positiveRoundMix7D0, positiveRoundMix7A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundAfterMix7Stack, positiveRoundMix7A0, positiveRoundMix7D0,
      positiveRoundMix7C0, positiveRoundMix7B0, positiveRoundMix7A1,
      positiveRoundMix7D1, positiveRoundMix7C1, positiveRoundMix7B1, rotr64Bytecode,
      mask64Bytecode, u64MaskWord, Nat.add_assoc] using rd3292⟩

/-- Context-level wrapper for the generic fourth diagonal `mixG` body. -/
theorem positiveRoundMix7BodyFromEntryStack
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨3109⟩
          (positiveRoundMix7EntryStack ctx.executionEnv i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨3292⟩
            (positiveRoundAfterMix7Stack ctx.executionEnv i)
            (positiveRoundMix7Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 318) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix7BodyFromEntryStackRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
