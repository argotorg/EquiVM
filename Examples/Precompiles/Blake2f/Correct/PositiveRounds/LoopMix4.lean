import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix4Selector

/-!
# BLAKE2F positive-round arbitrary first diagonal `mixG`

This file factors the first diagonal shared `mixG` body out of the concrete round-6 trace.  It is
parametric in the loop index `i`; the preceding selector supplies `SIGMA[i % 10][8]` and
`SIGMA[i % 10][9]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `2610`, immediately after completing the first diagonal `mixG` body. -/
def positiveRoundAfterMix4Stack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
    UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundAfterMix4Stack_length
    (I : ExecutionEnv) (i : Nat) :
    (positiveRoundAfterMix4Stack I i).length = 11 := by
  simp [positiveRoundAfterMix4Stack]

abbrev positiveRoundMix4V0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev positiveRoundMix4V5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev positiveRoundMix4V10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))

abbrev positiveRoundMix4V15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev positiveRoundMix4A0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix4V0Load mem + positiveRoundMix4V5Load mem +
    sigmaMessageArg mem i 8)

abbrev positiveRoundMix4D0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix4V15Load mem) (positiveRoundMix4A0 mem i))
    ⟨32⟩ ⟨32⟩

abbrev positiveRoundMix4C0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix4V10Load mem + positiveRoundMix4D0 mem i)

abbrev positiveRoundMix4B0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix4V5Load mem) (positiveRoundMix4C0 mem i))
    ⟨24⟩ ⟨40⟩

abbrev positiveRoundMix4A1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix4A0 mem i + positiveRoundMix4B0 mem i +
    sigmaMessageArg mem i 9)

abbrev positiveRoundMix4D1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix4D0 mem i) (positiveRoundMix4A1 mem i))
    ⟨16⟩ ⟨48⟩

abbrev positiveRoundMix4C1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix4C0 mem i + positiveRoundMix4D1 mem i)

abbrev positiveRoundMix4B1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix4B0 mem i) (positiveRoundMix4C1 mem i))
    ⟨63⟩ ⟨1⟩

def positiveRoundMix4Mem0 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix4A1 mem i)).write 0 mem
    (⟨1472⟩ : UInt256).toNat 32

def positiveRoundMix4Mem1 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix4B1 mem i)).write 0 (positiveRoundMix4Mem0 i mem)
    ((⟨1472⟩ : UInt256) + ⟨160⟩).toNat 32

def positiveRoundMix4Mem2 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix4C1 mem i)).write 0 (positiveRoundMix4Mem1 i mem)
    ((⟨1472⟩ : UInt256) + ⟨320⟩).toNat 32

def positiveRoundMix4Mem3 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix4D1 mem i)).write 0 (positiveRoundMix4Mem2 i mem)
    ((⟨1472⟩ : UInt256) + ⟨480⟩).toNat 32

theorem positiveRoundMix4Mem0_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem0 i mem).size = 1984 := by
  unfold positiveRoundMix4Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem positiveRoundMix4Mem1_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem1 i mem).size = 1984 := by
  unfold positiveRoundMix4Mem1
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix4Mem0_size hmem
  · rw [positiveRoundMix4Mem0_size hmem]
    decide
  · native_decide

theorem positiveRoundMix4Mem2_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem2 i mem).size = 1984 := by
  unfold positiveRoundMix4Mem2
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix4Mem1_size hmem
  · rw [positiveRoundMix4Mem1_size hmem]
    decide
  · native_decide

theorem positiveRoundMix4Mem3_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix4Mem3 i mem).size = 1984 := by
  unfold positiveRoundMix4Mem3
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix4Mem2_size hmem
  · rw [positiveRoundMix4Mem2_size hmem]
    decide
  · native_decide

private theorem positiveRoundMix4Mload1472 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
      positiveRoundMix4V0Load mem := by
  unfold positiveRoundMix4V0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix4Mload1632 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1632⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1632⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))) =
      positiveRoundMix4V5Load mem := by
  unfold positiveRoundMix4V5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1632⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix4Mload1792 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1792⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1792⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))) =
      positiveRoundMix4V10Load mem := by
  unfold positiveRoundMix4V10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1792⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix4Mload1952 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
      positiveRoundMix4V15Load mem := by
  unfold positiveRoundMix4V15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

/-- Generic exact trace for the first diagonal shared `mixG` body, from PC `2429` to PC `2610`. -/
theorem positiveRoundMix4BodyFromEntryStackRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨2429⟩
      (positiveRoundMix4EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨2610⟩
      (positiveRoundAfterMix4Stack I i)
      (positiveRoundMix4Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 315) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨2429⟩
      [sigmaMessageArg mem i 9, sigmaMessageArg mem i 8, ⟨2610⟩, sigmaPackedWord i,
        ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundMix4EntryStack] using hprefix
  have hmload1472 := positiveRoundMix4Mload1472 hmem
  have hmload1632 := positiveRoundMix4Mload1632 hmem
  have hmload1792 := positiveRoundMix4Mload1792 hmem
  have hmload1952 := positiveRoundMix4Mload1952 hmem
  have rd2610 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨480⟩,
    dup13,
    add,
    push2 ⟨320⟩,
    dup14,
    add,
    dup14,
    push1 ⟨160⟩,
    dup2,
    add,
    swap1,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (positiveRoundMix4V0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (positiveRoundMix4V5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1632
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (positiveRoundMix4V10Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (positiveRoundMix4V15Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (positiveRoundMix4Mem0 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix4Mem0
        simp [positiveRoundMix4A1, positiveRoundMix4B0, positiveRoundMix4C0,
          positiveRoundMix4D0, positiveRoundMix4A0, rotr64Bytecode, mask64Bytecode,
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
    raw mstore 0 (positiveRoundMix4Mem1 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix4Mem1
        simp [positiveRoundMix4B1, positiveRoundMix4C1, positiveRoundMix4D1,
          positiveRoundMix4A1, positiveRoundMix4B0, positiveRoundMix4C0,
          positiveRoundMix4D0, positiveRoundMix4A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix4Mem2 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix4Mem2
        simp [positiveRoundMix4C1, positiveRoundMix4D1, positiveRoundMix4A1,
          positiveRoundMix4B0, positiveRoundMix4C0, positiveRoundMix4D0,
          positiveRoundMix4A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix4Mem3 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix4Mem3
        simp [positiveRoundMix4D1, positiveRoundMix4A1, positiveRoundMix4B0,
          positiveRoundMix4C0, positiveRoundMix4D0, positiveRoundMix4A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundAfterMix4Stack, positiveRoundMix4A0, positiveRoundMix4D0,
      positiveRoundMix4C0, positiveRoundMix4B0, positiveRoundMix4A1,
      positiveRoundMix4D1, positiveRoundMix4C1, positiveRoundMix4B1, rotr64Bytecode,
      mask64Bytecode, u64MaskWord, Nat.add_assoc] using rd2610⟩

/-- Context-level wrapper for the generic first diagonal `mixG` body. -/
theorem positiveRoundMix4BodyFromEntryStack
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨2429⟩
          (positiveRoundMix4EntryStack ctx.executionEnv i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨2610⟩
            (positiveRoundAfterMix4Stack ctx.executionEnv i)
            (positiveRoundMix4Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 315) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix4BodyFromEntryStackRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
