import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopSelector

/-!
# BLAKE2F positive-round arbitrary first `mixG`

This file factors the shared first `mixG` body out of the concrete round-6 trace.  It is
parametric in the loop index `i`: the selector supplies `SIGMA[i % 10][0]` and
`SIGMA[i % 10][1]`, and the bytecode body at PC `1512` is otherwise independent of the
round number.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev positiveRoundMix0V0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev positiveRoundMix0V4Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))

abbrev positiveRoundMix0V8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))

abbrev positiveRoundMix0V12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))

abbrev positiveRoundMix0A0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix0V0Load mem + positiveRoundMix0V4Load mem +
    sigmaMessageArg mem i 0)

abbrev positiveRoundMix0D0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix0V12Load mem) (positiveRoundMix0A0 mem i))
    ⟨32⟩ ⟨32⟩

abbrev positiveRoundMix0C0 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix0V8Load mem + positiveRoundMix0D0 mem i)

abbrev positiveRoundMix0B0 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix0V4Load mem) (positiveRoundMix0C0 mem i))
    ⟨24⟩ ⟨40⟩

abbrev positiveRoundMix0A1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix0A0 mem i + positiveRoundMix0B0 mem i +
    sigmaMessageArg mem i 1)

abbrev positiveRoundMix0D1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix0D0 mem i) (positiveRoundMix0A1 mem i))
    ⟨16⟩ ⟨48⟩

abbrev positiveRoundMix0C1 (mem : ByteArray) (i : Nat) : UInt256 :=
  mask64Bytecode (positiveRoundMix0C0 mem i + positiveRoundMix0D1 mem i)

abbrev positiveRoundMix0B1 (mem : ByteArray) (i : Nat) : UInt256 :=
  rotr64Bytecode (UInt256.xor (positiveRoundMix0B0 mem i) (positiveRoundMix0C1 mem i))
    ⟨63⟩ ⟨1⟩

def positiveRoundMix0Mem0 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix0A1 mem i)).write 0 mem (⟨1472⟩ : UInt256).toNat 32

def positiveRoundMix0Mem1 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix0B1 mem i)).write 0 (positiveRoundMix0Mem0 i mem)
    ((⟨1472⟩ : UInt256) + ⟨128⟩).toNat 32

def positiveRoundMix0Mem2 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix0C1 mem i)).write 0 (positiveRoundMix0Mem1 i mem)
    ((⟨1472⟩ : UInt256) + ⟨256⟩).toNat 32

def positiveRoundMix0Mem3 (i : Nat) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (positiveRoundMix0D1 mem i)).write 0 (positiveRoundMix0Mem2 i mem)
    ((⟨1472⟩ : UInt256) + ⟨384⟩).toNat 32

theorem positiveRoundMix0Mem0_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem0 i mem).size = 1984 := by
  unfold positiveRoundMix0Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem positiveRoundMix0Mem1_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem1 i mem).size = 1984 := by
  unfold positiveRoundMix0Mem1
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix0Mem0_size hmem
  · rw [positiveRoundMix0Mem0_size hmem]
    decide
  · native_decide

theorem positiveRoundMix0Mem2_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem2 i mem).size = 1984 := by
  unfold positiveRoundMix0Mem2
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix0Mem1_size hmem
  · rw [positiveRoundMix0Mem1_size hmem]
    decide
  · native_decide

theorem positiveRoundMix0Mem3_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundMix0Mem3 i mem).size = 1984 := by
  unfold positiveRoundMix0Mem3
  apply toByteArray_write32_size_of_le
  · exact positiveRoundMix0Mem2_size hmem
  · rw [positiveRoundMix0Mem2_size hmem]
    decide
  · native_decide

private theorem positiveRoundMix0Mload1472 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
      positiveRoundMix0V0Load mem := by
  unfold positiveRoundMix0V0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix0Mload1600 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1600⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1600⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32))) =
      positiveRoundMix0V4Load mem := by
  unfold positiveRoundMix0V4Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1600⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix0Mload1728 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1728⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1728⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32))) =
      positiveRoundMix0V8Load mem := by
  unfold positiveRoundMix0V8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1728⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem positiveRoundMix0Mload1856 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1856⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1856⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32))) =
      positiveRoundMix0V12Load mem := by
  unfold positiveRoundMix0V12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1856⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

/-- Generic exact trace for the shared first `mixG` body, from PC `1512` to PC `1693`. -/
theorem positiveRoundMix0BodyFromEntryStackRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨1693⟩
      [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (positiveRoundMix0Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 315) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨1512⟩
      [sigmaMessageArg mem i 1, sigmaMessageArg mem i 0, ⟨1693⟩,
        sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundMix0Pc, positiveRoundMix0EntryStack] using hprefix
  have hmload1472 := positiveRoundMix0Mload1472 hmem
  have hmload1600 := positiveRoundMix0Mload1600 hmem
  have hmload1728 := positiveRoundMix0Mload1728 hmem
  have hmload1856 := positiveRoundMix0Mload1856 hmem
  have rd1693 := evm_run hprefix' with [
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
    raw mload 0 (positiveRoundMix0V0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (positiveRoundMix0V4Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1600
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (positiveRoundMix0V8Load mem) (UInt256.ofNat 62)
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
    raw mload 0 (positiveRoundMix0V12Load mem) (UInt256.ofNat 62)
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
    raw mstore 0 (positiveRoundMix0Mem0 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix0Mem0
        simp [positiveRoundMix0A1, positiveRoundMix0B0, positiveRoundMix0C0,
          positiveRoundMix0D0, positiveRoundMix0A0, rotr64Bytecode, mask64Bytecode,
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
    raw mstore 0 (positiveRoundMix0Mem1 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix0Mem1
        simp [positiveRoundMix0B1, positiveRoundMix0C1, positiveRoundMix0D1,
          positiveRoundMix0A1, positiveRoundMix0B0, positiveRoundMix0C0,
          positiveRoundMix0D0, positiveRoundMix0A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix0Mem2 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix0Mem2
        simp [positiveRoundMix0C1, positiveRoundMix0D1, positiveRoundMix0A1,
          positiveRoundMix0B0, positiveRoundMix0C0, positiveRoundMix0D0,
          positiveRoundMix0A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (positiveRoundMix0Mem3 i mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold positiveRoundMix0Mem3
        simp [positiveRoundMix0D1, positiveRoundMix0A1, positiveRoundMix0B0,
          positiveRoundMix0C0, positiveRoundMix0D0, positiveRoundMix0A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [positiveRoundMix0A0, positiveRoundMix0D0, positiveRoundMix0C0,
      positiveRoundMix0B0, positiveRoundMix0A1, positiveRoundMix0D1,
      positiveRoundMix0C1, positiveRoundMix0B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd1693⟩

/-- Context-level wrapper for the generic first `mixG` body. -/
theorem positiveRoundMix0BodyFromEntryStack
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundMix0Pc
          (positiveRoundMix0EntryStack ctx.executionEnv i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨1693⟩
            [sigmaPackedWord i, ⟨3109⟩, ⟨3292⟩, UInt256.ofNat i, ⟨1⟩, ⟨640⟩,
              UInt256.shiftRight (inputFirstWord ctx.executionEnv) ⟨224⟩, ⟨384⟩,
              ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
            (positiveRoundMix0Mem3 i mem) (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 315) := by
  intro i mem hinv k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  exact positiveRoundMix0BodyFromEntryStackRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    hmem hrdx

end Blake2f
