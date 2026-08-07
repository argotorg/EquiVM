import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopMix7

/-!
# BLAKE2F positive-round arbitrary loop-index update

This file factors the bytecode from PC `3292` to PC `1370`.  It increments the loop index after
one full compression round and jumps back to the rounds-loop guard.  The theorem is parametric in
the completed loop index `i`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Stack at PC `1370`, after completing loop index `i` and incrementing to `i + 1`. -/
def positiveRoundAfterUpdateStack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [UInt256.ofNat (i + 1), ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
    ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

@[simp] theorem positiveRoundAfterUpdateStack_length
    (I : ExecutionEnv) (i : Nat) :
    (positiveRoundAfterUpdateStack I i).length = 7 := by
  simp [positiveRoundAfterUpdateStack]

private theorem ofNat_add {a b : Nat} (hab : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    UInt256.toNat_ofNat_of_lt (by omega), UInt256.toNat_ofNat_of_lt hab,
    Nat.mod_eq_of_lt hab]

/-- Generic exact trace for the loop-index update, from PC `3292` to PC `1370`. -/
theorem positiveRoundUpdateFromMix7Raw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hi : i + 1 < UInt256.size)
    (hprefix : RDx runtimeBytecode I g s0
      ⟨3292⟩
      (positiveRoundAfterMix7Stack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      ⟨1370⟩
      (positiveRoundAfterUpdateStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + 15) := by
  have hprefix' : RDx runtimeBytecode I g s0
      ⟨3292⟩
      [UInt256.ofNat i, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty acc k C := by
    simpa [positiveRoundAfterMix7Stack] using hprefix
  have rd1370 := evm_run hprefix' with [
    raw jumpdest (by decide) (by evm_ov),
    add,
    push2 ⟨1370⟩,
    jump (by jump_dest) ]
  have hinc : UInt256.ofNat i + (⟨1⟩ : UInt256) = UInt256.ofNat (i + 1) := by
    have h1 : (⟨1⟩ : UInt256) = UInt256.ofNat 1 := by
      native_decide
    rw [h1, ofNat_add hi]
  exact ⟨_, by
    simpa [positiveRoundAfterUpdateStack, hinc, Nat.add_assoc] using rd1370⟩

/-- Context-level wrapper for the generic loop-index update. -/
theorem positiveRoundUpdateFromMix7
    (ctx : BytecodeContext) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      i + 1 < UInt256.size →
      ∀ {k C : Nat},
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          ⟨3292⟩
          (positiveRoundAfterMix7Stack ctx.executionEnv i)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            ⟨1370⟩
            (positiveRoundAfterUpdateStack ctx.executionEnv i)
            mem (UInt256.ofNat 62) ByteArray.empty
            (ctx.createdAccounts, ctx.accountMap) k'
            (C + 15) := by
  intro _i _mem _hinv hi _k _C hrdx
  exact positiveRoundUpdateFromMix7Raw hi hrdx

end Blake2f
