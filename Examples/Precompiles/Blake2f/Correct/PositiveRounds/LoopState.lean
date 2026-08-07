import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopGuard
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.LoopState

/-!
# BLAKE2F positive-round wrappers: loop invariant shape

This is the context-level invariant shape intended for the arbitrary-round proof.  It combines:

* the exact RDx state at the rounds-loop header;
* the pure-model memory relation from `Fallback.PositiveRounds.LoopState`;
* the computable cumulative gas recurrence `positiveRoundHeaderGas`.

The remaining hard theorem is the body step:

`positiveRoundInvariantContext ctx i mem` and `i < Model.rounds calldata`
should imply the existence of `mem'` satisfying
`positiveRoundInvariantContext ctx (i + 1) mem'`, with the RDx path going through PC `1445` and
the bytecode implementing `Model.roundStep`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def positiveRoundFinalFlagSet (ctx : BytecodeContext) : Bool :=
  ctx.executionEnv.calldata[212]! == 1

def positiveRoundInvariantContext
    (ctx : BytecodeContext) (i : Nat) (mem : ByteArray) : Prop :=
  positiveRoundHeaderRDxContext ctx i mem
    (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) i) ∧
  positiveRoundHeaderInvariant ctx.executionEnv i mem

theorem positiveRoundFinalFlagSet_eq_false_of_byte_zero
    (ctx : BytecodeContext) (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    positiveRoundFinalFlagSet ctx = false := by
  simp [positiveRoundFinalFlagSet, hbyte]

theorem positiveRoundFinalFlagSet_eq_true_of_byte_one
    (ctx : BytecodeContext) (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    positiveRoundFinalFlagSet ctx = true := by
  simp [positiveRoundFinalFlagSet, hbyte]

theorem positiveRoundInvariantContext.rdx
    {ctx : BytecodeContext} {i : Nat} {mem : ByteArray}
    (h : positiveRoundInvariantContext ctx i mem) :
    positiveRoundHeaderRDxContext ctx i mem
      (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) i) :=
  h.1

theorem positiveRoundInvariantContext.model
    {ctx : BytecodeContext} {i : Nat} {mem : ByteArray}
    (h : positiveRoundInvariantContext ctx i mem) :
    positiveRoundHeaderInvariant ctx.executionEnv i mem :=
  h.2

/-- Invariant-level exact guard exit. -/
theorem positiveRoundInvariantGuardExit
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {i : Nat} {mem : ByteArray}
    (hinv : positiveRoundInvariantContext ctx i mem)
    (hrounds : Model.rounds ctx.executionEnv.calldata = i) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundExitPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (positiveRoundGuardGas (positiveRoundFinalFlagSet ctx) i) := by
  unfold positiveRoundGuardGas
  exact positiveRoundGuardExitOfModelRoundsEq
    ctx hvalid hrounds (positiveRoundInvariantContext.rdx hinv)

/-- Invariant-level exact guard continuation. -/
theorem positiveRoundInvariantGuardContinue
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {i : Nat} {mem : ByteArray}
    (hinv : positiveRoundInvariantContext ctx i mem)
    (hrounds : i < Model.rounds ctx.executionEnv.calldata) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundBodyPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (positiveRoundGuardGas (positiveRoundFinalFlagSet ctx) i) := by
  unfold positiveRoundGuardGas
  exact positiveRoundGuardContinueOfModelRoundsGt
    ctx hvalid hrounds (positiveRoundInvariantContext.rdx hinv)

end Blake2f
