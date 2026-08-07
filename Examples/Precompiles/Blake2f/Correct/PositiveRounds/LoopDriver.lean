import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopState
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.LoopSigma

/-!
# BLAKE2F positive-round loop driver

This module is the arbitrary-round interface for the positive compression loop.  It does not prove
the round body itself.  Instead, it packages the exact statement the body proof must supply:

* from loop-body PC `1445` at index `i`,
* under the current invariant and `i < rounds`,
* reach the next loop header PC `1370` at index `i + 1`,
* preserve the model/memory invariant,
* and charge exactly `positiveRoundBodyDelta i`.

The theorem `positiveRoundLoopFromInvariant` then turns that local body fact into a complete
arbitrary-round loop proof, using the generic guard facts and `RDx.whileLoopCarryGas`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- State carried by the positive-round loop proof. -/
structure PositiveRoundLoopState where
  index : Nat
  mem : ByteArray

/-- Remaining exact gas from loop header at index `i` until guard exit. -/
def positiveRoundRemainingGas : Nat → Nat → Nat
  | _, 0 => 23
  | i, n + 1 => positiveRoundDelta i + positiveRoundRemainingGas (i + 1) n

@[simp] theorem positiveRoundRemainingGas_zero (i : Nat) :
    positiveRoundRemainingGas i 0 = 23 := by
  rfl

@[simp] theorem positiveRoundRemainingGas_succ (i n : Nat) :
    positiveRoundRemainingGas i (n + 1) =
      positiveRoundDelta i + positiveRoundRemainingGas (i + 1) n := by
  rfl

theorem positiveRoundHeaderGas_add_remaining
    (finalFlagSet : Bool) (i n : Nat) :
    positiveRoundHeaderGas finalFlagSet i + positiveRoundRemainingGas i n =
      positiveRoundHeaderGas finalFlagSet (i + n) + 23 := by
  induction n generalizing i with
  | zero =>
      simp
  | succ n ih =>
      calc
        positiveRoundHeaderGas finalFlagSet i + positiveRoundRemainingGas i (n + 1)
            =
              positiveRoundHeaderGas finalFlagSet i +
                (positiveRoundDelta i + positiveRoundRemainingGas (i + 1) n) := by
              rfl
        _ = positiveRoundHeaderGas finalFlagSet (i + 1) +
              positiveRoundRemainingGas (i + 1) n := by
              rw [positiveRoundHeaderGas_succ]
              omega
        _ = positiveRoundHeaderGas finalFlagSet ((i + 1) + n) + 23 := by
              exact ih (i + 1)
        _ = positiveRoundHeaderGas finalFlagSet (i + (n + 1)) + 23 := by
              congr 2
              omega

/-- Body theorem shape expected from the low-level bytecode proof. -/
def PositiveRoundBodyStep (ctx : BytecodeContext) : Prop :=
  ∀ {i : Nat} {mem : ByteArray},
    positiveRoundInvariantContext ctx i mem →
    i < Model.rounds ctx.executionEnv.calldata →
    ∀ {k C : Nat},
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundBodyPc
        (positiveRoundHeaderStack ctx.executionEnv i)
        mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
      ∃ mem' k',
        positiveRoundInvariantContext ctx (i + 1) mem' ∧
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundHeaderPc
          (positiveRoundHeaderStack ctx.executionEnv (i + 1))
          mem' (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
          (C + positiveRoundBodyDelta i)

/-- Header-to-header round step obtained by adding the generic guard to a body proof. -/
theorem PositiveRoundBodyStep.toHeaderStep
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    (hbody : PositiveRoundBodyStep ctx)
    {i : Nat} {mem : ByteArray}
    (hinv : positiveRoundInvariantContext ctx i mem)
    (hrounds : i < Model.rounds ctx.executionEnv.calldata)
    {k C : Nat}
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundHeaderPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ mem' k',
      positiveRoundInvariantContext ctx (i + 1) mem' ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundHeaderPc
        (positiveRoundHeaderStack ctx.executionEnv (i + 1))
        mem' (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
        (C + positiveRoundDelta i) := by
  have hprefix :
      positiveRoundHeaderRDxContext ctx i mem C := ⟨k, hrdx⟩
  obtain ⟨kg, hguard⟩ :=
    positiveRoundGuardContinueOfModelRoundsGt ctx hvalid hrounds hprefix
  obtain ⟨mem', kb, hinv', hnext⟩ :=
    hbody hinv hrounds hguard
  refine ⟨mem', kb, hinv', ?_⟩
  have hcost : C + 23 + positiveRoundBodyDelta i = C + positiveRoundDelta i := by
    rw [positiveRoundDelta_decompose]
    omega
  exact RDx.withIndices hnext rfl hcost

def positiveRoundLoopInv (ctx : BytecodeContext)
    (remaining : Nat) (st : PositiveRoundLoopState) : Prop :=
  st.index + remaining = Model.rounds ctx.executionEnv.calldata ∧
    positiveRoundInvariantContext ctx st.index st.mem

def positiveRoundLoopStack (ctx : BytecodeContext)
    (st : PositiveRoundLoopState) : List UInt256 :=
  positiveRoundHeaderStack ctx.executionEnv st.index

def positiveRoundLoopExitStack (ctx : BytecodeContext)
    (st : PositiveRoundLoopState) : List UInt256 :=
  positiveRoundHeaderStack ctx.executionEnv st.index

/-- Arbitrary-round positive-loop theorem, parameterized by the local body proof. -/
theorem positiveRoundLoopFromInvariant
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContext ctx 0 mem0)
    (hbody : PositiveRoundBodyStep ctx) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  let rounds := Model.rounds ctx.executionEnv.calldata
  let st0 : PositiveRoundLoopState := { index := 0, mem := mem0 }
  have hInv0 : positiveRoundLoopInv ctx rounds st0 := by
    simp [positiveRoundLoopInv, st0, rounds, hinv0]
  obtain ⟨k0, hrdx0⟩ := positiveRoundInvariantContext.rdx hinv0
  have hexit :
      ∀ st, positiveRoundLoopInv ctx 0 st → ∀ k C,
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundHeaderPc (positiveRoundLoopStack ctx st) st.mem (UInt256.ofNat 62)
          ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            positiveRoundExitPc (positiveRoundLoopExitStack ctx st) st.mem (UInt256.ofNat 62)
            ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
            (C + positiveRoundRemainingGas st.index 0) := by
    intro st hInv k C hrdx
    have hrel : st.index + 0 = Model.rounds ctx.executionEnv.calldata := hInv.1
    have hrounds : Model.rounds ctx.executionEnv.calldata = st.index := by
      omega
    have hprefix : positiveRoundHeaderRDxContext ctx st.index st.mem C := by
      exact ⟨k, by simpa [positiveRoundLoopStack] using hrdx⟩
    simpa [positiveRoundLoopExitStack, positiveRoundRemainingGas] using
      positiveRoundGuardExitOfModelRoundsEq
        ctx hvalid hrounds hprefix
  have hstep :
      ∀ v st, positiveRoundLoopInv ctx (v + 1) st → ∀ k C,
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundHeaderPc (positiveRoundLoopStack ctx st) st.mem (UInt256.ofNat 62)
          ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ st' k' dC,
          positiveRoundLoopInv ctx v st' ∧
          positiveRoundRemainingGas st.index (v + 1) =
            dC + positiveRoundRemainingGas st'.index v ∧
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            positiveRoundHeaderPc (positiveRoundLoopStack ctx st') st'.mem (UInt256.ofNat 62)
            ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k' (C + dC) := by
    intro v st hInv k C hrdx
    have hrel : st.index + (v + 1) = Model.rounds ctx.executionEnv.calldata := hInv.1
    have hlt : st.index < Model.rounds ctx.executionEnv.calldata := by
      omega
    obtain ⟨mem', k', hinv', hnext⟩ :=
      PositiveRoundBodyStep.toHeaderStep
        ctx hvalid hbody hInv.2 hlt (by simpa [positiveRoundLoopStack] using hrdx)
    let st' : PositiveRoundLoopState := { index := st.index + 1, mem := mem' }
    refine ⟨st', k', positiveRoundDelta st.index, ?_, ?_, ?_⟩
    · constructor
      · simp [st']
        omega
      · simpa [st'] using hinv'
    · simp [st']
    · simpa [positiveRoundLoopStack, st'] using hnext
  obtain ⟨stFinal, kFinal, hInvFinal, hrdxFinal⟩ :=
    RDx.whileLoopCarryGas
      (code := runtimeBytecode)
      (ee := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (rdata := ByteArray.empty)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      positiveRoundHeaderPc
      positiveRoundExitPc
      (positiveRoundLoopInv ctx)
      (positiveRoundLoopStack ctx)
      (fun st => st.mem)
      (fun _ => UInt256.ofNat 62)
      (positiveRoundLoopExitStack ctx)
      (fun remaining st => positiveRoundRemainingGas st.index remaining)
      hexit hstep
      rounds st0 hInv0 k0
      (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) 0)
      (by simpa [positiveRoundLoopStack, st0] using hrdx0)
  have hidx : stFinal.index = Model.rounds ctx.executionEnv.calldata := by
    have hrel : stFinal.index + 0 = Model.rounds ctx.executionEnv.calldata := hInvFinal.1
    omega
  have hcost :
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) 0 +
          positiveRoundRemainingGas 0 rounds =
        positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23 := by
    simpa [rounds] using
      positiveRoundHeaderGas_add_remaining
        (positiveRoundFinalFlagSet ctx) 0 rounds
  refine ⟨stFinal.mem, kFinal, ?_, ?_⟩
  · simpa [hidx] using hInvFinal.2
  · have hrdxCost := RDx.withIndices hrdxFinal rfl hcost
    simpa [positiveRoundLoopExitStack, hidx] using hrdxCost

end Blake2f
