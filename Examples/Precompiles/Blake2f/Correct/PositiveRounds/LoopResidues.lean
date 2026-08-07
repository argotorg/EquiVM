import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopDriver

/-!
# BLAKE2F positive-round residue split

The bytecode body for a positive round is periodic in `i % 10`, because both the trusted model and
the compiled selector use the ten-row BLAKE2F `SIGMA` schedule.  This file factors the remaining
body obligation into ten residue-specific obligations.

The intended use is:

1. choose the residue-specific bytecode memory transformer;
2. prove its exact `RDx` trace (`PositiveRoundResidueBodyTrace`);
3. prove it preserves the pure model/memory invariant (`PositiveRoundResidueInvariantStep`);
4. combine those into `PositiveRoundResidueBodyStep ctx r`;
5. combine the ten residue body proofs and pass the result to `positiveRoundLoopFromInvariant`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The local round-body theorem specialized to one SIGMA residue. -/
def PositiveRoundResidueBodyStep (ctx : BytecodeContext) (residue : Nat) : Prop :=
  ∀ {i : Nat} {mem : ByteArray},
    i % 10 = residue →
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

/-- Exact bytecode trace obligation for one residue and one chosen memory transformer.

This is deliberately independent of the pure model invariant: it is the local `evm_run` target for
the bytecode body from PC `1445` back to PC `1370`. -/
def PositiveRoundResidueBodyTrace
    (ctx : BytecodeContext) (residue : Nat) (nextMem : Nat → ByteArray → ByteArray) : Prop :=
  ∀ {i : Nat} {mem : ByteArray},
    i % 10 = residue →
    positiveRoundInvariantContext ctx i mem →
    i < Model.rounds ctx.executionEnv.calldata →
    ∀ {k C : Nat},
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundBodyPc
        (positiveRoundHeaderStack ctx.executionEnv i)
        mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
      ∃ k',
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundHeaderPc
          (positiveRoundHeaderStack ctx.executionEnv (i + 1))
          (nextMem i mem) (UInt256.ofNat 62) ByteArray.empty
          (ctx.createdAccounts, ctx.accountMap) k'
          (C + positiveRoundBodyDelta i)

/-- Selector-prefix trace for one residue.

This is the first reusable bytecode obligation for an arbitrary positive round: from loop-body
PC `1445`, execute the periodic SIGMA selector and prepare the first `mixG` call at PC `1512`.
It intentionally leaves the eight `mixG` calls and loop-index update to a separate remainder
trace. -/
def PositiveRoundResidueSelectorTrace
    (ctx : BytecodeContext) (residue : Nat)
    (mix0Stack : Nat → ByteArray → List UInt256) : Prop :=
  ∀ {i : Nat} {mem : ByteArray},
    i % 10 = residue →
    positiveRoundInvariantContext ctx i mem →
    i < Model.rounds ctx.executionEnv.calldata →
    ∀ {k C : Nat},
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundBodyPc
        (positiveRoundHeaderStack ctx.executionEnv i)
        mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
      ∃ k',
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundMix0Pc
          (mix0Stack i mem)
          mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
          (C + sigmaSelectorToMix0Gas i)

/-- Remainder trace for one residue after the selector has reached the shared `mixG` entry.

This covers the eight `mixG` calls, the round-index increment, and the jump back to the loop
header.  It is parameterized by the stack produced by the selector-prefix theorem, so residue
proofs can be built from two smaller exact-gas traces. -/
def PositiveRoundResidueMixRemainderTrace
    (ctx : BytecodeContext) (residue : Nat)
    (mix0Stack : Nat → ByteArray → List UInt256)
    (nextMem : Nat → ByteArray → ByteArray) : Prop :=
  ∀ {i : Nat} {mem : ByteArray},
    i % 10 = residue →
    positiveRoundInvariantContext ctx i mem →
    i < Model.rounds ctx.executionEnv.calldata →
    ∀ {k C : Nat},
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundMix0Pc
        (mix0Stack i mem)
        mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
      ∃ k',
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundHeaderPc
          (positiveRoundHeaderStack ctx.executionEnv (i + 1))
          (nextMem i mem) (UInt256.ofNat 62) ByteArray.empty
          (ctx.createdAccounts, ctx.accountMap) k'
          (C + positiveRoundAfterMix0EntryGas)

/-- Selector-prefix plus shared-mix remainder gives the full residue body trace. -/
theorem PositiveRoundResidueBodyTrace.of_selector_and_remainder
    (ctx : BytecodeContext) (residue : Nat)
    (mix0Stack : Nat → ByteArray → List UInt256)
    (nextMem : Nat → ByteArray → ByteArray)
    (hselector : PositiveRoundResidueSelectorTrace ctx residue mix0Stack)
    (hremainder : PositiveRoundResidueMixRemainderTrace ctx residue mix0Stack nextMem) :
    PositiveRoundResidueBodyTrace ctx residue nextMem := by
  intro i mem hresidue hinv hrounds k C hrdx
  obtain ⟨ks, hmix0⟩ := hselector hresidue hinv hrounds hrdx
  obtain ⟨kr, hnext⟩ := hremainder hresidue hinv hrounds hmix0
  refine ⟨kr, ?_⟩
  have hcost :
      C + sigmaSelectorToMix0Gas i + positiveRoundAfterMix0EntryGas =
        C + positiveRoundBodyDelta i := by
    unfold positiveRoundBodyDelta
    omega
  exact RDx.withIndices hnext rfl hcost

/-- Pure/model-memory preservation obligation for one residue and memory transformer. -/
def PositiveRoundResidueInvariantStep
    (ctx : BytecodeContext) (residue : Nat) (nextMem : Nat → ByteArray → ByteArray) : Prop :=
  ∀ {i : Nat} {mem : ByteArray},
    i % 10 = residue →
    positiveRoundInvariantContext ctx i mem →
    i < Model.rounds ctx.executionEnv.calldata →
    positiveRoundInvariantContext ctx (i + 1) (nextMem i mem)

/-- A residue body trace plus invariant preservation gives the residue body step. -/
theorem PositiveRoundResidueBodyStep.of_trace_and_invariant
    (ctx : BytecodeContext) (residue : Nat) (nextMem : Nat → ByteArray → ByteArray)
    (htrace : PositiveRoundResidueBodyTrace ctx residue nextMem)
    (hinvStep : PositiveRoundResidueInvariantStep ctx residue nextMem) :
    PositiveRoundResidueBodyStep ctx residue := by
  intro i mem hresidue hinv hrounds k C hrdx
  obtain ⟨k', hrdx'⟩ := htrace hresidue hinv hrounds hrdx
  exact ⟨nextMem i mem, k', hinvStep hresidue hinv hrounds, hrdx'⟩

/-- Selector-prefix, shared-mix remainder, and invariant preservation give a residue body step. -/
theorem PositiveRoundResidueBodyStep.of_selector_remainder_and_invariant
    (ctx : BytecodeContext) (residue : Nat)
    (mix0Stack : Nat → ByteArray → List UInt256)
    (nextMem : Nat → ByteArray → ByteArray)
    (hselector : PositiveRoundResidueSelectorTrace ctx residue mix0Stack)
    (hremainder : PositiveRoundResidueMixRemainderTrace ctx residue mix0Stack nextMem)
    (hinvStep : PositiveRoundResidueInvariantStep ctx residue nextMem) :
    PositiveRoundResidueBodyStep ctx residue := by
  exact PositiveRoundResidueBodyStep.of_trace_and_invariant ctx residue nextMem
    (PositiveRoundResidueBodyTrace.of_selector_and_remainder
      ctx residue mix0Stack nextMem hselector hremainder)
    hinvStep

/-- Any family of residue body proofs covering `0..9` gives the global body step. -/
theorem positiveRoundBodyStep_of_residue_family
    (ctx : BytecodeContext)
    (hresidue : ∀ residue, residue < 10 → PositiveRoundResidueBodyStep ctx residue) :
    PositiveRoundBodyStep ctx := by
  intro i mem hinv hrounds k C hrdx
  exact hresidue (i % 10) (Nat.mod_lt i (by decide)) rfl hinv hrounds hrdx

/-- Ten explicit residue proofs give the global body step. -/
theorem positiveRoundBodyStep_of_ten_residues
    (ctx : BytecodeContext)
    (h0 : PositiveRoundResidueBodyStep ctx 0)
    (h1 : PositiveRoundResidueBodyStep ctx 1)
    (h2 : PositiveRoundResidueBodyStep ctx 2)
    (h3 : PositiveRoundResidueBodyStep ctx 3)
    (h4 : PositiveRoundResidueBodyStep ctx 4)
    (h5 : PositiveRoundResidueBodyStep ctx 5)
    (h6 : PositiveRoundResidueBodyStep ctx 6)
    (h7 : PositiveRoundResidueBodyStep ctx 7)
    (h8 : PositiveRoundResidueBodyStep ctx 8)
    (h9 : PositiveRoundResidueBodyStep ctx 9) :
    PositiveRoundBodyStep ctx := by
  apply positiveRoundBodyStep_of_residue_family ctx
  intro residue hlt
  interval_cases residue <;> assumption

/-- Complete arbitrary-round positive loop from ten residue-specific body proofs. -/
theorem positiveRoundLoopFromInvariant_of_ten_residues
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContext ctx 0 mem0)
    (h0 : PositiveRoundResidueBodyStep ctx 0)
    (h1 : PositiveRoundResidueBodyStep ctx 1)
    (h2 : PositiveRoundResidueBodyStep ctx 2)
    (h3 : PositiveRoundResidueBodyStep ctx 3)
    (h4 : PositiveRoundResidueBodyStep ctx 4)
    (h5 : PositiveRoundResidueBodyStep ctx 5)
    (h6 : PositiveRoundResidueBodyStep ctx 6)
    (h7 : PositiveRoundResidueBodyStep ctx 7)
    (h8 : PositiveRoundResidueBodyStep ctx 8)
    (h9 : PositiveRoundResidueBodyStep ctx 9) :
    ∃ memFinal k,
      positiveRoundInvariantContext ctx (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  exact positiveRoundLoopFromInvariant ctx hvalid hinv0
    (positiveRoundBodyStep_of_ten_residues ctx h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)

end Blake2f
