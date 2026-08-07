import Examples.Precompiles.Blake2f.Correct.Interface
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.LoopGuard

/-!
# BLAKE2F positive-round wrappers: generic loop guard

Context-level wrappers for the parametric rounds-loop guard.  These are the guard facts that an
arbitrary-round positive proof should use instead of adding more concrete `GuardN.lean` files.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def positiveRoundHeaderRDxContext
    (ctx : BytecodeContext) (i : Nat) (mem : ByteArray) (gas : Nat) : Prop :=
  ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
    positiveRoundHeaderPc
    (positiveRoundHeaderStack ctx.executionEnv i)
    mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k gas

/-- Generic exact-gas guard exit at loop index `i`, for valid bytecode contexts. -/
theorem positiveRoundGuardExitOfModelRoundsEq
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {i : Nat} {mem : ByteArray} {startGas : Nat}
    (hrounds : Model.rounds ctx.executionEnv.calldata = i)
    (hprefix : positiveRoundHeaderRDxContext ctx i mem startGas) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundExitPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (startGas + 23) := by
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState, positiveRoundHeaderRDxContext] using
    positiveRoundGuardExitOfModelRoundsEqGas
      (cA := ctx.createdAccounts)
      (gh := ctx.genesisBlockHeader)
      (bl := ctx.blocks)
      (σ := ctx.accountMap)
      (σ₀ := ctx.originalAccountMap)
      (A := ctx.substate)
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (i := i)
      (mem := mem)
      (startGas := startGas)
      hlen' hrounds
      (by simpa [positiveRoundHeaderRDxContext, BytecodeContext.initialState] using hprefix)

/-- Generic exact-gas guard continuation at loop index `i`, for valid bytecode contexts. -/
theorem positiveRoundGuardContinueOfModelRoundsGt
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {i : Nat} {mem : ByteArray} {startGas : Nat}
    (hrounds : i < Model.rounds ctx.executionEnv.calldata)
    (hprefix : positiveRoundHeaderRDxContext ctx i mem startGas) :
    ∃ k, RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundBodyPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
      (startGas + 23) := by
  obtain ⟨hlen, _hflag⟩ := hvalid
  have hlen' : ctx.executionEnv.calldata.size = 213 := by
    simpa [Model.inputLength] using hlen
  simpa [BytecodeContext.initialState, positiveRoundHeaderRDxContext] using
    positiveRoundGuardContinueOfModelRoundsGtGas
      (cA := ctx.createdAccounts)
      (gh := ctx.genesisBlockHeader)
      (bl := ctx.blocks)
      (σ := ctx.accountMap)
      (σ₀ := ctx.originalAccountMap)
      (A := ctx.substate)
      (I := ctx.executionEnv)
      (g := ctx.gas)
      (i := i)
      (mem := mem)
      (startGas := startGas)
      hlen' hrounds
      (by simpa [positiveRoundHeaderRDxContext, BytecodeContext.initialState] using hprefix)

end Blake2f
