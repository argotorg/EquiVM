import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix7

/-!
# BLAKE2F positive-round post-loop setup bridge

This file starts the post-loop proof for the arbitrary-round path.  It deliberately contains only
the small transition from the rounds-loop exit to the output-loop head; the output-loop word ranges
are proved in follow-on files to keep elaboration localized.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- After the positive-round guard exits, the bytecode drops the compression-loop state and enters
the output loop with index `0`.

Source note: this is PC `1378..1381`, the same cleanup used by the zero-round branch after its guard
falls through, but stated for the arbitrary-round loop's final memory. -/
theorem positiveRoundOutputLoopSetupFromExit
    (ctx : BytecodeContext)
    {i k C : Nat} {mem : ByteArray}
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundExitPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k', RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      ⟨1382⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k' (C + 8) := by
  have rd1382 := evm_run hrdx with [
    pop,
    pop,
    pop,
    push0 ]
  exact ⟨_, by simpa [positiveRoundExitPc, positiveRoundHeaderStack] using rd1382⟩

end Blake2f
