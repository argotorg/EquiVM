import Examples.Precompiles.Ripemd160.HashCursorLoop

/-!
# RIPEMD-160 complete pure runtime run

The retained-message cursor invariant discharges the per-block parser premise of the compression
chain bridge for every allocator-accepted calldata value.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

def runtimeInitialHashState (I : ExecutionEnv) : RuntimeHashState :=
  { cursor := { mem := hashScratchMem I, aw := hashPaddedMessageAw I }
    chain := runtimeInitialChain }

theorem runtimeHashRun_final_rep_of_small (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeChainRep
      (runtimeHashRun I (Model.paddedLength I.calldata.size / 64)
        (runtimeInitialHashState I)).chain
      (Model.finalState I.calldata) := by
  apply runtimeHashRun_final_rep hsmall
  · intro block hblock
    exact runtimeHashRun_padded (RuntimePaddedCursor.initial I hsmall) hsmall
      (by omega)
  · exact runtimeInitial_rep

theorem runtimeHashRun_final_digest (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (runtimeDigestValue
      (runtimeHashRun I (Model.paddedLength I.calldata.size / 64)
        (runtimeInitialHashState I)).chain).toByteArray =
      Model.rawOutput I.calldata := by
  exact runtimeDigestValue_final I.calldata
    (runtimeHashRun_final_rep_of_small I hsmall)

end Ripemd160
