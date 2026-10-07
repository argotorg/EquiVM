import Benchmarks.EAS.Attester.Dispatch

/-!
# Attester revoke proof scaffold

Decode two complete bytes32 words (minimum calldata size 68, signed-size guard).
Reach arm 176, decoder 2662, body 2187. Match the three-word request and EXTCODESIZE at
2366 before zero-value CALL 2381. Callee failure reverts; any successful return bytes are
ignored. Account-map effects come entirely from the callee.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterRevokeBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  sorry

end Benchmarks.EAS.Attester
