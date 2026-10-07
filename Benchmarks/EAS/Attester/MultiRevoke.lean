import Benchmarks.EAS.Attester.Dispatch

/-!
# Attester multiRevoke proof scaffold

Reach arm 81, decoder 2482, body 195. Relate schemas and nested UIDs, including aliased,
unaligned, and wrapped offsets. Establish both loop invariants, nonempty/equal lengths,
and the ordered request array. EXTCODESIZE at 891 must be nonzero before CALL 906. Match
failed calls and successful calls with arbitrary ignored return bytes. Every request value
and the CALL value is zero; no storage slot belongs to this wrapper.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterMultiRevokeBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  sorry

end Benchmarks.EAS.Attester
