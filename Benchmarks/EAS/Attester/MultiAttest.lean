import Benchmarks.EAS.Attester.Dispatch

/-!
# Attester multiAttest proof scaffold

Reach arm 102, decoder 2482, body 935. Relate the schemas and nested inputs, including
noncanonical aliases and wrapped nested offsets. Establish the outer/inner loop invariants,
nonempty/equal lengths, and the request array in memory. Before CALL 1786 the free pointer
is 160 + 192*n + 480*sum(inner lengths). Match the raw zero-value call, return-copy rounding,
the bytes32[] decoder at 3547, and its allocation guard at 3681–3693 before canonical return
encoding. Neither the number nor the content of returned UIDs is checked against the input.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterMultiAttestBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  sorry

end Benchmarks.EAS.Attester
