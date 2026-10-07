import Benchmarks.EAS.Attester.Dispatch

/-!
# Attester attest proof scaffold

Decode the two words at calldata offsets 4 and 36 (minimum size 68, signed-size guard).
Reach arm 143, decoder 2662, body 1884. Encode the request, its dynamic tuple offsets, and
the one-word input bytes; CALL at 2127 has zero value and a 32-byte output area. There is no
EXTCODESIZE guard. Match failed calls, returns shorter than 32 bytes, and successful UID
returns, including trailing return data. The callee may modify arbitrary accounts.

The target includes malformed calldata, static entry, depth exhaustion, arbitrary callee
code, and out-of-gas paths. Do not add a permission or canonical-ABI precondition.
Generated RD summaries stop at CALL; compose that boundary using the shared call machinery.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterAttestBody (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hselector : (attesterAttestSelBytes == I.calldata.extract 0 4) = true) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  sorry

end Benchmarks.EAS.Attester
