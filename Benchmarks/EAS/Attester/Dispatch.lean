import Benchmarks.EAS.Attester.Common

/-!
# Attester dispatch scaffold

The nonpayable guard is at PC 5; its failure reverts at PC 15. Calldata shorter than four bytes
and unknown selectors reach the revert at PC 80. The selector chain compares multiRevoke,
multiAttest, attest, then revoke. Runtime PCs refer to the immutable-patched template.

Generated summaries cover both branches of each comparison. They do not compose the dispatcher
walk automatically. All statements below are proof obligations, not completed proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

structure DispatchArm where
  transitionIndex : Nat
  selector : ByteArray
  armPC : Nat
  decoderPC : Nat
  afterDecodePC : Nat
  bodyPC : Nat
  callPC : Nat

def dispatchArms : List DispatchArm :=
  [⟨2, attesterMultiRevokeSelBytes, 81, 2482, 95, 195, 906⟩,
   ⟨1, attesterMultiAttestSelBytes, 102, 2482, 116, 935, 1786⟩,
   ⟨0, attesterAttestSelBytes, 143, 2662, 157, 1884, 2127⟩,
   ⟨3, attesterRevokeSelBytes, 176, 2662, 190, 2187, 2381⟩]

theorem attesterDispatchNoneShort {data : ByteArray} (hshort : data.size < 4) :
    dispatchMsg contract data = none := by
  sorry

theorem attesterDispatchNoneUnknown {data : ByteArray}
    (hattest : (attesterAttestSelBytes == data.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == data.extract 0 4) = false)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == data.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == data.extract 0 4) = false) :
    dispatchMsg contract data = none := by
  sorry

theorem attesterNonPayable (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue ≠ ⟨0⟩) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  sorry

theorem attesterNoDispatch (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  sorry

end Benchmarks.EAS.Attester
