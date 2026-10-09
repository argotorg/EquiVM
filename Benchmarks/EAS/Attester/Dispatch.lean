import Benchmarks.EAS.Attester.DispatchTrace

/-!
# Attester dispatch scaffold

The nonpayable guard is at PC 5; its failure reverts at PC 15. Calldata shorter than four bytes
and unknown selectors reach the revert at PC 80. The selector chain compares multiRevoke,
multiAttest, attest, then revoke. Runtime PCs refer to the immutable-patched template.

Generated summaries cover both branches of each comparison. They do not compose the dispatcher
walk automatically. All statements below are proof obligations, not completed proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
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
  rw [dispatchMsg_eq_dispatchList contract data, contract_transitions]
  apply dispatchList_none_short _ _ hshort
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [attestSelectorOf]; rfl
  · rw [multiAttestSelectorOf]; rfl
  · rw [multiRevokeSelectorOf]; rfl
  · rw [revokeSelectorOf]; rfl

theorem attesterDispatchNoneUnknown {data : ByteArray}
    (hattest : (attesterAttestSelBytes == data.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == data.extract 0 4) = false)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == data.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == data.extract 0 4) = false) :
    dispatchMsg contract data = none := by
  rw [dispatchMsg_eq_dispatchList contract data, contract_transitions]
  simp only [dispatchList_cons, dispatchList_nil, attestSelectorOf, multiAttestSelectorOf,
    multiRevokeSelectorOf, revokeSelectorOf, hattest, hmultiAttest, hmultiRevoke, hrevoke,
    Bool.false_eq_true, if_false]

theorem attesterNonPayable (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue ≠ ⟨0⟩) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hcode' := hcode.trans (deployedRuntime_eq_layout hfit)
  have hrev := attesterRuntimeRevertValue (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hvalue
  apply hrev.reEquivNonPayableOfMem hcode'
  intro t ht callargs
  rw [contract_transitions] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> exact bodyReverts_nonPayable hvalue

theorem attesterNoDispatch (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = deployedRuntime attesterBytecode imms)
    (hsize : I.calldata.size < UInt256.size) (hvalue : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hcode' := hcode.trans (deployedRuntime_eq_layout hfit)
  by_cases hshort : I.calldata.size < 4
  · exact (attesterRuntimeRevertShort (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode' hvalue hshort).reEquivNoDispatch hcode' hdispatch
  · have hnone := hdispatch
    rw [dispatchMsg_eq_dispatchList contract I.calldata, contract_transitions] at hnone
    simp only [dispatchList_cons, dispatchList_nil, attestSelectorOf, multiAttestSelectorOf,
      multiRevokeSelectorOf, revokeSelectorOf] at hnone
    split at hnone
    · cases hnone
    · rename_i hattest
      split at hnone
      · cases hnone
      · rename_i hmultiAttest
        split at hnone
        · cases hnone
        · rename_i hmultiRevoke
          split at hnone
          · cases hnone
          · rename_i hrevoke
            exact (attesterRuntimeRevertUnknown (σ := σ) (σ₀ := σ₀) (A := A)
              (g := Sat256.ofUInt256 g) hcode' hvalue (by omega) hsize
              (Bool.eq_false_of_not_eq_true hattest)
              (Bool.eq_false_of_not_eq_true hmultiAttest)
              (Bool.eq_false_of_not_eq_true hmultiRevoke)
              (Bool.eq_false_of_not_eq_true hrevoke)).reEquivNoDispatch hcode' hdispatch

end Benchmarks.EAS.Attester
