import Benchmarks.EAS.Attester.Constructor
import Benchmarks.EAS.Attester.Attest
import Benchmarks.EAS.Attester.MultiAttest
import Benchmarks.EAS.Attester.MultiRevoke
import Benchmarks.EAS.Attester.Revoke
import Solm.Refine

/-!
# EAS Attester benchmark correctness stub

For every well-typed assignment of `_eas`, the runtime deployed for it (the template patched with
it) refines the spec run with those immutables.  With the constructor target this gives the
contract refinement.  Proofs are the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterCorrect (imms : Store) (_hfit : immutablesFit contract imms) :
    runtimeRefinement config (deployedRuntime attesterBytecode imms) contract
      (restrictImmutables contract imms) := by
  refine ⟨fun σ σ₀ g A I hcode hsize ↦ ?_⟩
  by_cases hvalue : I.weiValue = ⟨0⟩
  · by_cases hshort : I.calldata.size < 4
    · exact attesterNoDispatch imms _hfit hcode hsize hvalue
        (attesterDispatchNoneShort hshort)
    · by_cases hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true
      · exact attesterAttestBody imms _hfit hcode hsize hvalue hattest
      · by_cases hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true
        · exact attesterMultiAttestBody imms _hfit hcode hsize hvalue hmultiAttest
        · by_cases hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true
          · exact attesterMultiRevokeBody imms _hfit hcode hsize hvalue hmultiRevoke
          · by_cases hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true
            · exact attesterRevokeBody imms _hfit hcode hsize hvalue hrevoke
            · exact attesterNoDispatch imms _hfit hcode hsize hvalue
                (attesterDispatchNoneUnknown (Bool.eq_false_of_not_eq_true hattest)
                  (Bool.eq_false_of_not_eq_true hmultiAttest)
                  (Bool.eq_false_of_not_eq_true hmultiRevoke)
                  (Bool.eq_false_of_not_eq_true hrevoke))
  · exact attesterNonPayable imms _hfit hcode hsize hvalue

theorem attesterContractCorrect : contractRefinement config attesterCreationBytecode contract :=
  .of_runtime attesterConstructorCorrect attesterCorrect

end Benchmarks.EAS.Attester
