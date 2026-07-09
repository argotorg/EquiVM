import Benchmarks.EAS.Attester.Constructor
import Benchmarks.EAS.Attester.Attest
import Benchmarks.EAS.Attester.MultiAttest
import Benchmarks.EAS.Attester.MultiRevoke
import Benchmarks.EAS.Attester.Revoke
import Solm.Equiv

/-!
# EAS Attester benchmark correctness stub

For each immutable value `v`, the deployed runtime is the solc template patched with `_eas`
(`patchRuntime attesterBytecode (patches v) = some code`), and runtime equivalence is stated
against `contract v`. Proofs are intentionally left as targets.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem attesterCorrect (v : AttesterImmutables) {code : ByteArray}
    (hcode : patchRuntime attesterBytecode (patches v) = some code) :
    runtimeEquivalence!?! (config v) code (contract v) := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hIcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hshort : I.calldata.size < 4
    · exact attesterNoDispatchShort v hcode hIcode hsize hperm hwv hshort hAccounts
    · have hsz4 : 4 ≤ I.calldata.size := by omega
      by_cases hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true
      · exact attesterMultiRevokeBodyCore v hcode hIcode hsize hperm hwv hmultiRevoke hAccounts
      · have hmultiRevokeF :
            (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false :=
          Bool.eq_false_of_not_eq_true hmultiRevoke
        by_cases hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true
        · exact attesterMultiAttestBodyCore v hcode hIcode hsize hperm hwv
            hmultiRevokeF hmultiAttest hAccounts
        · have hmultiAttestF :
              (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false :=
            Bool.eq_false_of_not_eq_true hmultiAttest
          by_cases hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true
          · exact attesterAttestBodyCore v hcode hIcode hsize hperm hwv
              hmultiRevokeF hmultiAttestF hattest hAccounts
          · have hattestF :
                (attesterAttestSelBytes == I.calldata.extract 0 4) = false :=
              Bool.eq_false_of_not_eq_true hattest
            by_cases hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true
            · exact attesterRevokeBodyCore v hcode hIcode hsize hperm hwv
                hmultiRevokeF hmultiAttestF hattestF hrevoke hAccounts
            · have hrevokeF :
                  (attesterRevokeSelBytes == I.calldata.extract 0 4) = false :=
                Bool.eq_false_of_not_eq_true hrevoke
              exact attesterNoDispatchNoMatch v hcode hIcode hsize hperm hwv hsz4
                hmultiRevokeF hmultiAttestF hattestF hrevokeF hAccounts
  · exact attesterNonPayable v hcode hIcode hwv

theorem attesterContractCorrect (v : AttesterImmutables) {code : ByteArray}
    (hcode : patchRuntime attesterBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) attesterCreationBytecode code (contract v)
      (runtimeCodeOf attesterBytecode) :=
  contractEquivalenceWith.intro
    (attesterConstructorCorrect v)
    (attesterCorrect v hcode)

end Benchmarks.EAS.Attester
