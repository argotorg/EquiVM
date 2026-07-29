import Benchmarks.Scaffolds.EAS.Attester.Constructor
import Solm.Equiv

/-!
# EAS Attester benchmark correctness stub

For each immutable value `v`, the deployed runtime is the solc template patched with `_eas`, and
runtime equivalence is stated against `contract v`.  Proofs are the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterCorrect (v : AttesterImmutables) {code : ByteArray}
    (hcode : patchRuntime attesterBytecode (patches v) = some code) :
    runtimeEquivalence (config v) code (contract v) := by
  sorry

theorem attesterContractCorrect (v : AttesterImmutables) {code : ByteArray}
    (hcode : patchRuntime attesterBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) attesterCreationBytecode code (contract v)
      (runtimeCodeOf attesterBytecode) :=
  contractEquivalenceWith.intro (attesterConstructorCorrect v) (attesterCorrect v hcode)

end Benchmarks.EAS.Attester
