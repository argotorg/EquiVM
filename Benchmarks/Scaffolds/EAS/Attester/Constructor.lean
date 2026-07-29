import Benchmarks.Scaffolds.EAS.Attester.Bytecode
import Solm.Equiv

/-!
# EAS Attester constructor correctness stub

The creation bytecode deploys the runtime template with the immutable `_eas` patched in.  The
constructor-equivalence proof is the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterConstructorCorrect (v : AttesterImmutables) :
    constructorEquivalenceWith (config v) attesterCreationBytecode (contract v)
      (runtimeCodeOf attesterBytecode) := by
  sorry

end Benchmarks.EAS.Attester
