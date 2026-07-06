import Benchmarks.EAS.Attester.Bytecode
import Solm.Equiv

/-!
# EAS Attester constructor correctness stub

Parameterized over the constructor-set immutable `_eas`. The constructor returns runtime bytecode
with `_eas` patched into the template at the offsets recorded in `Immutables.lean`; the proof is
left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterConstructorCorrect (v : AttesterImmutables) :
    constructorEquivalenceWith (config v) attesterCreationBytecode (contract v)
      (runtimeCodeOf attesterBytecode) := by
  sorry

end Benchmarks.EAS.Attester
