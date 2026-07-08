import Benchmarks.Dss.Dog.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Dog constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

theorem dogConstructorCorrect (v : DogImmutables) :
    constructorEquivalenceWith (config v) dogCreationBytecode (contract v)
      (runtimeCodeOf dogBytecode) := by
  sorry

end Benchmarks.Dss.Dog
