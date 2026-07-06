import Benchmarks.Dss.LinearDecrease.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS LinearDecrease constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.LinearDecrease

theorem linearDecreaseConstructorCorrect :
    constructorEquivalence config linearDecreaseCreationBytecode contract linearDecreaseBytecode := by
  sorry

end Benchmarks.Dss.LinearDecrease
