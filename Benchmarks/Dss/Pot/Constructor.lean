import Benchmarks.Dss.Pot.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Pot constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Pot

theorem potConstructorCorrect :
    constructorEquivalence config potCreationBytecode contract potBytecode := by
  sorry

end Benchmarks.Dss.Pot
