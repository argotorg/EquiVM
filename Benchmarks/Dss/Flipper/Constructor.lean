import Benchmarks.Dss.Flipper.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flipper constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flipper

theorem flipperConstructorCorrect :
    constructorEquivalence config flipperCreationBytecode contract flipperBytecode := by
  sorry

end Benchmarks.Dss.Flipper
