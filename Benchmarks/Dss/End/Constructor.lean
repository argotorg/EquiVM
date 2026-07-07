import Benchmarks.Dss.End.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS End constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.End

theorem endConstructorBodyCore :
    constructorEquivalence config endCreationBytecode contract endBytecode := by
  sorry

theorem endConstructorCorrect :
    constructorEquivalence config endCreationBytecode contract endBytecode := by
  exact endConstructorBodyCore

end Benchmarks.Dss.End
