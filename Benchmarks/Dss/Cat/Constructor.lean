import Benchmarks.Dss.Cat.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Cat constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Cat

theorem catConstructorCorrect :
    constructorEquivalence config catCreationBytecode contract catBytecode := by
  sorry

end Benchmarks.Dss.Cat
