import Benchmarks.Dss.GemJoin.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS GemJoin constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.GemJoin

theorem gemJoinConstructorCorrect :
    constructorEquivalence config gemJoinCreationBytecode contract gemJoinBytecode := by
  sorry

end Benchmarks.Dss.GemJoin
