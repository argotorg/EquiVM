import Benchmarks.Dss.DaiJoin.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS DaiJoin constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.DaiJoin

theorem daiJoinConstructorCorrect :
    constructorEquivalence config daiJoinCreationBytecode contract daiJoinBytecode := by
  sorry

end Benchmarks.Dss.DaiJoin
