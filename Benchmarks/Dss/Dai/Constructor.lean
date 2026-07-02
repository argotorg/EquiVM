import Benchmarks.Dss.Dai.Bytecode
import Solm.Equiv

/-!
# MakerDAO DSS Dai constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present.  The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Dai

theorem daiConstructorCorrect :
    constructorEquivalence config daiCreationBytecode contract daiBytecode := by
  sorry

end Benchmarks.Dss.Dai
