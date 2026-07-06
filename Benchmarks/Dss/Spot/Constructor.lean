import Benchmarks.Dss.Spot.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Spotter constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Spot

theorem spotConstructorCorrect :
    constructorEquivalence config spotCreationBytecode contract spotBytecode := by
  sorry

end Benchmarks.Dss.Spot
