import Benchmarks.Dss.Flapper.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flapper constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flapper

theorem flapperConstructorCorrect :
    constructorEquivalence config flapperCreationBytecode contract flapperBytecode := by
  sorry

end Benchmarks.Dss.Flapper
