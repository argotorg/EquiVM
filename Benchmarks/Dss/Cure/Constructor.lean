import Benchmarks.Dss.Cure.Trusted
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Cure constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Cure

theorem cureConstructorCorrect :
    constructorEquivalence config cureCreationBytecode contract cureBytecode := by
  sorry

end Benchmarks.Dss.Cure
