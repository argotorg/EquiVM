import Benchmarks.Dss.Vow.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vow constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Vow

theorem vowConstructorCorrect :
    constructorEquivalence config vowCreationBytecode contract vowBytecode := by
  sorry

end Benchmarks.Dss.Vow
