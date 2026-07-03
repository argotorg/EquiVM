import Benchmarks.Dss.Jug.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Jug constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Jug

theorem jugConstructorCorrect :
    constructorEquivalence config jugCreationBytecode contract jugBytecode := by
  sorry

end Benchmarks.Dss.Jug
