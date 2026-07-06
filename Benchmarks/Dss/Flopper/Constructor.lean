import Benchmarks.Dss.Flopper.Bytecode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flopper constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flopper

theorem flopperConstructorCorrect :
    constructorEquivalence config flopperCreationBytecode contract flopperBytecode := by
  sorry

end Benchmarks.Dss.Flopper
