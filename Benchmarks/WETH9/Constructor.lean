import Benchmarks.WETH9.Bytecode
import Solm.Equiv

/-!
# WETH9 constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present.  The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.WETH9

theorem weth9ConstructorCorrect :
    constructorEquivalence config weth9CreationBytecode contract weth9Bytecode := by
  sorry

end Benchmarks.WETH9
