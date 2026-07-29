import Benchmarks.Scaffolds.UniswapV2Router02.Bytecode
import Solm.Equiv

/-!
# UniswapV2Router02 constructor correctness stub

Parameterized over the router's immutable values.  The constructor produces a runtime whose bytes
depend on `factory` and `WETH`; `constructorEquivalenceWith` checks that the returned runtime equals
`runtimeCodeOf` applied to the constructor's final `imm_<name>` locals.  Proof left as target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV2Router02.Immutables

namespace Benchmarks.UniswapV2Router02

theorem uniswapV2Router02ConstructorCorrect (v : RouterImmutables) :
    constructorEquivalenceWith (config v) uniswapV2Router02CreationBytecode (contract v)
      (runtimeCodeOf uniswapV2Router02Bytecode) := by
  sorry

end Benchmarks.UniswapV2Router02
