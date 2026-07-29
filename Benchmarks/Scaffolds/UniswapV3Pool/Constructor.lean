import Benchmarks.Scaffolds.UniswapV3Pool.Bytecode
import Solm.Equiv

/-!
# UniswapV3Pool constructor correctness stub

Parameterized over the pool's immutable values.  The constructor produces a runtime whose bytes
depend on the seven immutables; `constructorEquivalenceWith` checks that the runtime the EVM returns
equals `runtimeCodeOf` applied to the constructor's final `imm_<name>` locals.  Proof left as target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolConstructorCorrect (v : PoolImmutables) :
    constructorEquivalenceWith (config v) uniswapV3PoolCreationBytecode (contract v)
      (runtimeCodeOf uniswapV3PoolBytecode) := by
  sorry

end Benchmarks.UniswapV3Pool
