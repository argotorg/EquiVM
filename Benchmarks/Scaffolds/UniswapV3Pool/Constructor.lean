import Benchmarks.Scaffolds.UniswapV3Pool.Bytecode
import Solm.Refine

/-!
# UniswapV3Pool constructor correctness stub

The constructor sets the pool's seven immutables.  `typedConstructorRefinement` checks that the runtime the EVM returns
is the template patched with the constructor's final immutables (`deployedRuntime`), and that those
are well typed.  Proof left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolConstructorCorrect :
    typedConstructorRefinement config uniswapV3PoolCreationBytecode contract
      (deployedRuntime uniswapV3PoolBytecode) := by
  sorry

end Benchmarks.UniswapV3Pool
