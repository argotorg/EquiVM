import Benchmarks.Scaffolds.UniswapV3Pool.Constructor
import Solm.Refine

/-!
# UniswapV3Pool benchmark correctness stub

For every well-typed assignment of the pool's seven immutables, the runtime deployed for it (the template patched with
it) refines the spec run with those immutables.  With the constructor target this gives the
contract refinement.  Proofs are the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolCorrect (imms : Store) (_hfit : immutablesFit contract imms) :
    runtimeRefinement config (deployedRuntime uniswapV3PoolBytecode imms) contract
      (restrictImmutables contract imms) := by
  sorry

theorem uniswapV3PoolContractCorrect : contractRefinement config uniswapV3PoolCreationBytecode contract :=
  .of_runtime uniswapV3PoolConstructorCorrect uniswapV3PoolCorrect

end Benchmarks.UniswapV3Pool
