import Benchmarks.UniswapV3.Pool.Common

/-!
# UniswapV3Pool constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

theorem uniswapV3PoolConstructorCorrect :
    typedConstructorRefinement config uniswapV3PoolCreationBytecode contract (immutableLayout.deployed uniswapV3PoolBytecode) := by
  sorry

end Benchmarks.UniswapV3.Pool
