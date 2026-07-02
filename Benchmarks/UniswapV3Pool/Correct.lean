import Benchmarks.UniswapV3Pool.Constructor
import Solm.Equiv

/-!
# UniswapV3Pool benchmark correctness stub

The upstream Solidity source tree, optimized runtime bytecode, Solm AST spec, and Solm syntax spec
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolCorrect :
    runtimeEquivalence!?! config uniswapV3PoolBytecode contract := by
  sorry

theorem uniswapV3PoolContractCorrect :
    contractEquivalence config uniswapV3PoolCreationBytecode uniswapV3PoolBytecode contract :=
  contractEquivalence.intro uniswapV3PoolConstructorCorrect uniswapV3PoolCorrect

end Benchmarks.UniswapV3Pool
