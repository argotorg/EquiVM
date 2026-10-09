import Benchmarks.UniswapV4PoolManager.Common

/-!
# PoolManager constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

theorem poolManagerConstructorCorrect :
    typedConstructorRefinement config poolManagerCreationBytecode contract (immutableLayout.deployed poolManagerBytecode) := by
  sorry

end Benchmarks.UniswapV4PoolManager
