import Benchmarks.Scaffolds.UniswapV3Pool.Constructor
import Solm.Equiv

/-!
# UniswapV3Pool benchmark correctness stub

Parameterized over the pool's immutable values `v`: the deployed runtime is the template patched
with `v`, and runtime equivalence is stated against `contract v`.  Proofs are the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolCorrect (v : PoolImmutables) {code : ByteArray}
    (hcode : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    runtimeEquivalence (config v) code (contract v) := by
  sorry

theorem uniswapV3PoolContractCorrect (v : PoolImmutables) {code : ByteArray}
    (hcode : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) uniswapV3PoolCreationBytecode code (contract v)
      (runtimeCodeOf uniswapV3PoolBytecode) :=
  contractEquivalenceWith.intro (uniswapV3PoolConstructorCorrect v) (uniswapV3PoolCorrect v hcode)

end Benchmarks.UniswapV3Pool
