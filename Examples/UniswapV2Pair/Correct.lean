import Examples.UniswapV2Pair.Bytecode
import Examples.UniswapV2Pair.Allowance
import Examples.UniswapV2Pair.BalanceOf
import Examples.UniswapV2Pair.Decimals
import Examples.UniswapV2Pair.DomainSeparator
import Examples.UniswapV2Pair.Factory
import Examples.UniswapV2Pair.GetReserves
import Examples.UniswapV2Pair.KLast
import Examples.UniswapV2Pair.MinimumLiquidity
import Examples.UniswapV2Pair.Nonces
import Examples.UniswapV2Pair.PermitTypehash
import Examples.UniswapV2Pair.Price0CumulativeLast
import Examples.UniswapV2Pair.Price1CumulativeLast
import Examples.UniswapV2Pair.Token0
import Examples.UniswapV2Pair.Token1
import Examples.UniswapV2Pair.TotalSupply
import Solm.Equiv

/-!
# UniswapV2Pair benchmark correctness stub

The source, ABI, optimized runtime bytecode, and Solm specification are present.  The equivalence
proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace UniswapV2Pair

theorem uniswapV2PairCorrect :
    runtimeEquivalence!?! config uniswapV2PairBytecode contract := by
  sorry

end UniswapV2Pair
