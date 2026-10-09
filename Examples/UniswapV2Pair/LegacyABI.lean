import Examples.UniswapV2Pair.Spec
import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-!
# Legacy address ABI helpers

Uniswap V2 Pair was compiled by solc 0.5.16 with optimizer enabled. Its static external wrappers
mask address calldata words instead of rejecting non-canonical high bits. The generic decoder facts
for this legacy mode now live in `Reasoning.ABI`; this module remains as the compatibility import
used by the Uniswap proof files.
-/

end UniswapV2Pair
