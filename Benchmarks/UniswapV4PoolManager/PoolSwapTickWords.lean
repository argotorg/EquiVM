import Benchmarks.UniswapV4PoolManager.PoolSwapTickSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapTickResultWords (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) : PoolSwapResultWords :=
  if r.price = s.priceNext then
    {r with
      tick := poolSwapBoundaryTick zeroForOne s.tickNext
      liquidity := if s.initialized then poolSwapCrossLiquidity evm id s zeroForOne r.liquidity else r.liquidity}
  else if r.price = s.priceStart then r
  else match tickPriceResult r.price with
    | none => r
    | some tick => {r with tick := tick}

end Benchmarks.UniswapV4PoolManager
