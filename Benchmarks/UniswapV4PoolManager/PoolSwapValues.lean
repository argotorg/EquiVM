import Benchmarks.UniswapV4PoolManager.PoolSwapStepWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

structure PoolSwapResultWords where
  price : UInt256
  tick : UInt256
  liquidity : UInt256

structure PoolSwapParamsWords where
  amountSpecified : UInt256
  tickSpacing : UInt256
  zeroForOne : Bool
  priceLimit : UInt256
  lpFeeOverride : UInt256

def poolSwapResultValue (r : PoolSwapResultWords) : Value :=
  .struct "SwapResult" [("sqrtPriceX96", .int (Int.ofNat r.price.toNat)),
    ("tick", .int (EVM.signed r.tick)), ("liquidity", .int (Int.ofNat r.liquidity.toNat))]

def poolSwapParamsValue (p : PoolSwapParamsWords) : Value :=
  .struct "Pool_SwapParams" [("tickSpacing", .int (EVM.signed p.tickSpacing)),
    ("zeroForOne", .bool p.zeroForOne), ("amountSpecified", .int (EVM.signed p.amountSpecified)),
    ("sqrtPriceLimitX96", .int (Int.ofNat p.priceLimit.toNat)),
    ("lpFeeOverride", .int (Int.ofNat p.lpFeeOverride.toNat))]

end Benchmarks.UniswapV4PoolManager
