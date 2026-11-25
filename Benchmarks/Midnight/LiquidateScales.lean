import Benchmarks.Midnight.MulDiv

/-! The price scale used by liquidation's collateral conversions. -/

open Ethereum

namespace Benchmarks.Midnight

def liquidatePriceScale : UInt256 := UInt256.ofNat 1000000000000000000000000000000000000

end Benchmarks.Midnight
