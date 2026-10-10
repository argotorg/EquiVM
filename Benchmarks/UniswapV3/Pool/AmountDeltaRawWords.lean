import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.WordSubMasks
import Benchmarks.UniswapV3.Pool.NextSqrt0Model

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem amountDeltaRawDifference (a : AmountDeltaArgs) (upperRaw lowerRaw : UInt256)
    (hu : UInt256.land upperRaw (UInt256.ofNat (2 ^ 160 - 1)) = amountDeltaUpper a)
    (hl : UInt256.land lowerRaw (UInt256.ofNat (2 ^ 160 - 1)) = amountDeltaLower a) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1)) (UInt256.sub upperRaw lowerRaw) = amountDeltaDifference a := by
  rw [amountDeltaMask160, u256_land_comm,
    ← wordSub_land_both ⟨160, by decide⟩ upperRaw lowerRaw _ (by decide), hu, hl]
  rfl

theorem amountDeltaRawNumerator (a : AmountDeltaArgs) (liquidityRaw : UInt256)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity) :
    UInt256.land (UInt256.shiftLeft liquidityRaw (UInt256.ofNat 96))
      (UInt256.ofNat 26959946667150639794667015087019630673557916260026308143510066298880) =
      amountDeltaNumerator a :=
  nextSqrt0NumeratorClean liquidityRaw ⟨a.sqrtA, a.liquidity, ⟨0⟩, false⟩ hl

end Benchmarks.UniswapV3.Pool
