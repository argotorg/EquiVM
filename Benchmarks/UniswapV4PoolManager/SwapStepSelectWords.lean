import Benchmarks.UniswapV4PoolManager.SwapStepRemainingWords
import Benchmarks.UniswapV4PoolManager.NextPriceWords

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

def swapStepReachesTarget (available desired : UInt256) : Prop := desired.toNat ≤ available.toNat
instance (available desired : UInt256) : Decidable (swapStepReachesTarget available desired) :=
  inferInstanceAs (Decidable (_ ≤ _))

def swapStepSelectedAmount (available desired : UInt256) : UInt256 :=
  if swapStepReachesTarget available desired then desired else available

def swapStepSelectedPrice (price target liquidity available desired : UInt256) (input zeroForOne : Bool) : UInt256 :=
  if swapStepReachesTarget available desired then target
  else nextPriceWord price liquidity available input zeroForOne

def swapStepInputSelectFits (price liquidity available desired fee : UInt256) (zeroForOne : Bool) : Prop :=
  if swapStepReachesTarget available desired then swapStepTargetFeeFits desired fee
  else nextPriceFits price liquidity available true zeroForOne
instance (price liquidity available desired fee : UInt256) (zeroForOne : Bool) :
    Decidable (swapStepInputSelectFits price liquidity available desired fee zeroForOne) := by
  unfold swapStepInputSelectFits
  infer_instance

def swapStepSelectedFee (remaining available desired fee : UInt256) : UInt256 :=
  if swapStepReachesTarget available desired then swapStepTargetFeeWord desired fee
  else swapStepRemainingFeeWord remaining available

def swapStepOutputSelectFits (price liquidity remaining desired : UInt256) (zeroForOne : Bool) : Prop :=
  if swapStepReachesTarget remaining desired then True
  else nextPriceFits price liquidity remaining false zeroForOne
instance (price liquidity remaining desired : UInt256) (zeroForOne : Bool) :
    Decidable (swapStepOutputSelectFits price liquidity remaining desired zeroForOne) := by
  unfold swapStepOutputSelectFits
  infer_instance

theorem swapStepInputSelectedPrice_canonical {price target liquidity available desired fee : UInt256}
    {zeroForOne : Bool} (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hf : swapStepInputSelectFits price liquidity available desired fee zeroForOne) :
    (swapStepSelectedPrice price target liquidity available desired true zeroForOne).toNat < 2^160 := by
  by_cases hr : swapStepReachesTarget available desired
  · simpa only [swapStepSelectedPrice, if_pos hr] using ht
  · simp only [swapStepInputSelectFits, if_neg hr] at hf
    simpa only [swapStepSelectedPrice, if_neg hr] using
      nextPriceWord_canonical (price := price) (liquidity := liquidity) (amount := available)
        (input := true) (zeroForOne := zeroForOne) hp hf

theorem swapStepOutputSelectedPrice_canonical {price target liquidity remaining desired : UInt256}
    {zeroForOne : Bool} (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hf : swapStepOutputSelectFits price liquidity remaining desired zeroForOne) :
    (swapStepSelectedPrice price target liquidity remaining desired false zeroForOne).toNat < 2^160 := by
  by_cases hr : swapStepReachesTarget remaining desired
  · simpa only [swapStepSelectedPrice, if_pos hr] using ht
  · simp only [swapStepOutputSelectFits, if_neg hr] at hf
    simpa only [swapStepSelectedPrice, if_neg hr] using
      nextPriceWord_canonical (price := price) (liquidity := liquidity) (amount := remaining)
        (input := false) (zeroForOne := zeroForOne) hp hf

end Benchmarks.UniswapV4PoolManager
