import Benchmarks.UniswapV4PoolManager.SwapStepSelectWords
import Benchmarks.UniswapV4PoolManager.SwapStepDeltaWords

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

structure SwapStepWords where
  next : UInt256
  amountIn : UInt256
  amountOut : UInt256
  fee : UInt256

def swapStepInputWords (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) : SwapStepWords :=
  let available := swapStepAvailableWord remaining fee
  let desired := swapStepDeltaWord price target liquidity true zeroForOne
  let next := swapStepSelectedPrice price target liquidity available desired true zeroForOne
  {next, amountIn := swapStepSelectedAmount available desired,
   amountOut := swapStepDeltaWord price next liquidity false zeroForOne,
   fee := swapStepSelectedFee remaining available desired fee}

def swapStepInputFits (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) : Prop :=
  swapStepAvailableFits remaining fee ∧ swapStepDeltaFits price target liquidity true zeroForOne ∧
    swapStepInputSelectFits price liquidity (swapStepAvailableWord remaining fee)
      (swapStepDeltaWord price target liquidity true zeroForOne) fee zeroForOne ∧
    swapStepDeltaFits price (swapStepInputWords price target liquidity remaining fee zeroForOne).next liquidity false zeroForOne
instance (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) :
    Decidable (swapStepInputFits price target liquidity remaining fee zeroForOne) := by
  unfold swapStepInputFits
  infer_instance

def swapStepOutputWords (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) : SwapStepWords :=
  let desired := swapStepDeltaWord price target liquidity false zeroForOne
  let next := swapStepSelectedPrice price target liquidity remaining desired false zeroForOne
  let amountIn := swapStepDeltaWord price next liquidity true zeroForOne
  {next, amountIn, amountOut := swapStepSelectedAmount remaining desired, fee := swapStepFeeWord amountIn fee}

def swapStepOutputFits (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) : Prop :=
  swapStepDeltaFits price target liquidity false zeroForOne ∧
    swapStepOutputSelectFits price liquidity remaining (swapStepDeltaWord price target liquidity false zeroForOne) zeroForOne ∧
    swapStepDeltaFits price (swapStepOutputWords price target liquidity remaining fee zeroForOne).next liquidity true zeroForOne ∧
    swapStepFeeFits (swapStepOutputWords price target liquidity remaining fee zeroForOne).amountIn fee
instance (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) :
    Decidable (swapStepOutputFits price target liquidity remaining fee zeroForOne) := by
  unfold swapStepOutputFits
  infer_instance

theorem swapStepInputWords_next_canonical {price target liquidity remaining fee : UInt256} {zeroForOne : Bool}
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hf : swapStepInputFits price target liquidity remaining fee zeroForOne) :
    (swapStepInputWords price target liquidity remaining fee zeroForOne).next.toNat < 2^160 :=
  swapStepInputSelectedPrice_canonical (price := price) (target := target) (liquidity := liquidity)
    (available := swapStepAvailableWord remaining fee)
    (desired := swapStepDeltaWord price target liquidity true zeroForOne) (fee := fee) hp ht hf.2.2.1

theorem swapStepOutputWords_next_canonical {price target liquidity remaining fee : UInt256} {zeroForOne : Bool}
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hf : swapStepOutputFits price target liquidity remaining fee zeroForOne) :
    (swapStepOutputWords price target liquidity remaining fee zeroForOne).next.toNat < 2^160 :=
  swapStepOutputSelectedPrice_canonical (price := price) (target := target) (liquidity := liquidity)
    (remaining := remaining) (desired := swapStepDeltaWord price target liquidity false zeroForOne) hp ht hf.2.1

def swapStepDirection (price target : UInt256) : Bool := decide (target.toNat ≤ price.toNat)
def swapStepExactInput (remaining : UInt256) : Bool := decide (EVM.signed remaining < 0)

def swapStepFits (price target liquidity remaining fee : UInt256) : Prop :=
  if swapStepExactInput remaining then
    swapStepInputFits price target liquidity remaining fee (swapStepDirection price target)
  else swapStepOutputFits price target liquidity remaining fee (swapStepDirection price target)
instance (price target liquidity remaining fee : UInt256) :
    Decidable (swapStepFits price target liquidity remaining fee) := by
  unfold swapStepFits
  infer_instance

def swapStepWord (price target liquidity remaining fee : UInt256) : SwapStepWords :=
  if swapStepExactInput remaining then
    swapStepInputWords price target liquidity remaining fee (swapStepDirection price target)
  else swapStepOutputWords price target liquidity remaining fee (swapStepDirection price target)

theorem swapStepWord_next_canonical {price target liquidity remaining fee : UInt256}
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hf : swapStepFits price target liquidity remaining fee) :
    (swapStepWord price target liquidity remaining fee).next.toNat < 2^160 := by
  by_cases hi : swapStepExactInput remaining = true
  · simp only [swapStepFits, swapStepWord, if_pos hi] at hf ⊢
    exact swapStepInputWords_next_canonical hp ht hf
  · simp only [swapStepFits, swapStepWord, if_neg hi] at hf ⊢
    exact swapStepOutputWords_next_canonical hp ht hf

end Benchmarks.UniswapV4PoolManager
