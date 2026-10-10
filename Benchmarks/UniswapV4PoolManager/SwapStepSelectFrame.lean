import Benchmarks.UniswapV4PoolManager.SwapStepInputSelectSource
import Benchmarks.UniswapV4PoolManager.SwapStepOutputSelectSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepComputedFeeFrame_eq (f : Frame) (name : Ident) (amount fee : UInt256) :
    swapStepComputedFeeFrame f name amount fee =
      wordLocal (wordLocal f name (swapStepFeeWord amount fee)) "feeAmount" (swapStepFeeWord amount fee) := rfl

theorem swapStepPriceFrame_eq (f : Frame) (price liquidity amount : UInt256) (input zeroForOne : Bool) :
    swapStepPriceFrame f price liquidity amount input zeroForOne =
      wordLocal (wordLocal f (swapStepPriceRet input) (nextPriceWord price liquidity amount input zeroForOne))
        "sqrtPriceNextX96" (nextPriceWord price liquidity amount input zeroForOne) := rfl

theorem swapStepInputSelectFrame_contract (f : Frame) (price target liquidity remaining available desired fee : UInt256)
    (zeroForOne : Bool) :
    (swapStepInputSelectFrame f price target liquidity remaining available desired fee zeroForOne).contract = f.contract := by
  unfold swapStepInputSelectFrame
  split
  · unfold swapStepTargetFeeFrame
    split <;> rfl
  · rfl

theorem swapStepInputSelectFrame_get (f : Frame) (price target liquidity remaining available desired fee : UInt256)
    (zeroForOne : Bool) (name : Ident)
    (hn : ("sqrtPriceNextX96" == name) = false) (ha : ("amountIn" == name) = false)
    (hf : ("feeAmount" == name) = false) (hc : ("computedFee" == name) = false) (hp : ("__c4" == name) = false) :
    (swapStepInputSelectFrame f price target liquidity remaining available desired fee zeroForOne).locals.get? name =
      f.locals.get? name := by
  unfold swapStepInputSelectFrame
  split
  · unfold swapStepTargetFeeFrame
    split <;> simp only [swapStepComputedFeeFrame_eq, wordLocal_get, hn, hf, hc, Bool.false_eq_true, if_false]
  · simp only [swapStepInputPartialFrame, swapStepPriceFrame_eq, swapStepPriceRet, if_true,
      wordLocal_get, hn, ha, hf, hp, Bool.false_eq_true, if_false]

theorem swapStepInputSelectFrame_next (f : Frame) (price target liquidity remaining available desired fee : UInt256)
    (zeroForOne : Bool) :
    (swapStepInputSelectFrame f price target liquidity remaining available desired fee zeroForOne).locals.get? "sqrtPriceNextX96" =
      some (.int (Int.ofNat (swapStepSelectedPrice price target liquidity available desired true zeroForOne).toNat)) := by
  unfold swapStepInputSelectFrame swapStepSelectedPrice
  split
  · unfold swapStepTargetFeeFrame
    split <;> simp only [swapStepComputedFeeFrame_eq, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  · simp only [swapStepInputPartialFrame, swapStepPriceFrame_eq, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]

theorem swapStepInputSelectFrame_amount {f : Frame} (price target liquidity remaining available desired fee : UInt256)
    (zeroForOne : Bool) (ha : f.locals.get? "amountIn" = some (.int (Int.ofNat desired.toNat))) :
    (swapStepInputSelectFrame f price target liquidity remaining available desired fee zeroForOne).locals.get? "amountIn" =
      some (.int (Int.ofNat (swapStepSelectedAmount available desired).toNat)) := by
  unfold swapStepInputSelectFrame swapStepSelectedAmount
  split
  · unfold swapStepTargetFeeFrame
    split <;> simp only [swapStepComputedFeeFrame_eq, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
  · simp only [swapStepInputPartialFrame, swapStepPriceFrame_eq, swapStepPriceRet, if_true, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]

theorem swapStepInputSelectFrame_fee (f : Frame) (price target liquidity remaining available desired fee : UInt256)
    (zeroForOne : Bool) :
    (swapStepInputSelectFrame f price target liquidity remaining available desired fee zeroForOne).locals.get? "feeAmount" =
      some (.int (Int.ofNat (swapStepSelectedFee remaining available desired fee).toNat)) := by
  unfold swapStepInputSelectFrame swapStepSelectedFee
  split
  · unfold swapStepTargetFeeFrame swapStepTargetFeeWord
    split <;> simp only [swapStepComputedFeeFrame_eq, wordLocal_get, beq_self_eq_true, if_true]
  · exact store_get_self _ _ _

theorem swapStepOutputSelectFrame_contract (f : Frame) (price target liquidity remaining desired : UInt256)
    (zeroForOne : Bool) :
    (swapStepOutputSelectFrame f price target liquidity remaining desired zeroForOne).contract = f.contract := by
  unfold swapStepOutputSelectFrame
  split <;> rfl

theorem swapStepOutputSelectFrame_get (f : Frame) (price target liquidity remaining desired : UInt256)
    (zeroForOne : Bool) (name : Ident)
    (hn : ("sqrtPriceNextX96" == name) = false) (ha : ("amountOut" == name) = false) (hp : ("__c9" == name) = false) :
    (swapStepOutputSelectFrame f price target liquidity remaining desired zeroForOne).locals.get? name =
      f.locals.get? name := by
  unfold swapStepOutputSelectFrame
  split <;> simp only [swapStepPriceFrame_eq, swapStepPriceRet, Bool.false_eq_true, if_false,
    wordLocal_get, hn, ha, hp, if_false]

theorem swapStepOutputSelectFrame_next (f : Frame) (price target liquidity remaining desired : UInt256)
    (zeroForOne : Bool) :
    (swapStepOutputSelectFrame f price target liquidity remaining desired zeroForOne).locals.get? "sqrtPriceNextX96" =
      some (.int (Int.ofNat (swapStepSelectedPrice price target liquidity remaining desired false zeroForOne).toNat)) := by
  unfold swapStepOutputSelectFrame swapStepSelectedPrice
  split <;> simp only [swapStepPriceFrame_eq, wordLocal_get, beq_self_eq_true, if_true]

theorem swapStepOutputSelectFrame_amount {f : Frame} (price target liquidity remaining desired : UInt256)
    (zeroForOne : Bool) (ha : f.locals.get? "amountOut" = some (.int (Int.ofNat desired.toNat))) :
    (swapStepOutputSelectFrame f price target liquidity remaining desired zeroForOne).locals.get? "amountOut" =
      some (.int (Int.ofNat (swapStepSelectedAmount remaining desired).toNat)) := by
  unfold swapStepOutputSelectFrame swapStepSelectedAmount
  split <;> simp only [swapStepPriceFrame_eq, swapStepPriceRet, Bool.false_eq_true, if_false,
    wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]

end Benchmarks.UniswapV4PoolManager
