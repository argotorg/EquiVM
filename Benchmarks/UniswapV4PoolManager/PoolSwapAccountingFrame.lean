import Benchmarks.UniswapV4PoolManager.PoolSwapAmountSource
import Benchmarks.UniswapV4PoolManager.PoolSwapFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapAmountFrame_contract (f : Frame) (s : PoolSwapStepWords)
    (specified remaining calculated : UInt256) :
    (poolSwapAmountFrame f s specified remaining calculated).contract = f.contract := by
  unfold poolSwapAmountFrame
  split <;> simp only [poolSwapInputAmountFrame, poolSwapOutputAmountFrame, valueLocal_contract]

theorem poolSwapAmountFrame_get (f : Frame) (s : PoolSwapStepWords)
    (specified remaining calculated : UInt256) (key : Ident)
    (h16 : ("__c16" == key) = false) (h17 : ("__c17" == key) = false)
    (h18 : ("__c18" == key) = false) (h19 : ("__c19" == key) = false)
    (hr : ("amountSpecifiedRemaining" == key) = false) (hc : ("amountCalculated" == key) = false) :
    (poolSwapAmountFrame f s specified remaining calculated).locals.get? key = f.locals.get? key := by
  unfold poolSwapAmountFrame
  split <;> simp only [poolSwapInputAmountFrame, poolSwapOutputAmountFrame,
    valueLocal_get, h16, h17, h18, h19, hr, hc, Bool.false_eq_true, if_false]

theorem poolSwapAmountFrame_remaining (f : Frame) (s : PoolSwapStepWords)
    (specified remaining calculated : UInt256) :
    (poolSwapAmountFrame f s specified remaining calculated).locals.get? "amountSpecifiedRemaining" =
      some (.int (EVM.signed (poolSwapRemainingAfter s specified remaining))) := by
  unfold poolSwapAmountFrame poolSwapRemainingAfter
  split <;> exact (store_get_ne2 _ _ _ (by decide) (by decide)).trans (store_get_self _ _ _)

theorem poolSwapAmountFrame_calculated (f : Frame) (s : PoolSwapStepWords)
    (specified remaining calculated : UInt256) :
    (poolSwapAmountFrame f s specified remaining calculated).locals.get? "amountCalculated" =
      some (.int (EVM.signed (poolSwapCalculatedAfter s specified calculated))) := by
  unfold poolSwapAmountFrame poolSwapCalculatedAfter
  split <;> exact store_get_self _ _ _

theorem poolSwapGrowthFrame_contract (f : Frame) (s : PoolSwapStepWords) (liquidity : UInt256) :
    (poolSwapGrowthFrame f s liquidity).contract = f.contract := by
  unfold poolSwapGrowthFrame
  split <;> simp only [valueLocal_contract, wordLocal_contract]

theorem poolSwapGrowthFrame_get (f : Frame) (s : PoolSwapStepWords) (liquidity : UInt256) (key : Ident)
    (hc : ("__c20" == key) = false) (hs : ("step" == key) = false) :
    (poolSwapGrowthFrame f s liquidity).locals.get? key = f.locals.get? key := by
  unfold poolSwapGrowthFrame
  split <;> simp only [wordLocal_get, valueLocal_get, hc, hs, Bool.false_eq_true, if_false]

theorem poolSwapGrowthFrame_step {f : Frame} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) (liquidity : UInt256) :
    (poolSwapGrowthFrame f s liquidity).locals.get? "step" =
      some (poolSwapStepValue (poolSwapGrowthStep s liquidity)) := by
  by_cases hz : liquidity = ⟨0⟩
  · simpa only [poolSwapGrowthFrame, poolSwapGrowthStep, if_pos hz] using hs
  · rw [poolSwapGrowthFrame, if_neg hz]
    exact store_get_self _ _ _

theorem poolSwapProtocolFrame_amount {f : Frame} {s : PoolSwapStepWords} {amount : UInt256}
    (ha : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat))) (fee protocol : UInt256) :
    (poolSwapProtocolFrame f s fee protocol amount).locals.get? "amountToProtocol" =
      some (.int (Int.ofNat (poolSwapProtocolAmount s fee protocol amount).toNat)) := by
  by_cases hz : protocol = ⟨0⟩
  · simpa only [poolSwapProtocolFrame, poolSwapProtocolAmount, if_pos hz] using ha
  · rw [poolSwapProtocolFrame, if_neg hz]
    exact store_get_self _ _ _

end Benchmarks.UniswapV4PoolManager
