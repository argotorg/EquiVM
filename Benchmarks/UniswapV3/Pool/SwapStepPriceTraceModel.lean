import Benchmarks.UniswapV3.Pool.SwapStepRecalcModel
import Benchmarks.UniswapV3.Pool.SwapStepPrefixTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

noncomputable def swapStepChoiceValid (a : SwapStepArgs) : Prop :=
  if swapStepReachTarget a then True
  else nextPriceValid (swapStepExactIn a) (swapStepNextArgs a)

noncomputable def swapStepRawPrice (a : SwapStepArgs) (currentRaw targetRaw : UInt256) : UInt256 :=
  if swapStepReachTarget a then targetRaw
  else nextPriceRawResult (swapStepExactIn a) (swapStepNextArgs a) currentRaw

noncomputable def swapStepPriceWords (a : SwapStepArgs)
    (currentRaw targetRaw liquidityRaw feeRaw : UInt256) : List UInt256 :=
  [(swapStepExactIn a).toUInt256, (swapStepZeroForOne a).toUInt256, ⟨0⟩,
   swapStepBeforeAmount a false, swapStepBeforeAmount a true,
   swapStepRawPrice a currentRaw targetRaw] ++
    swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw

noncomputable def swapStepUnpricedWords (a : SwapStepArgs)
    (currentRaw targetRaw liquidityRaw feeRaw : UInt256) : List UInt256 :=
  [(swapStepExactIn a).toUInt256, (swapStepZeroForOne a).toUInt256, ⟨0⟩,
   swapStepBeforeAmount a false, swapStepBeforeAmount a true, ⟨0⟩] ++
    swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw

theorem swapStepRawPrice_clean (a : SwapStepArgs) (currentRaw targetRaw : UInt256)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (ha : a.Fits) (hv : swapStepChoiceValid a) :
    UInt256.land (swapStepRawPrice a currentRaw targetRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
      swapStepPrice a := by
  cases hr : swapStepReachTarget a
  · have hn : nextPriceValid (swapStepExactIn a) (swapStepNextArgs a) := by
      simpa only [swapStepChoiceValid, hr, Bool.false_eq_true, if_false] using hv
    simpa only [swapStepRawPrice, swapStepPrice, hr, Bool.false_eq_true, if_false] using
      nextPriceResult_clean (swapStepExactIn a) (swapStepNextArgs a) currentRaw
        (swapStepNextArgs_fits a ha) hn.2 hc
  · simpa only [swapStepRawPrice, swapStepPrice, hr, if_true] using ht

theorem swapStepReachTarget_true (a : SwapStepArgs) (h : swapStepReachTarget a = true) :
    (swapStepInitialDelta a).toNat ≤ (swapStepBudget a).toNat := by
  simpa only [swapStepReachTarget, decide_eq_true_eq] using h

theorem swapStepReachTarget_false (a : SwapStepArgs) (h : swapStepReachTarget a = false) :
    (swapStepBudget a).toNat < (swapStepInitialDelta a).toNat := by
  have hh : ¬(swapStepInitialDelta a).toNat ≤ (swapStepBudget a).toNat := by
    simpa only [swapStepReachTarget, decide_eq_false_iff_not] using h
  omega

end Benchmarks.UniswapV3.Pool
