import Benchmarks.UniswapV4PoolManager.SwapStepSelectFrame
import Benchmarks.UniswapV4PoolManager.SwapStepDeltaSource
import Benchmarks.UniswapV4PoolManager.SwapStepWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapStepInputStmts : List Stmt :=
  [swapStepAvailableStmt, swapStepDeltaStmt "sqrtPriceTargetX96" "amountIn" true,
   swapStepInputSelectStmt, swapStepDeltaStmt "sqrtPriceNextX96" "amountOut" false]

def swapStepInputFrame (f : Frame) (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) : Frame :=
  let available := swapStepAvailableWord remaining fee
  let desired := swapStepDeltaWord price target liquidity true zeroForOne
  let f1 := wordLocal f "amountRemainingLessFee" available
  let f2 := amountDeltaFrame f1 "amountIn" desired
  let f3 := swapStepInputSelectFrame f2 price target liquidity remaining available desired fee zeroForOne
  amountDeltaFrame f3 "amountOut" (swapStepInputWords price target liquidity remaining fee zeroForOne).amountOut

theorem swapStepInputSource {f : Frame} {evm : EVM.State}
    {price target liquidity remaining fee : UInt256} {oldNext oldIn oldOut oldFee : Value}
    (zeroForOne : Bool) (hc : f.contract = contract) (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hs : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (htr : f.locals.get? "sqrtPriceTargetX96" = some (.int (Int.ofNat target.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (hfee : f.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat)))
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hn : f.locals.get? "sqrtPriceNextX96" = some oldNext)
    (hi : f.locals.get? "amountIn" = some oldIn) (ho : f.locals.get? "amountOut" = some oldOut)
    (hfa : f.locals.get? "feeAmount" = some oldFee) :
    ExecBlock config f evm swapStepInputStmts
      (if swapStepInputFits price target liquidity remaining fee zeroForOne then
        .ok (swapStepInputFrame f price target liquidity remaining fee zeroForOne) evm else .reverted) := by
  let available := swapStepAvailableWord remaining fee
  let desired := swapStepDeltaWord price target liquidity true zeroForOne
  let f1 := wordLocal f "amountRemainingLessFee" available
  let f2 := amountDeltaFrame f1 "amountIn" desired
  let f3 := swapStepInputSelectFrame f2 price target liquidity remaining available desired fee zeroForOne
  have hget1 (name : Ident) (hne : ("amountRemainingLessFee" == name) = false) :
      f1.locals.get? name = f.locals.get? name := store_get_ne _ _ hne
  have hget2 (name : Ident) (ha : ("amountRemainingLessFee" == name) = false)
      (hd : ("amount" == name) = false) (hi : ("amountIn" == name) = false) :
      f2.locals.get? name = f.locals.get? name :=
    (amountDeltaFrame_get _ _ _ _ hi hd).trans (hget1 name ha)
  have h0 := swapStepAvailableSource (evm := evm) hc hr hfee
  by_cases h0fit : swapStepAvailableFits remaining fee
  · rw [if_pos h0fit] at h0
    have h1 := swapStepDeltaSource (f := f1) (evm := evm) "sqrtPriceTargetX96" "amountIn" true zeroForOne hc hp ht
      ((hget1 _ (by decide)).trans hs) ((hget1 _ (by decide)).trans htr)
      ((hget1 _ (by decide)).trans hl) ((hget1 _ (by decide)).trans hb)
      ((hget1 _ (by decide)).trans hi) (by decide)
    by_cases h1fit : swapStepDeltaFits price target liquidity true zeroForOne
    · rw [if_pos h1fit] at h1
      have havi : f2.locals.get? "amountRemainingLessFee" = some (.int (Int.ofNat available.toNat)) :=
        (amountDeltaFrame_get _ _ _ _ (by decide) (by decide)).trans (store_get_self _ _ _)
      have h2 := swapStepInputSelectSource (f := f2) (evm := evm) zeroForOne hc hp
        ((hget2 _ (by decide) (by decide) (by decide)).trans hs)
        ((hget2 _ (by decide) (by decide) (by decide)).trans htr)
        ((hget2 _ (by decide) (by decide) (by decide)).trans hl)
        ((hget2 _ (by decide) (by decide) (by decide)).trans hr) havi
        ((hget2 _ (by decide) (by decide) (by decide)).trans hb) (store_get_self _ _ _)
        ((hget2 _ (by decide) (by decide) (by decide)).trans hn)
        ((hget2 _ (by decide) (by decide) (by decide)).trans hfa)
        ((hget2 _ (by decide) (by decide) (by decide)).trans hfee)
      by_cases h2fit : swapStepInputSelectFits price liquidity available desired fee zeroForOne
      · rw [if_pos h2fit] at h2
        have hnc : (swapStepSelectedPrice price target liquidity available desired true zeroForOne).toNat < 2^160 :=
          swapStepInputSelectedPrice_canonical (price := price) (target := target) (liquidity := liquidity)
            (available := available) (desired := desired) (fee := fee) hp ht h2fit
        have hget3 (name : Ident) (ha : ("amountRemainingLessFee" == name) = false)
            (hd : ("amount" == name) = false) (hi : ("amountIn" == name) = false)
            (hn : ("sqrtPriceNextX96" == name) = false) (hf : ("feeAmount" == name) = false)
            (hcf : ("computedFee" == name) = false) (hp : ("__c4" == name) = false) :
            f3.locals.get? name = f.locals.get? name :=
          (swapStepInputSelectFrame_get _ _ _ _ _ _ _ _ _ _ hn hi hf hcf hp).trans (hget2 name ha hd hi)
        have hc3 : f3.contract = contract := (swapStepInputSelectFrame_contract _ _ _ _ _ _ _ _ _).trans hc
        have h3 := swapStepDeltaSource (f := f3) (evm := evm) "sqrtPriceNextX96" "amountOut" false zeroForOne hc3 hp hnc
          ((hget3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs)
          (swapStepInputSelectFrame_next _ _ _ _ _ _ _ _ _)
          ((hget3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl)
          ((hget3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb)
          ((hget3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ho) (by decide)
        by_cases h3fit : swapStepDeltaFits price
            (swapStepSelectedPrice price target liquidity available desired true zeroForOne) liquidity false zeroForOne
        · rw [if_pos h3fit] at h3
          have hfit : swapStepInputFits price target liquidity remaining fee zeroForOne := ⟨h0fit, h1fit, h2fit, h3fit⟩
          rw [if_pos hfit]
          exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (execBlock_singleton h3)))
        · rw [if_neg h3fit] at h3
          rw [if_neg (show ¬swapStepInputFits price target liquidity remaining fee zeroForOne from fun h => h3fit h.2.2.2)]
          exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consRevert h3)))
      · rw [if_neg h2fit] at h2
        rw [if_neg (show ¬swapStepInputFits price target liquidity remaining fee zeroForOne from fun h => h2fit h.2.2.1)]
        exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consRevert h2))
    · rw [if_neg h1fit] at h1
      rw [if_neg (show ¬swapStepInputFits price target liquidity remaining fee zeroForOne from fun h => h1fit h.2.1)]
      exact ExecBlock.consNormal h0 (ExecBlock.consRevert h1)
  · rw [if_neg h0fit] at h0
    rw [if_neg (show ¬swapStepInputFits price target liquidity remaining fee zeroForOne from fun h => h0fit h.1)]
    exact ExecBlock.consRevert h0

end Benchmarks.UniswapV4PoolManager
