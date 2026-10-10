import Benchmarks.UniswapV4PoolManager.SwapStepSelectFrame
import Benchmarks.UniswapV4PoolManager.SwapStepDeltaSource
import Benchmarks.UniswapV4PoolManager.SwapStepWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapStepOutputStmts : List Stmt :=
  [swapStepDeltaStmt "sqrtPriceTargetX96" "amountOut" false, swapStepOutputSelectStmt,
   swapStepDeltaStmt "sqrtPriceNextX96" "amountIn" true] ++ swapStepComputedFeeStmts "__c12"

def swapStepOutputFrame (f : Frame) (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) : Frame :=
  let desired := swapStepDeltaWord price target liquidity false zeroForOne
  let f1 := amountDeltaFrame f "amountOut" desired
  let f2 := swapStepOutputSelectFrame f1 price target liquidity remaining desired zeroForOne
  let f3 := amountDeltaFrame f2 "amountIn" (swapStepOutputWords price target liquidity remaining fee zeroForOne).amountIn
  swapStepComputedFeeFrame f3 "__c12" (swapStepOutputWords price target liquidity remaining fee zeroForOne).amountIn fee

theorem swapStepOutputSource {f : Frame} {evm : EVM.State}
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
    ExecBlock config f evm swapStepOutputStmts
      (if swapStepOutputFits price target liquidity remaining fee zeroForOne then
        .ok (swapStepOutputFrame f price target liquidity remaining fee zeroForOne) evm else .reverted) := by
  let desired := swapStepDeltaWord price target liquidity false zeroForOne
  let f1 := amountDeltaFrame f "amountOut" desired
  let f2 := swapStepOutputSelectFrame f1 price target liquidity remaining desired zeroForOne
  let amountIn := (swapStepOutputWords price target liquidity remaining fee zeroForOne).amountIn
  let f3 := amountDeltaFrame f2 "amountIn" amountIn
  have hget1 (name : Ident) (hd : ("amount" == name) = false) (ho : ("amountOut" == name) = false) :
      f1.locals.get? name = f.locals.get? name := amountDeltaFrame_get _ _ _ _ ho hd
  have h0 := swapStepDeltaSource (evm := evm) "sqrtPriceTargetX96" "amountOut" false zeroForOne
    hc hp ht hs htr hl hb ho (by decide)
  by_cases h0fit : swapStepDeltaFits price target liquidity false zeroForOne
  · rw [if_pos h0fit] at h0
    have h1 := swapStepOutputSelectSource (f := f1) (evm := evm) zeroForOne hc hp
      ((hget1 _ (by decide) (by decide)).trans hs) ((hget1 _ (by decide) (by decide)).trans htr)
      ((hget1 _ (by decide) (by decide)).trans hl) ((hget1 _ (by decide) (by decide)).trans hr)
      ((hget1 _ (by decide) (by decide)).trans hb) (store_get_self _ _ _)
      ((hget1 _ (by decide) (by decide)).trans hn)
    by_cases h1fit : swapStepOutputSelectFits price liquidity remaining desired zeroForOne
    · rw [if_pos h1fit] at h1
      have hnc : (swapStepSelectedPrice price target liquidity remaining desired false zeroForOne).toNat < 2^160 :=
        swapStepOutputSelectedPrice_canonical (price := price) (target := target) (liquidity := liquidity)
          (remaining := remaining) (desired := desired) hp ht h1fit
      have hget2 (name : Ident) (hd : ("amount" == name) = false) (ho : ("amountOut" == name) = false)
          (hn : ("sqrtPriceNextX96" == name) = false) (hp : ("__c9" == name) = false) :
          f2.locals.get? name = f.locals.get? name :=
        (swapStepOutputSelectFrame_get _ _ _ _ _ _ _ _ hn ho hp).trans (hget1 name hd ho)
      have hc2 : f2.contract = contract := (swapStepOutputSelectFrame_contract _ _ _ _ _ _ _).trans hc
      have h2 := swapStepDeltaSource (f := f2) (evm := evm) "sqrtPriceNextX96" "amountIn" true zeroForOne hc2 hp hnc
        ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hs)
        (swapStepOutputSelectFrame_next _ _ _ _ _ _ _)
        ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hl)
        ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hb)
        ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hi) (by decide)
      by_cases h2fit : swapStepDeltaFits price
          (swapStepSelectedPrice price target liquidity remaining desired false zeroForOne) liquidity true zeroForOne
      · rw [if_pos h2fit] at h2
        have h3 := swapStepComputedFeeSource (f := f3) (evm := evm) "__c12" hc2 (store_get_self _ _ _)
          ((amountDeltaFrame_get _ _ _ _ (by decide) (by decide)).trans
            ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hfee))
          ((amountDeltaFrame_get _ _ _ _ (by decide) (by decide)).trans
            ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hfa)) (by decide)
        by_cases h3fit : swapStepFeeFits amountIn fee
        · rw [if_pos h3fit] at h3
          have hfit : swapStepOutputFits price target liquidity remaining fee zeroForOne := ⟨h0fit, h1fit, h2fit, h3fit⟩
          rw [if_pos hfit]
          exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2 h3))
        · rw [if_neg h3fit] at h3
          rw [if_neg (show ¬swapStepOutputFits price target liquidity remaining fee zeroForOne from fun h => h3fit h.2.2.2)]
          exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2 h3))
      · rw [if_neg h2fit] at h2
        rw [if_neg (show ¬swapStepOutputFits price target liquidity remaining fee zeroForOne from fun h => h2fit h.2.2.1)]
        exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consRevert h2))
    · rw [if_neg h1fit] at h1
      rw [if_neg (show ¬swapStepOutputFits price target liquidity remaining fee zeroForOne from fun h => h1fit h.2.1)]
      exact ExecBlock.consNormal h0 (ExecBlock.consRevert h1)
  · rw [if_neg h0fit] at h0
    rw [if_neg (show ¬swapStepOutputFits price target liquidity remaining fee zeroForOne from fun h => h0fit h.1)]
    exact ExecBlock.consRevert h0

end Benchmarks.UniswapV4PoolManager
