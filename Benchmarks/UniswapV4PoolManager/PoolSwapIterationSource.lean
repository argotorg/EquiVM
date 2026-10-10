import Benchmarks.UniswapV4PoolManager.PoolSwapScanComputeSource
import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapIterationResult (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) (remaining calculated fee protocol amount : UInt256) : ExecResult :=
  let scan := poolSwapScanStep s evm id r p
  let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
  let clamped := {scan with tickNext := tickClampWord scan.tickNext}
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  let f1 := poolSwapComputeFrame (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) scan)
    clamped r p next remaining fee
  if swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee then
    poolSwapAccountingResult f1 evm id (poolSwapComputeStep clamped next w) {r with price := w.next}
      p remaining calculated fee protocol amount
  else .reverted

theorem poolSwapIterationSource {f : Frame} {evm : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {remaining calculated fee protocol amount : UInt256}
    (hf : f.contract = contract) (htick : (EVM.signed r.tick).natAbs < 2^255)
    (hrc : r.price.toNat < 2^160) (hlc : p.priceLimit.toNat < 2^160)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hself : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne))
    (hrem : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hcalc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated)))
    (hfee : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hprot : f.locals.get? "protocolFee" = some (.int (Int.ofNat protocol.toNat)))
    (ha : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat))) :
    ExecBlock config f evm poolSwapLoopBody
      (poolSwapIterationResult f evm id s r p remaining calculated fee protocol amount) := by
  let scan := poolSwapScanStep s evm id r p
  let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
  let clamped := {scan with tickNext := tickClampWord scan.tickNext}
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  let f0 := tickClampPriceFrame (poolSwapScanFrame f s evm id r p) scan
  let f1 := poolSwapComputeFrame f0 clamped r p next remaining fee
  have hpre := poolSwapScanComputeSource (evm := evm) hf htick hrc hlc hs hr hp hself hz hrem hfee
  dsimp only at hpre
  change ExecBlock config f evm _ (if swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit)
    r.liquidity remaining fee then poolSwapAccountingResult f1 evm id (poolSwapComputeStep clamped next w)
      {r with price := w.next} p remaining calculated fee protocol amount else .reverted)
  by_cases hfit : swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  · rw [if_pos hfit] at hpre ⊢
    have hf0 : f0.contract = contract := by
      simp only [f0, tickClampPriceFrame, valueLocal_contract, tickClampFrame_contract, poolSwapScanFrame_contract, hf]
    have hf1 : f1.contract = contract := (poolSwapComputeFrame_contract ..).trans hf0
    have hget (key : Ident) (hstep : ("step" == key) = false) (hresult : ("result" == key) = false)
        (h12 : ("__c12" == key) = false) (h13 : ("__c13" == key) = false)
        (h14 : ("__c14" == key) = false) (h15 : ("__c15" == key) = false)
        (halias : (poolSwapBitmapAlias == key) = false) : f1.locals.get? key = f.locals.get? key :=
      (poolSwapComputeFrame_get f0 clamped r p next remaining fee key hstep hresult h14 h15).trans
        (poolSwapScanPriceFrame_get f s evm id r p key hstep halias h12 h13)
    have htail := poolSwapAccountingSource (evm := evm) (s := poolSwapComputeStep clamped next w)
      (r := {r with price := w.next}) hf1 (poolSwapComputeFrame_step ..) (poolSwapComputeFrame_result ..)
      ((hget "params" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp)
      ((hget "self" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hself)
      ((hget "zeroForOne" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz)
      ((hget "amountSpecifiedRemaining" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrem)
      ((hget "amountCalculated" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcalc)
      ((hget "swapFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfee)
      ((hget "protocolFee" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hprot)
      ((hget "amountToProtocol" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha)
    simpa only [List.take_append_drop] using execBlock_append hpre htail
  · rw [if_neg hfit] at hpre ⊢
    have hfull := execBlock_reverted_append (s2 := poolSwapLoopBody.drop 15) hpre
    simpa only [List.take_append_drop] using hfull

end Benchmarks.UniswapV4PoolManager
