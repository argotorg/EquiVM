import Benchmarks.UniswapV4PoolManager.PoolSwapScanSource
import Benchmarks.UniswapV4PoolManager.PoolSwapComputeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickClampFrame_get (f : Frame) (s : PoolSwapStepWords) (key : Ident)
    (hk : ("step" == key) = false) :
    (tickClampFrame f s).locals.get? key = f.locals.get? key := by
  unfold tickClampFrame tickClampUpperFrame tickClampLowerFrame
  split <;> split <;> simp only [valueLocal_get, hk, Bool.false_eq_true, if_false]

theorem poolSwapScanPriceFrame_get (f : Frame) (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) (key : Ident)
    (h0 : ("step" == key) = false) (h1 : (poolSwapBitmapAlias == key) = false)
    (h2 : ("__c12" == key) = false) (h3 : ("__c13" == key) = false) :
    (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) (poolSwapScanStep s evm id r p)).locals.get? key =
      f.locals.get? key := by
  simp only [tickClampPriceFrame, valueLocal_get, h3, Bool.false_eq_true, if_false, tickClampFrame_get _ _ _ h0,
    poolSwapScanFrame, poolSwapScanCallFrame, h0, h1, h2]

theorem poolSwapScanComputeSource {f : Frame} {evm : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords} {remaining fee : UInt256}
    (hf : f.contract = contract) (htick : (EVM.signed r.tick).natAbs < 2^255)
    (hrc : r.price.toNat < 2^160) (hlc : p.priceLimit.toNat < 2^160)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hself : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne))
    (hrem : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hfee : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat))) :
    let scan := poolSwapScanStep s evm id r p
    let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
    let f1 := tickClampPriceFrame (poolSwapScanFrame f s evm id r p) scan
    ExecBlock config f evm (poolSwapLoopBody.take 15)
      (if swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee then
        .ok (poolSwapComputeFrame f1 {scan with tickNext := tickClampWord scan.tickNext} r p next remaining fee) evm
       else .reverted) := by
  dsimp only
  let scan := poolSwapScanStep s evm id r p
  let f1 := tickClampPriceFrame (poolSwapScanFrame f s evm id r p) scan
  have hpre := poolSwapScanPriceSource (evm := evm) hf htick hs hr hp hself hz
  have hstep := tickClampFrame_step (poolSwapScanFrame_step f s evm id r p) (poolSwapScanStep_tick_canonical ..)
  have hs1 : f1.locals.get? "step" = some (poolSwapStepValue {scan with tickNext := tickClampWord scan.tickNext}) :=
    (store_get_ne _ _ (by decide : ("__c13" == "step") = false)).trans hstep
  have hf1 : (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) (poolSwapScanStep s evm id r p)).contract = contract := by
    simp only [tickClampPriceFrame, valueLocal_contract, tickClampFrame_contract, poolSwapScanFrame_contract, hf]
  have hrun := poolSwapComputeSource (evm := evm) hf1 hrc (tickSqrtPrice_lt_160 (tickClampWord_natAbs scan.tickNext)) hlc hs1
    ((poolSwapScanPriceFrame_get _ _ _ _ _ _ "result" (by decide) (by decide) (by decide) (by decide)).trans hr)
    ((poolSwapScanPriceFrame_get _ _ _ _ _ _ "params" (by decide) (by decide) (by decide) (by decide)).trans hp)
    ((poolSwapScanPriceFrame_get _ _ _ _ _ _ "zeroForOne" (by decide) (by decide) (by decide) (by decide)).trans hz)
    (store_get_self _ _ _)
    ((poolSwapScanPriceFrame_get _ _ _ _ _ _ "amountSpecifiedRemaining" (by decide) (by decide) (by decide) (by decide)).trans hrem)
    ((poolSwapScanPriceFrame_get _ _ _ _ _ _ "swapFee" (by decide) (by decide) (by decide) (by decide)).trans hfee)
  exact execBlock_append hpre hrun

end Benchmarks.UniswapV4PoolManager
