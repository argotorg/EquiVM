import Benchmarks.UniswapV4PoolManager.SwapStepInputSource
import Benchmarks.UniswapV4PoolManager.SwapStepOutputSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

structure SwapStepFrameResult (f : Frame) (w : SwapStepWords) : Prop where
  next : f.locals.get? "sqrtPriceNextX96" = some (.int (Int.ofNat w.next.toNat))
  amountIn : f.locals.get? "amountIn" = some (.int (Int.ofNat w.amountIn.toNat))
  amountOut : f.locals.get? "amountOut" = some (.int (Int.ofNat w.amountOut.toNat))
  fee : f.locals.get? "feeAmount" = some (.int (Int.ofNat w.fee.toNat))

def swapStepReturnValues (w : SwapStepWords) : List Value :=
  [.int (Int.ofNat w.next.toNat), .int (Int.ofNat w.amountIn.toNat),
   .int (Int.ofNat w.amountOut.toNat), .int (Int.ofNat w.fee.toNat)]

def swapStepReturnStmt : Stmt :=
  .return [.var "sqrtPriceNextX96", .var "amountIn", .var "amountOut", .var "feeAmount"]

theorem swapStepReturnSource {f : Frame} {evm : EVM.State} {w : SwapStepWords} (h : SwapStepFrameResult f w) :
    ExecBlock config f evm [swapStepReturnStmt] (.returned f evm (some (swapStepReturnValues w))) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  change evalExprs? config f evm [.var "sqrtPriceNextX96", .var "amountIn", .var "amountOut", .var "feeAmount"] = _
  simp only [swapStepReturnValues, evalExprs?, evalLocalValue h.next, evalLocalValue h.amountIn,
    evalLocalValue h.amountOut, evalLocalValue h.fee, bind, EvalResult.bind, pure]

theorem swapStepInputFrame_result (f : Frame) (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) :
    SwapStepFrameResult (swapStepInputFrame f price target liquidity remaining fee zeroForOne)
      (swapStepInputWords price target liquidity remaining fee zeroForOne) := by
  let available := swapStepAvailableWord remaining fee
  let desired := swapStepDeltaWord price target liquidity true zeroForOne
  let f2 := amountDeltaFrame (wordLocal f "amountRemainingLessFee" available) "amountIn" desired
  let f3 := swapStepInputSelectFrame f2 price target liquidity remaining available desired fee zeroForOne
  constructor
  · exact (amountDeltaFrame_get f3 _ _ _ (by decide) (by decide)).trans
      (swapStepInputSelectFrame_next _ _ _ _ _ _ _ _ _)
  · exact (amountDeltaFrame_get f3 _ _ _ (by decide) (by decide)).trans
      (swapStepInputSelectFrame_amount _ _ _ _ _ _ _ _ (store_get_self _ _ _))
  · exact store_get_self _ _ _
  · exact (amountDeltaFrame_get f3 _ _ _ (by decide) (by decide)).trans
      (swapStepInputSelectFrame_fee _ _ _ _ _ _ _ _ _)

theorem swapStepOutputFrame_result (f : Frame) (price target liquidity remaining fee : UInt256) (zeroForOne : Bool) :
    SwapStepFrameResult (swapStepOutputFrame f price target liquidity remaining fee zeroForOne)
      (swapStepOutputWords price target liquidity remaining fee zeroForOne) := by
  let desired := swapStepDeltaWord price target liquidity false zeroForOne
  let f1 := amountDeltaFrame f "amountOut" desired
  let f2 := swapStepOutputSelectFrame f1 price target liquidity remaining desired zeroForOne
  let amountIn := (swapStepOutputWords price target liquidity remaining fee zeroForOne).amountIn
  let f3 := amountDeltaFrame f2 "amountIn" amountIn
  have hget (name : Ident) (hf : ("feeAmount" == name) = false) (hc : ("__c12" == name) = false) :
      (swapStepOutputFrame f price target liquidity remaining fee zeroForOne).locals.get? name = f3.locals.get? name := by
    change (swapStepComputedFeeFrame f3 "__c12" amountIn fee).locals.get? name = _
    simp only [swapStepComputedFeeFrame_eq, wordLocal_get, hf, hc, Bool.false_eq_true, if_false]
  constructor
  · exact (hget _ (by decide) (by decide)).trans
      ((amountDeltaFrame_get f2 _ _ _ (by decide) (by decide)).trans
        (swapStepOutputSelectFrame_next _ _ _ _ _ _ _))
  · exact (hget _ (by decide) (by decide)).trans (store_get_self _ _ _)
  · exact (hget _ (by decide) (by decide)).trans
      ((amountDeltaFrame_get f2 _ _ _ (by decide) (by decide)).trans
        (swapStepOutputSelectFrame_amount _ _ _ _ _ _ (store_get_self _ _ _)))
  · simp only [swapStepOutputFrame, swapStepComputedFeeFrame_eq, wordLocal_get,
      beq_self_eq_true, if_true, swapStepOutputWords]

end Benchmarks.UniswapV4PoolManager
