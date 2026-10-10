import Benchmarks.UniswapV4PoolManager.SwapStepInputPartialSource
import Benchmarks.UniswapV4PoolManager.SwapStepSelectWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapStepInputSelectStmt : Stmt :=
  .ite (.binary .ge (.var "amountRemainingLessFee") (.var "amountIn"))
    (.assign .localVar {base := "sqrtPriceNextX96"} (.var "sqrtPriceTargetX96") :: swapStepTargetFeeStmts)
    swapStepInputPartialStmts

def swapStepInputSelectFrame (f : Frame) (price target liquidity remaining available desired fee : UInt256)
    (zeroForOne : Bool) : Frame :=
  if swapStepReachesTarget available desired then
    swapStepTargetFeeFrame (wordLocal f "sqrtPriceNextX96" target) desired fee
  else swapStepInputPartialFrame f price liquidity remaining available zeroForOne

theorem swapStepInputSelectSource {f : Frame} {evm : EVM.State}
    {price target liquidity remaining available desired fee : UInt256} {oldNext oldFee : Value}
    (zeroForOne : Bool) (hf : f.contract = contract) (hp : price.toNat < 2^160)
    (hs : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "sqrtPriceTargetX96" = some (.int (Int.ofNat target.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (ha : f.locals.get? "amountRemainingLessFee" = some (.int (Int.ofNat available.toNat)))
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hi : f.locals.get? "amountIn" = some (.int (Int.ofNat desired.toNat)))
    (hn : f.locals.get? "sqrtPriceNextX96" = some oldNext)
    (hfee : f.locals.get? "feeAmount" = some oldFee)
    (hfPips : f.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat))) :
    ExecStmt config f evm swapStepInputSelectStmt
      (if swapStepInputSelectFits price liquidity available desired fee zeroForOne then
        .ok (swapStepInputSelectFrame f price target liquidity remaining available desired fee zeroForOne) evm
       else .reverted) := by
  have hg := naturalGeSource (evalLocalValue (cfg := config) (f := f) (evm := evm) ha) (evalLocalValue hi)
  change evalExpr? config f evm (.binary .ge (.var "amountRemainingLessFee") (.var "amountIn")) =
    .ok (.bool (decide (swapStepReachesTarget available desired))) at hg
  by_cases hreach : swapStepReachesTarget available desired
  · simp only [swapStepInputSelectFits, swapStepInputSelectFrame, if_pos hreach]
    let f1 := wordLocal f "sqrtPriceNextX96" target
    have hn1 : ExecStmt config f evm
        (.assign .localVar {base := "sqrtPriceNextX96"} (.var "sqrtPriceTargetX96")) (.ok f1 evm) :=
      ExecStmt.assign (evalLocalValue ht) (assignLocalValue hn)
    have hcalc := swapStepTargetFeeSource (f := f1) (evm := evm) hf
      ((store_get_ne _ _ (by decide : ("sqrtPriceNextX96" == "amountIn") = false)).trans hi)
      ((store_get_ne _ _ (by decide : ("sqrtPriceNextX96" == "_feePips") = false)).trans hfPips)
      ((store_get_ne _ _ (by decide : ("sqrtPriceNextX96" == "feeAmount") = false)).trans hfee)
    have htrue := (show evalExpr? config f evm
        (.binary .ge (.var "amountRemainingLessFee") (.var "amountIn")) = .ok (.bool true) by
      simpa only [decide_eq_true hreach] using hg)
    by_cases hfit : swapStepTargetFeeFits desired fee
    · rw [if_pos hfit] at hcalc ⊢
      exact ExecStmt.iteTrue htrue (ExecBlock.consNormal hn1 hcalc)
    · rw [if_neg hfit] at hcalc ⊢
      exact ExecStmt.iteTrue htrue (ExecBlock.consNormal hn1 hcalc)
  · simp only [swapStepInputSelectFits, swapStepInputSelectFrame, if_neg hreach]
    have hcalc := swapStepInputPartialSource (evm := evm) zeroForOne hf hp hs hl hr ha hb hi hn hfee
    have hfalse := (show evalExpr? config f evm
        (.binary .ge (.var "amountRemainingLessFee") (.var "amountIn")) = .ok (.bool false) by
      simpa only [decide_eq_false hreach] using hg)
    by_cases hfit : nextPriceFits price liquidity available true zeroForOne
    · rw [if_pos hfit] at hcalc ⊢
      exact ExecStmt.iteFalse hfalse hcalc
    · rw [if_neg hfit] at hcalc ⊢
      exact ExecStmt.iteFalse hfalse hcalc

end Benchmarks.UniswapV4PoolManager
