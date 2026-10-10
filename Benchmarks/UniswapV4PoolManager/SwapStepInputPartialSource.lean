import Benchmarks.UniswapV4PoolManager.SwapStepPriceSource
import Benchmarks.UniswapV4PoolManager.SwapStepRemainingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapStepInputPartialStmts : List Stmt :=
  [.assign .localVar {base := "amountIn"} (.var "amountRemainingLessFee")] ++
  swapStepPriceStmts (.var "amountRemainingLessFee") true ++
  [.assign .localVar {base := "feeAmount"} swapStepRemainingFeeExpr]

def swapStepInputPartialFrame (f : Frame) (price liquidity remaining available : UInt256) (zeroForOne : Bool) : Frame :=
  wordLocal (swapStepPriceFrame (wordLocal f "amountIn" available) price liquidity available true zeroForOne)
    "feeAmount" (swapStepRemainingFeeWord remaining available)

theorem swapStepInputPartialSource {f : Frame} {evm : EVM.State} {price liquidity remaining available : UInt256}
    {oldIn oldNext oldFee : Value} (zeroForOne : Bool) (hf : f.contract = contract) (hp : price.toNat < 2^160)
    (hs : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (ha : f.locals.get? "amountRemainingLessFee" = some (.int (Int.ofNat available.toNat)))
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hi : f.locals.get? "amountIn" = some oldIn)
    (hn : f.locals.get? "sqrtPriceNextX96" = some oldNext)
    (hfee : f.locals.get? "feeAmount" = some oldFee) :
    ExecBlock config f evm swapStepInputPartialStmts
      (if nextPriceFits price liquidity available true zeroForOne then
        .ok (swapStepInputPartialFrame f price liquidity remaining available zeroForOne) evm else .reverted) := by
  let f1 := wordLocal f "amountIn" available
  have h1 : ExecStmt config f evm (.assign .localVar {base := "amountIn"} (.var "amountRemainingLessFee"))
      (.ok f1 evm) := ExecStmt.assign (evalLocalValue ha) (assignLocalValue hi)
  have hprice := swapStepPriceSource (f := f1) (evm := evm) true zeroForOne hf hp
    ((store_get_ne _ _ (by decide : ("amountIn" == "sqrtPriceCurrentX96") = false)).trans hs)
    ((store_get_ne _ _ (by decide : ("amountIn" == "liquidity") = false)).trans hl)
    (evalLocalValue ((store_get_ne _ _ (by decide : ("amountIn" == "amountRemainingLessFee") = false)).trans ha))
    ((store_get_ne _ _ (by decide : ("amountIn" == "zeroForOne") = false)).trans hb)
    ((store_get_ne _ _ (by decide : ("amountIn" == "sqrtPriceNextX96") = false)).trans hn)
  by_cases hfit : nextPriceFits price liquidity available true zeroForOne
  · rw [if_pos hfit] at hprice ⊢
    let f2 := swapStepPriceFrame f1 price liquidity available true zeroForOne
    have hr2 : f2.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)) :=
      (swapStepPriceFrame_get _ _ _ _ _ _ _ (by decide) (by decide)).trans
        ((store_get_ne _ _ (by decide : ("amountIn" == "amountRemaining") = false)).trans hr)
    have hi2 : f2.locals.get? "amountIn" = some (.int (Int.ofNat available.toNat)) :=
      (swapStepPriceFrame_get _ _ _ _ _ _ _ (by decide) (by decide)).trans (store_get_self _ _ _)
    have hf2 : f2.locals.get? "feeAmount" = some oldFee :=
      (swapStepPriceFrame_get _ _ _ _ _ _ _ (by decide) (by decide)).trans
        ((store_get_ne _ _ (by decide : ("amountIn" == "feeAmount") = false)).trans hfee)
    have h2 : ExecStmt config f2 evm (.assign .localVar {base := "feeAmount"} swapStepRemainingFeeExpr)
        (.ok (wordLocal f2 "feeAmount" (swapStepRemainingFeeWord remaining available)) evm) :=
      ExecStmt.assign (swapStepRemainingFeeSource hr2 hi2) (assignLocalValue hf2)
    exact ExecBlock.consNormal h1 (execBlock_append hprice (execBlock_singleton h2))
  · rw [if_neg hfit] at hprice ⊢
    exact ExecBlock.consNormal h1 (execBlock_reverted_append hprice)

end Benchmarks.UniswapV4PoolManager
