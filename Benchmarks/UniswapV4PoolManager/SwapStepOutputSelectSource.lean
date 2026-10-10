import Benchmarks.UniswapV4PoolManager.SwapStepPriceSource
import Benchmarks.UniswapV4PoolManager.SwapStepSelectWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapStepOutputRemainingExpr : Expr :=
  .cast (.var "amountRemaining") (.elem (.int (.uint ⟨256, by decide⟩)))

theorem swapStepOutputRemainingSource {f : Frame} {evm : EVM.State} {remaining : UInt256}
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining))) :
    evalExpr? config f evm swapStepOutputRemainingExpr = .ok (.int (Int.ofNat remaining.toNat)) := by
  have hc := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
    (evalLocalValue (cfg := config) (f := f) (evm := evm) hr)
  simpa only [normalizeUnsignedSigned] using hc

def swapStepOutputSelectStmt : Stmt :=
  .ite (.binary .ge swapStepOutputRemainingExpr (.var "amountOut"))
    [.assign .localVar {base := "sqrtPriceNextX96"} (.var "sqrtPriceTargetX96")]
    (.assign .localVar {base := "amountOut"} swapStepOutputRemainingExpr :: swapStepPriceStmts (.var "amountOut") false)

def swapStepOutputSelectFrame (f : Frame) (price target liquidity remaining desired : UInt256)
    (zeroForOne : Bool) : Frame :=
  if swapStepReachesTarget remaining desired then wordLocal f "sqrtPriceNextX96" target
  else swapStepPriceFrame (wordLocal f "amountOut" remaining) price liquidity remaining false zeroForOne

theorem swapStepOutputSelectSource {f : Frame} {evm : EVM.State}
    {price target liquidity remaining desired : UInt256} {oldNext : Value}
    (zeroForOne : Bool) (hf : f.contract = contract) (hp : price.toNat < 2^160)
    (hs : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "sqrtPriceTargetX96" = some (.int (Int.ofNat target.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (ho : f.locals.get? "amountOut" = some (.int (Int.ofNat desired.toNat)))
    (hn : f.locals.get? "sqrtPriceNextX96" = some oldNext) :
    ExecStmt config f evm swapStepOutputSelectStmt
      (if swapStepOutputSelectFits price liquidity remaining desired zeroForOne then
        .ok (swapStepOutputSelectFrame f price target liquidity remaining desired zeroForOne) evm else .reverted) := by
  have he := swapStepOutputRemainingSource (evm := evm) hr
  have hg := naturalGeSource he (evalLocalValue ho)
  change evalExpr? config f evm (.binary .ge swapStepOutputRemainingExpr (.var "amountOut")) =
    .ok (.bool (decide (swapStepReachesTarget remaining desired))) at hg
  by_cases hreach : swapStepReachesTarget remaining desired
  · simp only [swapStepOutputSelectFits, swapStepOutputSelectFrame, if_pos hreach, if_true]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hreach] using hg)
      (execBlock_singleton (ExecStmt.assign (evalLocalValue ht) (assignLocalValue hn)))
  · simp only [swapStepOutputSelectFits, swapStepOutputSelectFrame, if_neg hreach]
    let f1 := wordLocal f "amountOut" remaining
    have h1 : ExecStmt config f evm (.assign .localVar {base := "amountOut"} swapStepOutputRemainingExpr)
        (.ok f1 evm) := ExecStmt.assign he (assignLocalValue ho)
    have hprice := swapStepPriceSource (f := f1) (evm := evm) (ea := .var "amountOut") false zeroForOne hf hp
      ((store_get_ne _ _ (by decide : ("amountOut" == "sqrtPriceCurrentX96") = false)).trans hs)
      ((store_get_ne _ _ (by decide : ("amountOut" == "liquidity") = false)).trans hl)
      wordLocal_eval
      ((store_get_ne _ _ (by decide : ("amountOut" == "zeroForOne") = false)).trans hb)
      ((store_get_ne _ _ (by decide : ("amountOut" == "sqrtPriceNextX96") = false)).trans hn)
    have hfalse := (show evalExpr? config f evm
        (.binary .ge swapStepOutputRemainingExpr (.var "amountOut")) = .ok (.bool false) by
      simpa only [decide_eq_false hreach] using hg)
    by_cases hfit : nextPriceFits price liquidity remaining false zeroForOne
    · rw [if_pos hfit] at hprice ⊢
      exact ExecStmt.iteFalse hfalse (ExecBlock.consNormal h1 hprice)
    · rw [if_neg hfit] at hprice ⊢
      exact ExecStmt.iteFalse hfalse (ExecBlock.consNormal h1 hprice)

end Benchmarks.UniswapV4PoolManager
