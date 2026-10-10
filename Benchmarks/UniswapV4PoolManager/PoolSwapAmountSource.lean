import Benchmarks.UniswapV4PoolManager.PoolSwapInputAmountSource
import Benchmarks.UniswapV4PoolManager.PoolSwapOutputAmountSource
import Benchmarks.UniswapV4PoolManager.PoolSwapValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapAmountFits (s : PoolSwapStepWords) (specified calculated : UInt256) : Prop :=
  if 0 < EVM.signed specified then poolSwapOutputAmountFits s calculated else poolSwapInputAmountFits s calculated
instance (s : PoolSwapStepWords) (specified calculated : UInt256) : Decidable (poolSwapAmountFits s specified calculated) := by
  unfold poolSwapAmountFits
  infer_instance

def poolSwapAmountFrame (f : Frame) (s : PoolSwapStepWords) (specified remaining calculated : UInt256) : Frame :=
  if 0 < EVM.signed specified then poolSwapOutputAmountFrame f s remaining calculated
  else poolSwapInputAmountFrame f s remaining calculated

theorem poolSwapAmountSource {f : Frame} {evm : State}
    {s : PoolSwapStepWords} {p : PoolSwapParamsWords} {remaining calculated : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hr : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hc : f.locals.get? "amountCalculated" = some (.int (EVM.signed calculated))) :
    ExecStmt config f evm poolSwapLoopBody[15]!
      (if poolSwapAmountFits s p.amountSpecified calculated then
        .ok (poolSwapAmountFrame f s p.amountSpecified remaining calculated) evm else .reverted) := by
  have hg : evalExpr? config f evm (.binary .gt (.field (.var "params") "amountSpecified") (.intLit 0)) =
      .ok (.bool (decide (0 < EVM.signed p.amountSpecified))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalStructField (evalLocalValue hp) rfl]
    simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
  rw [poolSwapLoop_amounts]
  by_cases hpos : 0 < EVM.signed p.amountSpecified
  · simp only [poolSwapAmountFits, poolSwapAmountFrame, if_pos hpos]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hpos] using hg) (poolSwapOutputAmountSource hf hs hr hc)
  · simp only [poolSwapAmountFits, poolSwapAmountFrame, if_neg hpos]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hpos] using hg) (poolSwapInputAmountSource hf hs hr hc)

end Benchmarks.UniswapV4PoolManager
