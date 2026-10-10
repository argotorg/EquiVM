import Benchmarks.UniswapV4PoolManager.TickClampWords
import Benchmarks.UniswapV4PoolManager.PoolSwapStepWords
import Benchmarks.UniswapV4PoolManager.ValueLocals
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickClampLowerStmt : Stmt :=
  .ite (.binary .le (.field (.var "step") "tickNext") (.unary .neg (.intLit 887272)))
    [.assign .localVar {base := "step", steps := [.field "tickNext"]} (.unary .neg (.intLit 887272))] []

def tickClampUpperStmt : Stmt :=
  .ite (.binary .ge (.field (.var "step") "tickNext") (.intLit 887272))
    [.assign .localVar {base := "step", steps := [.field "tickNext"]} (.intLit 887272)] []

theorem poolSwapLoop_clamp : (poolSwapLoopBody.drop 5).take 2 = [tickClampLowerStmt, tickClampUpperStmt] := rfl

def tickClampLowerFrame (f : Frame) (s : PoolSwapStepWords) : Frame :=
  if EVM.signed s.tickNext ≤ -887272 then
    valueLocal f "step" (poolSwapStepValue {s with tickNext := tickMinWord}) else f

def tickClampUpperFrame (f : Frame) (s : PoolSwapStepWords) : Frame :=
  if EVM.signed s.tickNext ≥ 887272 then
    valueLocal f "step" (poolSwapStepValue {s with tickNext := tickMaxWord}) else f

def tickClampFrame (f : Frame) (s : PoolSwapStepWords) : Frame :=
  tickClampUpperFrame (tickClampLowerFrame f s) {s with tickNext := tickClampLowerWord s.tickNext}

theorem tickClampLowerSource {cfg : Config} {f : Frame} {evm : State} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) :
    ExecStmt cfg f evm tickClampLowerStmt (.ok (tickClampLowerFrame f s) evm) := by
  have he : evalExpr? cfg f evm (.unary .neg (.intLit 887272)) = .ok (.int (-887272)) := by
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalUnaryOp?, EvalResult.ofOption]
  have hguard : evalExpr? cfg f evm
      (.binary .le (.field (.var "step") "tickNext") (.unary .neg (.intLit 887272))) =
      .ok (.bool (decide (EVM.signed s.tickNext ≤ -887272))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), poolSwapStep_tick_eval hs, he]
    rfl
  by_cases hl : EVM.signed s.tickNext ≤ -887272
  · rw [tickClampLowerFrame, if_pos hl]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hl] using hguard)
    apply execBlock_singleton
    exact ExecStmt.assign (by simpa only [tickMinWord_signed] using he) (poolSwapStep_tick_assign hs tickMinWord)
  · rw [tickClampLowerFrame, if_neg hl]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hl] using hguard) ExecBlock.nil

theorem tickClampUpperSource {cfg : Config} {f : Frame} {evm : State} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) :
    ExecStmt cfg f evm tickClampUpperStmt (.ok (tickClampUpperFrame f s) evm) := by
  have he : evalExpr? cfg f evm (.intLit 887272) = .ok (.int 887272) := by
    simp only [evalExpr?, pure]
  have hguard : evalExpr? cfg f evm
      (.binary .ge (.field (.var "step") "tickNext") (.intLit 887272)) =
      .ok (.bool (decide (EVM.signed s.tickNext ≥ 887272))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), poolSwapStep_tick_eval hs, he]
    rfl
  by_cases hh : EVM.signed s.tickNext ≥ 887272
  · rw [tickClampUpperFrame, if_pos hh]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hh] using hguard)
    apply execBlock_singleton
    exact ExecStmt.assign (by simpa only [tickMaxWord_signed] using he) (poolSwapStep_tick_assign hs tickMaxWord)
  · rw [tickClampUpperFrame, if_neg hh]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hh] using hguard) ExecBlock.nil

theorem tickClampLowerFrame_step {f : Frame} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) (hc : int24Canonical s.tickNext) :
    (tickClampLowerFrame f s).locals.get? "step" =
      some (poolSwapStepValue {s with tickNext := tickClampLowerWord s.tickNext}) := by
  have hclean : UInt256.signextend (UInt256.ofNat 2) s.tickNext = s.tickNext := (signextend24_eq_iff _).mpr hc
  unfold tickClampLowerFrame tickClampLowerWord
  rw [hclean]
  split
  · exact store_get_self _ _ _
  · exact hs

theorem tickClampSource {cfg : Config} {f : Frame} {evm : State} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) (hc : int24Canonical s.tickNext) :
    ExecBlock cfg f evm [tickClampLowerStmt, tickClampUpperStmt] (.ok (tickClampFrame f s) evm) :=
  ExecBlock.consNormal (tickClampLowerSource hs)
    (execBlock_singleton (tickClampUpperSource (tickClampLowerFrame_step hs hc)))

theorem tickClampFrame_step {f : Frame} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) (hc : int24Canonical s.tickNext) :
    (tickClampFrame f s).locals.get? "step" =
      some (poolSwapStepValue {s with tickNext := tickClampWord s.tickNext}) := by
  unfold tickClampFrame tickClampUpperFrame tickClampWord
  dsimp only
  split
  · exact store_get_self _ _ _
  · exact tickClampLowerFrame_step hs hc

theorem tickClampFrame_contract (f : Frame) (s : PoolSwapStepWords) :
    (tickClampFrame f s).contract = f.contract := by
  unfold tickClampFrame tickClampLowerFrame tickClampUpperFrame
  split <;> split <;> rfl

end Benchmarks.UniswapV4PoolManager
