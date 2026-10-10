import Benchmarks.UniswapV3.Pool.SwapIterationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationBitmapStoresFrame (frame : Frame) (d : SwapIterationData) (tick : Int)
    (hit : Bool) : Frame :=
  swapIterationFrame (swapIterationFrame frame {d with tickNext := tick})
    {d with tickNext := tick, initialized := hit}

theorem swapIterationBitmapStoresSource {frame : Frame} {evm : EVM.State}
    (d : SwapIterationData) (tick : Int) (hit : Bool)
    (hd : frame.locals.get? "step" = some d.value)
    (hc : frame.locals.get? "__c2" = some (.tuple [.int tick, .bool hit])) :
    ExecBlock config frame evm ((swapLoopBody.drop 3).take 2)
      (.ok (swapIterationBitmapStoresFrame frame d tick hit) evm) := by
  have he : evalExpr? config frame evm (.tupleGet (.var "__c2") 0) = .ok (.int tick) := by
    simp only [evalExpr?, hc, EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]
    rfl
  have hg : (swapIterationFrame frame {d with tickNext := tick}).locals.get? "__c2" =
      some (.tuple [.int tick, .bool hit]) := by
    simpa only [swapIterationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using hc
  have hf : evalExpr? config (swapIterationFrame frame {d with tickNext := tick}) evm
      (.tupleGet (.var "__c2") 1) = .ok (.bool hit) := by
    simp only [evalExpr?, hg, EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]
    rfl
  exact ExecBlock.consNormal (ExecStmt.assign he (assignLocalField_frame hd rfl rfl))
    (ExecBlock.consNormal (ExecStmt.assign hf
      (assignLocalField_frame Std.HashMap.getElem?_insert_self rfl rfl)) ExecBlock.nil)

def swapIterationClampTick (tick : Int) : Int :=
  if tick < -887272 then -887272 else if 887272 < tick then 887272 else tick

def swapIterationClampFrame (frame : Frame) (d : SwapIterationData) : Frame :=
  if d.tickNext < -887272 then swapIterationFrame frame {d with tickNext := -887272}
  else if 887272 < d.tickNext then swapIterationFrame frame {d with tickNext := 887272}
  else frame

theorem swapIterationClampTick_bounds (tick : Int) :
    -887272 ≤ swapIterationClampTick tick ∧ swapIterationClampTick tick ≤ 887272 := by
  unfold swapIterationClampTick
  split_ifs <;> omega

theorem swapIterationClampSource {frame : Frame} {evm : EVM.State} (d : SwapIterationData)
    (hd : frame.locals.get? "step" = some d.value) :
    ExecStmt config frame evm swapLoopBody[5]!
      (.ok (swapIterationClampFrame frame d) evm) := by
  have ht := evalExpr_structField (name := "tickNext")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  have hl : evalExpr? config frame evm
      (.binary .lt (.field (.var "step") "tickNext") (.unary .neg (.intLit 887272))) =
      .ok (.bool (decide (d.tickNext < -887272))) :=
    evalExpr_int_lt ht (by
      simp only [evalExpr?, evalUnaryOp?, EvalResult.ofOption, bind, EvalResult.bind, pure])
  have hu : evalExpr? config frame evm
      (.binary .gt (.field (.var "step") "tickNext")
        (.cast (.binary .sub (.intLit 0) (.unary .neg (.intLit 887272)))
          (.elem (.int (.sint ⟨24, by decide⟩))))) =
      .ok (.bool (decide (887272 < d.tickNext))) := by
    simp only [evalExpr?, ht, evalUnaryOp?, evalBinaryOp?, castValue?, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
    rfl
  by_cases hlo : d.tickNext < -887272
  · simp only [swapIterationClampFrame, if_pos hlo]
    apply ExecStmt.iteTrue (by simpa only [hlo, decide_true] using hl)
    exact ExecBlock.consNormal (ExecStmt.assign (by
      simp only [evalExpr?, evalUnaryOp?, EvalResult.ofOption, bind, EvalResult.bind, pure])
      (assignLocalField_frame hd rfl rfl)) ExecBlock.nil
  · simp only [swapIterationClampFrame, if_neg hlo]
    apply ExecStmt.iteFalse (by simpa only [hlo, decide_false] using hl)
    apply ExecBlock.consNormal _ ExecBlock.nil
    by_cases hhi : 887272 < d.tickNext
    · simp only [if_pos hhi]
      apply ExecStmt.iteTrue (by simpa only [hhi, decide_true] using hu)
      apply ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalField_frame hd rfl rfl))
        ExecBlock.nil
      simp only [evalExpr?, evalUnaryOp?, evalBinaryOp?, castValue?, EvalResult.ofOption,
        bind, EvalResult.bind, pure]
      rfl
    · simp only [if_neg hhi]
      exact ExecStmt.iteFalse (by simpa only [hhi, decide_false] using hu) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
