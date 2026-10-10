import Benchmarks.UniswapV3.Pool.TickSpacingModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def spacingMinExpr : Expr :=
  .cast (.binary .mul (.binary .sdiv (.unary .neg (.intLit 887272)) (.var "tickSpacing"))
    (.var "tickSpacing")) (.elem (.int (.sint ⟨24, by decide⟩)))

def spacingMaxExpr : Expr :=
  .cast (.binary .mul (.binary .sdiv
    (.cast (.binary .sub (.intLit 0) (.unary .neg (.intLit 887272)))
      (.elem (.int (.sint ⟨24, by decide⟩)))) (.var "tickSpacing"))
    (.var "tickSpacing")) (.elem (.int (.sint ⟨24, by decide⟩)))

def spacingCountExpr : Expr :=
  .cast (.binary .add (.cast (.binary .sdiv
    (.cast (.binary .sub (.var "maxTick") (.var "minTick"))
      (.elem (.int (.sint ⟨24, by decide⟩)))) (.var "tickSpacing"))
      (.elem (.int (.uint ⟨24, by decide⟩)))) (.intLit 1))
    (.elem (.int (.uint ⟨24, by decide⟩)))

def tickSpacingMinFrame (imms : Store) (spacing : Int) : Frame :=
  {tickSpacingFrame imms spacing with
    locals := (tickSpacingLocals spacing).insert "minTick" (.int (spacingMin spacing))}

def tickSpacingMaxFrame (imms : Store) (spacing : Int) : Frame :=
  {tickSpacingMinFrame imms spacing with
    locals := (tickSpacingMinFrame imms spacing).locals.insert "maxTick" (.int (spacingMax spacing))}

def tickSpacingReadyFrame (imms : Store) (spacing : Int) : Frame :=
  {tickSpacingMaxFrame imms spacing with
    locals := (tickSpacingMaxFrame imms spacing).locals.insert "numTicks" (.int (spacingCount spacing))}

theorem evalSpacingMin {frame : Frame} {evm : EVM.State} (spacing : Int)
    (ht : frame.locals.get? "tickSpacing" = some (.int spacing)) (hn : spacing ≠ 0) :
    evalExpr? config frame evm spacingMinExpr = .ok (.int (spacingMin spacing)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) ht
  simp [spacingMinExpr, spacingMin, spacingMinProduct, evalExpr?, he,
    evalUnaryOp?, EvalResult.ofOption, evalBinaryOp?, castValue?, EvalResult.ofOption, bind, EvalResult.bind, hn]

theorem evalSpacingMax {frame : Frame} {evm : EVM.State} (spacing : Int)
    (ht : frame.locals.get? "tickSpacing" = some (.int spacing)) (hn : spacing ≠ 0) :
    evalExpr? config frame evm spacingMaxExpr = .ok (.int (spacingMax spacing)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) ht
  have hc : normalizeInt (.sint ⟨24, by decide⟩) 887272 = 887272 := by decide
  simp [spacingMaxExpr, spacingMax, spacingMaxProduct, evalExpr?, he,
    evalUnaryOp?, EvalResult.ofOption, evalBinaryOp?, castValue?, EvalResult.ofOption, bind, EvalResult.bind, hc, hn]

theorem evalSpacingCount {frame : Frame} {evm : EVM.State} (spacing : Int)
    (ht : frame.locals.get? "tickSpacing" = some (.int spacing))
    (hmin : frame.locals.get? "minTick" = some (.int (spacingMin spacing)))
    (hmax : frame.locals.get? "maxTick" = some (.int (spacingMax spacing))) (hn : spacing ≠ 0) :
    evalExpr? config frame evm spacingCountExpr = .ok (.int (spacingCount spacing)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) ht
  have h0 := evalExpr_var_get (cfg := config) (evm := evm) hmin
  have h1 := evalExpr_var_get (cfg := config) (evm := evm) hmax
  simp [spacingCountExpr, spacingCount, spacingDelta, evalExpr?, he, h0, h1,
    evalBinaryOp?, castValue?, EvalResult.ofOption, bind, EvalResult.bind, hn]

theorem tickSpacingReadySource (imms : Store) (evm : EVM.State) (spacing : Int)
    (hn : spacing ≠ 0) :
    ExecBlock config (tickSpacingFrame imms spacing) evm (tickSpacingFunction.body.take 3)
      (.ok (tickSpacingReadyFrame imms spacing) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalSpacingMin spacing
    Std.HashMap.getElem?_insert_self hn)) ?_
  have hget : (tickSpacingMinFrame imms spacing).locals.get? "tickSpacing" = some (.int spacing) := by
    simp only [tickSpacingMinFrame, tickSpacingLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalSpacingMax spacing hget hn)) ?_
  have hgets :
      (tickSpacingMaxFrame imms spacing).locals.get? "tickSpacing" = some (.int spacing) ∧
      (tickSpacingMaxFrame imms spacing).locals.get? "minTick" = some (.int (spacingMin spacing)) ∧
      (tickSpacingMaxFrame imms spacing).locals.get? "maxTick" = some (.int (spacingMax spacing)) := by
    simp only [tickSpacingMaxFrame, tickSpacingMinFrame, tickSpacingLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    exact ⟨rfl, rfl, rfl⟩
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalSpacingCount spacing hgets.1 hgets.2.1
    hgets.2.2 hn)) ExecBlock.nil

theorem tickSpacingReturns (imms : Store) (evm : EVM.State) (spacing : Int)
    (hn : spacing ≠ 0) (hc : spacingCount spacing ≠ 0) :
    ExecFuncBody config (tickSpacingFrame imms spacing) evm tickSpacingFunction.body
      (.returned (tickSpacingReadyFrame imms spacing) evm (some [.int (spacingLiquidity spacing)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 3 tickSpacingFunction.body]
  apply execBlock_append_ok (tickSpacingReadySource imms evm spacing hn)
  refine ExecBlock.consReturn (ExecStmt.return ?_)
  have he : evalExpr? config (tickSpacingReadyFrame imms spacing) evm (.var "numTicks") =
      .ok (.int (spacingCount spacing)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp [evalExprs?, evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure, hc, spacingLiquidity]

theorem tickSpacingRevertsZero (imms : Store) (evm : EVM.State) :
    ExecFuncBody config (tickSpacingFrame imms 0) evm tickSpacingFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  have he : evalExpr? config (tickSpacingFrame imms 0) evm (.var "tickSpacing") =
      .ok (.int 0) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  change evalExpr? config _ _ spacingMinExpr = .revert
  simp [spacingMinExpr, evalExpr?, he, evalUnaryOp?, EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem tickSpacingRevertsCount (imms : Store) (evm : EVM.State) (spacing : Int)
    (hn : spacing ≠ 0) (hc : spacingCount spacing = 0) :
    ExecFuncBody config (tickSpacingFrame imms spacing) evm tickSpacingFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 tickSpacingFunction.body]
  apply execBlock_append_ok (tickSpacingReadySource imms evm spacing hn)
  refine ExecBlock.consRevert (ExecStmt.returnRevert ?_)
  have he : evalExpr? config (tickSpacingReadyFrame imms spacing) evm (.var "numTicks") =
      .ok (.int (spacingCount spacing)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp [evalExprs?, evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, hc]

end Benchmarks.UniswapV3.Pool
