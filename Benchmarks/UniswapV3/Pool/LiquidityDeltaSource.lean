import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000
attribute [local instance] Classical.propDecidable

def liquidityDeltaFunction : FunctionDecl := contract.functions[24]!

theorem liquidityDeltaLookup :
    lookupCallable? contract "LiquidityMath_addDelta" =
      some liquidityDeltaFunction.toCallable := rfl

def liquidityDeltaLocals (x y : Int) : Store :=
  ((∅ : Store).insert "y" (.int y)).insert "x" (.int x)

def liquidityDeltaFrame (imms : Store) (x y : Int) : Frame :=
  {contract := contract, locals := liquidityDeltaLocals x y, immutables := imms}

def liquidityDeltaZeroFrame (imms : Store) (x y : Int) : Frame :=
  {liquidityDeltaFrame imms x y with locals := (liquidityDeltaLocals x y).insert "z" (.int 0)}

def liquidityDeltaReadyFrame (imms : Store) (x y : Int) : Frame :=
  {liquidityDeltaZeroFrame imms x y with
    locals := (liquidityDeltaZeroFrame imms x y).locals.insert "z"
      (.int (liquidityDeltaResult x y))}

theorem liquidityDeltaBind (x y : Int) :
    bindParams? liquidityDeltaFunction.params [.int x, .int y] =
      some (liquidityDeltaLocals x y) := rfl

def liquidityDeltaSubExpr : Expr :=
  .cast (.binary .sub (.var "x")
    (.cast (.cast (.binary .sub (.intLit 0) (.var "y"))
      (.elem (.int (.sint ⟨128, by decide⟩)))) (.elem (.int (.uint ⟨128, by decide⟩)))))
    (.elem (.int (.uint ⟨128, by decide⟩)))

def liquidityDeltaAddExpr : Expr :=
  .cast (.binary .add (.var "x")
    (.cast (.var "y") (.elem (.int (.uint ⟨128, by decide⟩)))))
    (.elem (.int (.uint ⟨128, by decide⟩)))

theorem liquidityDeltaZeroGet (imms : Store) (x y : Int) :
    (liquidityDeltaZeroFrame imms x y).locals.get? "x" = some (.int x) ∧
      (liquidityDeltaZeroFrame imms x y).locals.get? "y" = some (.int y) := by
  simp only [liquidityDeltaZeroFrame, liquidityDeltaLocals,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl⟩

theorem evalLiquidityDeltaCondition (imms : Store) (evm : EVM.State) (x y : Int) :
    evalExpr? config (liquidityDeltaZeroFrame imms x y) evm
      (.binary .lt (.var "y") (.intLit 0)) = .ok (.bool (decide (y < 0))) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (liquidityDeltaZeroGet imms x y).2
  simp only [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure]

theorem liquidityDeltaSubSource (imms : Store) (evm : EVM.State) (x y : Int) :
    ExecStmt config (liquidityDeltaZeroFrame imms x y) evm
      (.assign .localVar ⟨"z", []⟩ liquidityDeltaSubExpr)
      (.ok (liquidityDeltaReadyFrame imms x y) evm) := by
  apply ExecStmt.assign (value := .int (liquidityDeltaResult x y))
  · have hx := evalExpr_var_get (cfg := config) (evm := evm)
      (liquidityDeltaZeroGet imms x y).1
    have hy := evalExpr_var_get (cfg := config) (evm := evm)
      (liquidityDeltaZeroGet imms x y).2
    simp only [liquidityDeltaSubExpr, evalExpr?, hx, hy, evalBinaryOp?,
      castValue?, EvalResult.ofOption, bind, EvalResult.bind, pure, liquidityDeltaSubtract]
  · exact assignLocalVarBase_frame Std.HashMap.getElem?_insert_self

theorem liquidityDeltaAddSource (imms : Store) (evm : EVM.State) (x y : Int) :
    ExecStmt config (liquidityDeltaZeroFrame imms x y) evm
      (.assign .localVar ⟨"z", []⟩ liquidityDeltaAddExpr)
      (.ok (liquidityDeltaReadyFrame imms x y) evm) := by
  apply ExecStmt.assign (value := .int (liquidityDeltaResult x y))
  · have hx := evalExpr_var_get (cfg := config) (evm := evm)
      (liquidityDeltaZeroGet imms x y).1
    have hy := evalExpr_var_get (cfg := config) (evm := evm)
      (liquidityDeltaZeroGet imms x y).2
    simp only [liquidityDeltaAddExpr, evalExpr?, hx, hy, evalBinaryOp?,
      castValue?, EvalResult.ofOption, bind, EvalResult.bind, pure, liquidityDeltaAdd]
  · exact assignLocalVarBase_frame Std.HashMap.getElem?_insert_self

theorem evalLiquidityDeltaGuards (imms : Store) (evm : EVM.State) (x y : Int) :
    evalExpr? config (liquidityDeltaReadyFrame imms x y) evm
      (.binary .lt (.var "z") (.var "x")) =
      .ok (.bool (decide (liquidityDeltaResult x y < x))) ∧
    evalExpr? config (liquidityDeltaReadyFrame imms x y) evm
      (.binary .ge (.var "z") (.var "x")) =
      .ok (.bool (decide (x ≤ liquidityDeltaResult x y))) := by
  have hx : (liquidityDeltaReadyFrame imms x y).locals.get? "x" = some (.int x) := by
    simp only [liquidityDeltaReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    exact (liquidityDeltaZeroGet imms x y).1
  have he := evalExpr_var_get (cfg := config) (evm := evm) hx
  have hz : evalExpr? config (liquidityDeltaReadyFrame imms x y) evm (.var "z") =
      .ok (.int (liquidityDeltaResult x y)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  constructor <;> simp only [evalExpr?, he, hz, evalBinaryOp?, bind, EvalResult.bind, pure]

theorem liquidityDeltaReturns (imms : Store) (evm : EVM.State) (x y : Int)
    (hv : liquidityDeltaValid x y) :
    ExecFuncBody config (liquidityDeltaFrame imms x y) evm liquidityDeltaFunction.body
      (.returned (liquidityDeltaReadyFrame imms x y) evm
        (some [.int (liquidityDeltaResult x y)])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (solm' := liquidityDeltaZeroFrame imms x y)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := liquidityDeltaReadyFrame imms x y) (evm' := evm) ?_ ?_
  · by_cases hy : y < 0
    · have hg : liquidityDeltaResult x y < x := by
        simpa only [liquidityDeltaValid, hy, if_true] using hv
      apply ExecStmt.iteTrue
        (by simpa only [hy, decide_true] using evalLiquidityDeltaCondition imms evm x y)
      exact ExecBlock.consNormal (liquidityDeltaSubSource imms evm x y)
        (ExecBlock.consNormal (ExecStmt.requireTrue
          (by simpa only [hg, decide_true] using (evalLiquidityDeltaGuards imms evm x y).1))
          ExecBlock.nil)
    · have hg : x ≤ liquidityDeltaResult x y := by
        simpa only [liquidityDeltaValid, hy, if_false] using hv
      apply ExecStmt.iteFalse
        (by simpa only [hy, decide_false] using evalLiquidityDeltaCondition imms evm x y)
      exact ExecBlock.consNormal (liquidityDeltaAddSource imms evm x y)
        (ExecBlock.consNormal (ExecStmt.requireTrue
          (by simpa only [hg, decide_true] using (evalLiquidityDeltaGuards imms evm x y).2))
          ExecBlock.nil)
  · refine ExecBlock.consReturn (ExecStmt.return ?_)
    have he : evalExpr? config (liquidityDeltaReadyFrame imms x y) evm (.var "z") =
        .ok (.int (liquidityDeltaResult x y)) :=
      evalExpr_var_get Std.HashMap.getElem?_insert_self
    simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem liquidityDeltaReverts (imms : Store) (evm : EVM.State) (x y : Int)
    (hv : ¬ liquidityDeltaValid x y) :
    ExecFuncBody config (liquidityDeltaFrame imms x y) evm liquidityDeltaFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (solm' := liquidityDeltaZeroFrame imms x y)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  apply ExecBlock.consRevert
  by_cases hy : y < 0
  · have hg : ¬ liquidityDeltaResult x y < x := by
      simpa only [liquidityDeltaValid, hy, if_true] using hv
    apply ExecStmt.iteTrue
      (by simpa only [hy, decide_true] using evalLiquidityDeltaCondition imms evm x y)
    exact ExecBlock.consNormal (liquidityDeltaSubSource imms evm x y)
      (ExecBlock.consRevert (ExecStmt.requireFalse
        (by simpa only [hg, decide_false] using (evalLiquidityDeltaGuards imms evm x y).1)))
  · have hg : ¬ x ≤ liquidityDeltaResult x y := by
      simpa only [liquidityDeltaValid, hy, if_false] using hv
    apply ExecStmt.iteFalse
      (by simpa only [hy, decide_false] using evalLiquidityDeltaCondition imms evm x y)
    exact ExecBlock.consNormal (liquidityDeltaAddSource imms evm x y)
      (ExecBlock.consRevert (ExecStmt.requireFalse
        (by simpa only [hg, decide_false] using (evalLiquidityDeltaGuards imms evm x y).2)))

end Benchmarks.UniswapV3.Pool
