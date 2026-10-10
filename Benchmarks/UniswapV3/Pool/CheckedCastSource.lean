import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: narrowing casts checked by equality with the original integer.
def checkedCastBody (input output : Ident) (ty : ABI.IntType) : List Stmt :=
  [.letDecl output (some (.elem (.int ty))) (.intLit 0),
   .assign .localVar ⟨output, []⟩ (.cast (.var input) (.elem (.int ty))),
   .require (.binary .eq (.var output) (.var input)), .return [.var output]]

def checkedCastZeroFrame (frame : Frame) (output : Ident) : Frame :=
  {frame with locals := frame.locals.insert output (.int 0)}

def checkedCastFrame (frame : Frame) (output : Ident) (ty : ABI.IntType) (y : Int) : Frame :=
  {checkedCastZeroFrame frame output with
    locals := (checkedCastZeroFrame frame output).locals.insert output (.int (normalizeInt ty y))}

theorem checkedCastReadySource {cfg : Config} (frame : Frame) (evm : EVM.State)
    (input output : Ident) (ty : ABI.IntType) (y : Int)
    (hne : output ≠ input) (hy : frame.locals.get? input = some (.int y)) :
    ExecBlock cfg frame evm ((checkedCastBody input output ty).take 2)
      (.ok (checkedCastFrame frame output ty y) evm) := by
  refine ExecBlock.consNormal (solm' := checkedCastZeroFrame frame output)
    (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (value := .int (normalizeInt ty y)) ?_
    (assignLocalVarBase_frame Std.HashMap.getElem?_insert_self)) ExecBlock.nil
  have hy' : (checkedCastZeroFrame frame output).locals.get? input = some (.int y) := by
    simpa [checkedCastZeroFrame, Std.HashMap.getElem?_insert, hne] using hy
  have he := evalExpr_var_get (cfg := cfg) (evm := evm) hy'
  change evalExpr? cfg (checkedCastZeroFrame frame output) evm
    (.cast (.var input) (.elem (.int ty))) = _
  simp only [evalExpr?, he, castValue?, EvalResult.ofOption, bind, EvalResult.bind]

theorem evalCheckedCastGuard {cfg : Config} (frame : Frame) (evm : EVM.State)
    (input output : Ident) (ty : ABI.IntType) (y : Int)
    (hne : output ≠ input) (hy : frame.locals.get? input = some (.int y)) :
    evalExpr? cfg (checkedCastFrame frame output ty y) evm
      (.binary .eq (.var output) (.var input)) =
      .ok (.bool (decide (normalizeInt ty y = y))) := by
  have hy' : (checkedCastFrame frame output ty y).locals.get? input = some (.int y) := by
    simpa [checkedCastFrame, checkedCastZeroFrame, Std.HashMap.getElem?_insert, hne] using hy
  have he := evalExpr_var_get (cfg := cfg) (evm := evm) hy'
  have hz : evalExpr? cfg (checkedCastFrame frame output ty y) evm (.var output) =
      .ok (.int (normalizeInt ty y)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExpr?, he, hz, evalBinaryOp?, bind, EvalResult.bind]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, Value.int.injEq]

theorem checkedCastReturns {cfg : Config} (frame : Frame) (evm : EVM.State)
    (input output : Ident) (ty : ABI.IntType) (y : Int)
    (hne : output ≠ input) (hy : frame.locals.get? input = some (.int y))
    (hcast : normalizeInt ty y = y) :
    ExecFuncBody cfg frame evm (checkedCastBody input output ty)
      (.returned (checkedCastFrame frame output ty y) evm (some [.int y])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 2 (checkedCastBody input output ty)]
  apply execBlock_append_ok (checkedCastReadySource frame evm input output ty y hne hy)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hcast, decide_true] using evalCheckedCastGuard frame evm input output ty y hne hy
  refine ExecBlock.consReturn (ExecStmt.return ?_)
  have hz : (checkedCastFrame frame output ty y).locals.get? output = some (.int y) := by
    change ((checkedCastZeroFrame frame output).locals.insert output (.int (normalizeInt ty y)))[output]? = _
    rw [hcast, Std.HashMap.getElem?_insert_self]
  have he := evalExpr_var_get (cfg := cfg) (evm := evm) hz
  simp only [checkedCastBody, List.drop, evalExprs?, he, bind, EvalResult.bind, pure]

theorem checkedCastReverts {cfg : Config} (frame : Frame) (evm : EVM.State)
    (input output : Ident) (ty : ABI.IntType) (y : Int)
    (hne : output ≠ input) (hy : frame.locals.get? input = some (.int y))
    (hcast : normalizeInt ty y ≠ y) :
    ExecFuncBody cfg frame evm (checkedCastBody input output ty) .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 (checkedCastBody input output ty)]
  apply execBlock_append_ok (checkedCastReadySource frame evm input output ty y hne hy)
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    simpa only [hcast, decide_false] using evalCheckedCastGuard frame evm input output ty y hne hy))

end Benchmarks.UniswapV3.Pool
