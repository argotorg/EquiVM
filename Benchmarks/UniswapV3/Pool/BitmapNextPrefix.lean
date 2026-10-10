import Benchmarks.UniswapV3.Pool.BitmapNextModel
import Benchmarks.UniswapV3.Pool.SourceSignedDivision

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitmapNextNextZeroFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextFrame imms tick spacing lte with
    locals := (bitmapNextLocals tick spacing lte).insert "next" (.int 0)}

def bitmapNextZeroFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextNextZeroFrame imms tick spacing lte with
    locals := (bitmapNextNextZeroFrame imms tick spacing lte).locals.insert "initialized"
      (.bool false)}

def bitmapNextDivFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextZeroFrame imms tick spacing lte with
    locals := (bitmapNextZeroFrame imms tick spacing lte).locals.insert "compressed"
      (.int (tick.tdiv spacing))}

def bitmapNextPrefixFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextDivFrame imms tick spacing lte with
    locals := if bitmapNextAdjust tick spacing then
      (bitmapNextDivFrame imms tick spacing lte).locals.insert "compressed"
        (.int (bitmapNextCompressed tick spacing))
      else (bitmapNextDivFrame imms tick spacing lte).locals}

macro "bitmap_next_prefix_get" : tactic =>
  `(tactic| simp [bitmapNextDivFrame, bitmapNextZeroFrame, bitmapNextNextZeroFrame,
    bitmapNextFrame, bitmapNextLocals, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, beq_self_eq_true, ↓reduceIte])

def bitmapNextAdjustGuard : Expr :=
  .binary .and (.binary .lt (.var "tick") (.intLit 0))
    (.binary .ne (.binary .srem (.var "tick") (.var "tickSpacing")) (.intLit 0))

theorem evalBitmapNextAdjust {frame : Frame} {evm : EVM.State} (tick spacing : Int)
    (ht : frame.locals.get? "tick" = some (.int tick))
    (hs : frame.locals.get? "tickSpacing" = some (.int spacing)) (hn : spacing ≠ 0) :
    evalExpr? config frame evm bitmapNextAdjustGuard =
      .ok (.bool (decide (bitmapNextAdjust tick spacing))) := by
  have et := evalExpr_var_get (cfg := config) (evm := evm) ht
  have es := evalExpr_var_get (cfg := config) (evm := evm) hs
  have ez : evalExpr? config frame evm (.intLit 0) = .ok (.int 0) := by
    simp only [evalExpr?, pure]
  simpa only [bitmapNextAdjustGuard, bitmapNextAdjust, Bool.decide_and] using
    evalExpr_bool_and (evalExpr_int_lt et ez) (evalExpr_int_ne (evalExpr_int_srem et es hn) ez)

theorem bitmapNextRevertsZero (imms : Store) (evm : EVM.State) (tick : Int) (lte : Bool) :
    ExecFuncBody config (bitmapNextFrame imms tick 0 lte) evm
      bitmapNextFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (solm' := bitmapNextNextZeroFrame imms tick 0 lte)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := bitmapNextZeroFrame imms tick 0 lte)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  have et := evalExpr_var_get (cfg := config) (evm := evm)
    (show (bitmapNextZeroFrame imms tick 0 lte).locals.get? "tick" = some (.int tick) by
      bitmap_next_prefix_get)
  have es := evalExpr_var_get (cfg := config) (evm := evm)
    (show (bitmapNextZeroFrame imms tick 0 lte).locals.get? "tickSpacing" = some (.int 0) by
      bitmap_next_prefix_get)
  simp only [evalExpr?, et, es, evalBinaryOp?, if_true, bind, EvalResult.bind]

theorem bitmapNextPrefixSource (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool)
    (hn : spacing ≠ 0) :
    ExecBlock config (bitmapNextFrame imms tick spacing lte) evm (bitmapNextFunction.body.take 4)
      (.ok (bitmapNextPrefixFrame imms tick spacing lte) evm) := by
  refine ExecBlock.consNormal (solm' := bitmapNextNextZeroFrame imms tick spacing lte)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := bitmapNextZeroFrame imms tick spacing lte)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := bitmapNextDivFrame imms tick spacing lte)
    (ExecStmt.letDecl (evalExpr_int_sdiv
      (evalExpr_var_get (by bitmap_next_prefix_get))
      (evalExpr_var_get (by bitmap_next_prefix_get)) hn)) ?_
  have hg := evalBitmapNextAdjust (evm := evm) tick spacing
    (frame := bitmapNextDivFrame imms tick spacing lte)
    (by bitmap_next_prefix_get) (by bitmap_next_prefix_get) hn
  by_cases h : bitmapNextAdjust tick spacing
  · rw [bitmapNextPrefixFrame, if_pos h]
    refine ExecBlock.consNormal (ExecStmt.iteTrue
      (by simpa only [h, decide_true] using hg) ?_) ExecBlock.nil
    refine ExecBlock.consNormal (ExecStmt.assign (value := .int (bitmapNextCompressed tick spacing))
      ?_ (assignLocalVarBase_frame Std.HashMap.getElem?_insert_self)) ExecBlock.nil
    have ec : evalExpr? config (bitmapNextDivFrame imms tick spacing lte) evm (.var "compressed") =
        .ok (.int (tick.tdiv spacing)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
    simp only [evalExpr?, ec, evalBinaryOp?, castValue?, bind, EvalResult.bind,
      EvalResult.ofOption, bitmapNextCompressed, if_pos h]
  · rw [bitmapNextPrefixFrame, if_neg h]
    exact ExecBlock.consNormal (ExecStmt.iteFalse
      (by simpa only [h, decide_false] using hg) ExecBlock.nil) ExecBlock.nil

theorem bitmapNextPrefixGet (imms : Store) (tick spacing : Int) (lte : Bool) :
    (bitmapNextPrefixFrame imms tick spacing lte).locals.get? "compressed" =
        some (.int (bitmapNextCompressed tick spacing)) ∧
      (bitmapNextPrefixFrame imms tick spacing lte).locals.get? "tickSpacing" =
        some (.int spacing) ∧
      (bitmapNextPrefixFrame imms tick spacing lte).locals.get? "lte" = some (.bool lte) ∧
      (bitmapNextPrefixFrame imms tick spacing lte).locals.get? "next" = some (.int 0) ∧
      (bitmapNextPrefixFrame imms tick spacing lte).locals.get? "initialized" = some (.bool false) ∧
      (bitmapNextPrefixFrame imms tick spacing lte).locals.get? "tickBitmap" = none := by
  by_cases h : bitmapNextAdjust tick spacing <;>
    simp only [bitmapNextPrefixFrame, bitmapNextCompressed, h, ↓reduceIte] <;>
    bitmap_next_prefix_get

end Benchmarks.UniswapV3.Pool
