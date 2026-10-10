import Benchmarks.UniswapV3.Pool.SignedRemainder
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def bitmapWordPos (tick : Int) : Int := normalizeInt (.sint ⟨24, by decide⟩) tick / 256

def bitmapBitPos (tick : Int) : Int := normalizeInt (.uint ⟨8, by decide⟩) tick

theorem bitmapWordPos_bounds (tick : Int) :
    -(2 ^ 15 : Int) ≤ bitmapWordPos tick ∧ bitmapWordPos tick < 2 ^ 15 := by
  have hb := normalizeSint_bounds ⟨24, by decide⟩ tick
  change -(2 ^ 23 : Int) ≤ normalizeInt (.sint ⟨24, by decide⟩) tick ∧
    normalizeInt (.sint ⟨24, by decide⟩) tick < 2 ^ 23 at hb
  unfold bitmapWordPos
  omega

theorem bitmapBitPos_bounds (tick : Int) : 0 ≤ bitmapBitPos tick ∧ bitmapBitPos tick < 256 := by
  change 0 ≤ tick % 256 ∧ tick % 256 < 256
  omega

theorem bitmapBitPos_tmod (tick : Int) :
    normalizeInt (.uint ⟨8, by decide⟩) (tick.tmod 256) = bitmapBitPos tick :=
  tmod_emod tick 256

def bitmapPositionFunction : FunctionDecl := contract.functions[33]!

theorem bitmapPositionLookup :
    lookupCallable? contract "TickBitmap_position" = some bitmapPositionFunction.toCallable := rfl

def bitmapPositionLocals (tick : Int) : Store := (∅ : Store).insert "tick" (.int tick)

def bitmapPositionFrame (imms : Store) (tick : Int) : Frame :=
  {contract := contract, locals := bitmapPositionLocals tick, immutables := imms}

def bitmapPositionWordZeroFrame (imms : Store) (tick : Int) : Frame :=
  {bitmapPositionFrame imms tick with
    locals := (bitmapPositionLocals tick).insert "wordPos" (.int 0)}

def bitmapPositionZeroFrame (imms : Store) (tick : Int) : Frame :=
  {bitmapPositionWordZeroFrame imms tick with
    locals := (bitmapPositionWordZeroFrame imms tick).locals.insert "bitPos" (.int 0)}

def bitmapPositionWordFrame (imms : Store) (tick : Int) : Frame :=
  {bitmapPositionZeroFrame imms tick with
    locals := (bitmapPositionZeroFrame imms tick).locals.insert "wordPos" (.int (bitmapWordPos tick))}

def bitmapPositionReadyFrame (imms : Store) (tick : Int) : Frame :=
  {bitmapPositionWordFrame imms tick with
    locals := (bitmapPositionWordFrame imms tick).locals.insert "bitPos" (.int (bitmapBitPos tick))}

theorem bitmapPositionBind (tick : Int) :
    bindParams? bitmapPositionFunction.params [.int tick] = some (bitmapPositionLocals tick) := rfl

theorem bitmapPositionGetTick (imms : Store) (tick : Int) :
    (bitmapPositionZeroFrame imms tick).locals.get? "tick" = some (.int tick) ∧
    (bitmapPositionWordFrame imms tick).locals.get? "tick" = some (.int tick) := by
  simp only [bitmapPositionZeroFrame, bitmapPositionWordZeroFrame, bitmapPositionWordFrame,
    bitmapPositionLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl⟩

theorem bitmapPositionGetResult (imms : Store) (tick : Int) :
    (bitmapPositionReadyFrame imms tick).locals.get? "wordPos" =
      some (.int (bitmapWordPos tick)) ∧
    (bitmapPositionReadyFrame imms tick).locals.get? "bitPos" =
      some (.int (bitmapBitPos tick)) := by
  simp only [bitmapPositionReadyFrame, bitmapPositionWordFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl⟩

theorem bitmapPositionReturns (imms : Store) (evm : EVM.State) (tick : Int) :
    ExecFuncBody config (bitmapPositionFrame imms tick) evm bitmapPositionFunction.body
      (.returned (bitmapPositionReadyFrame imms tick) evm
        (some [.int (bitmapWordPos tick), .int (bitmapBitPos tick)])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (solm' := bitmapPositionWordZeroFrame imms tick)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := bitmapPositionZeroFrame imms tick)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := bitmapPositionWordFrame imms tick) (evm' := evm)
    (ExecStmt.assign (value := .int (bitmapWordPos tick)) ?_ ?_) ?_
  · have he := evalExpr_var_get (cfg := config) (evm := evm)
      (bitmapPositionGetTick imms tick).1
    change evalExpr? config (bitmapPositionZeroFrame imms tick) evm
      (.cast (.binary (.shr (.sint ⟨24, by decide⟩)) (.var "tick") (.intLit 8))
        (.elem (.int (.sint ⟨16, by decide⟩)))) = _
    simp only [evalExpr?, he, evalBinaryOp?, castValue?, EvalResult.ofOption, bind,
      EvalResult.bind, pure, show ¬ (8 : Int) < 0 by decide, ↓reduceIte]
    change EvalResult.ok (Value.int (normalizeInt (.sint ⟨16, by decide⟩) (bitmapWordPos tick))) =
      EvalResult.ok (Value.int (bitmapWordPos tick))
    rw [normalizeSint_eq_self ⟨16, by decide⟩ _
      (bitmapWordPos_bounds tick).1 (bitmapWordPos_bounds tick).2]
  · apply assignLocalVarBase_frame
    simp only [bitmapPositionZeroFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    exact Std.HashMap.getElem?_insert_self
  · refine ExecBlock.consNormal (solm' := bitmapPositionReadyFrame imms tick) (evm' := evm)
      (ExecStmt.assign (value := .int (bitmapBitPos tick)) ?_ ?_) ?_
    · have he := evalExpr_var_get (cfg := config) (evm := evm)
        (bitmapPositionGetTick imms tick).2
      change evalExpr? config (bitmapPositionWordFrame imms tick) evm
        (.cast (.binary .srem (.var "tick") (.intLit 256))
          (.elem (.int (.uint ⟨8, by decide⟩)))) = _
      simp only [evalExpr?, he, evalBinaryOp?, castValue?, EvalResult.ofOption, bind,
        EvalResult.bind, pure, show (256 : Int) ≠ 0 by decide, if_false, bitmapBitPos_tmod]
    · apply assignLocalVarBase_frame
      simp only [bitmapPositionWordFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]
      exact Std.HashMap.getElem?_insert_self
    · refine ExecBlock.consReturn (ExecStmt.return ?_)
      have hw := evalExpr_var_get (cfg := config) (evm := evm)
        (bitmapPositionGetResult imms tick).1
      have hb := evalExpr_var_get (cfg := config) (evm := evm)
        (bitmapPositionGetResult imms tick).2
      simp only [evalExprs?, hw, hb, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
