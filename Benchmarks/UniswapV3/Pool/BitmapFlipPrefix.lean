import Benchmarks.UniswapV3.Pool.BitmapPositionSource
import Benchmarks.UniswapV3.Pool.WordXor
import Benchmarks.UniswapV3.Pool.SourceWordMask

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def bitmapFlipFunction : FunctionDecl := contract.functions[43]!

theorem bitmapFlipLookup :
    lookupCallable? contract "TickBitmap_flipTick" = some bitmapFlipFunction.toCallable := rfl

def bitmapFlipLocals (tick spacing : Int) : Store :=
  ((∅ : Store).insert "tickSpacing" (.int spacing)).insert "tick" (.int tick)

def bitmapFlipFrame (imms : Store) (tick spacing : Int) : Frame :=
  {contract := contract, locals := bitmapFlipLocals tick spacing, immutables := imms}

def bitmapFlipCallFrame (imms : Store) (tick spacing : Int) : Frame :=
  {bitmapFlipFrame imms tick spacing with
    locals := (bitmapFlipLocals tick spacing).insert "__c0"
      (.tuple [.int (bitmapWordPos (tick.tdiv spacing)), .int (bitmapBitPos (tick.tdiv spacing))])}

def bitmapFlipWordFrame (imms : Store) (tick spacing : Int) : Frame :=
  {bitmapFlipCallFrame imms tick spacing with
    locals := (bitmapFlipCallFrame imms tick spacing).locals.insert "wordPos"
      (.int (bitmapWordPos (tick.tdiv spacing)))}

def bitmapFlipBitFrame (imms : Store) (tick spacing : Int) : Frame :=
  {bitmapFlipWordFrame imms tick spacing with
    locals := (bitmapFlipWordFrame imms tick spacing).locals.insert "bitPos"
      (.int (bitmapBitPos (tick.tdiv spacing)))}

def bitmapFlipMask (tick spacing : Int) : UInt256 :=
  UInt256.ofNat (2 ^ (bitmapBitPos (tick.tdiv spacing)).toNat)

def bitmapFlipReadyFrame (imms : Store) (tick spacing : Int) : Frame :=
  {bitmapFlipBitFrame imms tick spacing with
    locals := (bitmapFlipBitFrame imms tick spacing).locals.insert "mask"
      (.int (Int.ofNat (bitmapFlipMask tick spacing).toNat))}

theorem bitmapFlipBind (tick spacing : Int) :
    bindParams? bitmapFlipFunction.params [.int tick, .int spacing] =
      some (bitmapFlipLocals tick spacing) := rfl

theorem bitmapFlipInitialGet (imms : Store) (tick spacing : Int) :
    (bitmapFlipFrame imms tick spacing).locals.get? "tick" = some (.int tick) ∧
    (bitmapFlipFrame imms tick spacing).locals.get? "tickSpacing" = some (.int spacing) := by
  simp only [bitmapFlipFrame, bitmapFlipLocals,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact ⟨rfl, rfl⟩

theorem evalBitmapFlipGuard (imms : Store) (evm : EVM.State) (tick spacing : Int)
    (hn : spacing ≠ 0) :
    evalExpr? config (bitmapFlipFrame imms tick spacing) evm
      (.binary .eq (.binary .srem (.var "tick") (.var "tickSpacing")) (.intLit 0)) =
      .ok (.bool (decide (tick.tmod spacing = 0))) := by
  have ht := evalExpr_var_get (cfg := config) (evm := evm) (bitmapFlipInitialGet imms tick spacing).1
  have hs := evalExpr_var_get (cfg := config) (evm := evm) (bitmapFlipInitialGet imms tick spacing).2
  simp only [evalExpr?, ht, hs, evalBinaryOp?, hn, if_false, bind, EvalResult.bind, pure]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, Value.int.injEq]

theorem bitmapFlipRevertsZero (imms : Store) (evm : EVM.State) (tick : Int) :
    ExecFuncBody config (bitmapFlipFrame imms tick 0) evm bitmapFlipFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.requireRevert
  have ht := evalExpr_var_get (cfg := config) (evm := evm) (bitmapFlipInitialGet imms tick 0).1
  have hs := evalExpr_var_get (cfg := config) (evm := evm) (bitmapFlipInitialGet imms tick 0).2
  simp only [evalExpr?, ht, hs, evalBinaryOp?, if_true, bind, EvalResult.bind, pure]

theorem bitmapFlipRevertsRemainder (imms : Store) (evm : EVM.State) (tick spacing : Int)
    (hn : spacing ≠ 0) (hr : tick.tmod spacing ≠ 0) :
    ExecFuncBody config (bitmapFlipFrame imms tick spacing) evm bitmapFlipFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse
    (by simpa only [hr, decide_false] using evalBitmapFlipGuard imms evm tick spacing hn)))

theorem bitmapFlipPositionCall (imms : Store) (evm : EVM.State) (tick spacing : Int)
    (hn : spacing ≠ 0) :
    ExecStmt config (bitmapFlipFrame imms tick spacing) evm (bitmapFlipFunction.body[1]!)
      (.ok (bitmapFlipCallFrame imms tick spacing) evm) := by
  have ht := evalExpr_var_get (cfg := config) (evm := evm) (bitmapFlipInitialGet imms tick spacing).1
  have hs := evalExpr_var_get (cfg := config) (evm := evm) (bitmapFlipInitialGet imms tick spacing).2
  exact internalCallFunctionReturn (callee := bitmapPositionFunction)
    (locals := bitmapPositionLocals (tick.tdiv spacing))
    (calleeSolm := bitmapPositionReadyFrame imms (tick.tdiv spacing))
    (value := some [.int (bitmapWordPos (tick.tdiv spacing)), .int (bitmapBitPos (tick.tdiv spacing))])
    (by simp only [evalExprs?, evalExpr?, ht, hs, evalBinaryOp?, hn, if_false,
      bind, EvalResult.bind, pure]) bitmapPositionLookup (bitmapPositionBind (tick.tdiv spacing))
    (bitmapPositionReturns imms evm (tick.tdiv spacing))

theorem evalBitmapFlipMask (imms : Store) (evm : EVM.State) (tick spacing : Int) :
    evalExpr? config (bitmapFlipBitFrame imms tick spacing) evm
      (.binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1) (.var "bitPos")) =
      .ok (.int (Int.ofNat (bitmapFlipMask tick spacing).toNat)) :=
  evalExpr_one_shl_int (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (bitmapBitPos_bounds (tick.tdiv spacing))

theorem bitmapFlipReadySource (imms : Store) (evm : EVM.State) (tick spacing : Int)
    (hn : spacing ≠ 0) (hr : tick.tmod spacing = 0) :
    ExecBlock config (bitmapFlipFrame imms tick spacing) evm (bitmapFlipFunction.body.take 5)
      (.ok (bitmapFlipReadyFrame imms tick spacing) evm) := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by simpa only [hr, decide_true] using evalBitmapFlipGuard imms evm tick spacing hn)) ?_
  refine ExecBlock.consNormal (bitmapFlipPositionCall imms evm tick spacing hn) ?_
  refine ExecBlock.consNormal (solm' := bitmapFlipWordFrame imms tick spacing)
    (ExecStmt.letDecl ?_) ?_
  · have he : evalExpr? config (bitmapFlipCallFrame imms tick spacing) evm (.var "__c0") =
        .ok (.tuple [.int (bitmapWordPos (tick.tdiv spacing)),
          .int (bitmapBitPos (tick.tdiv spacing))]) :=
      evalExpr_var_get Std.HashMap.getElem?_insert_self
    simp only [evalExpr?, he, bind, EvalResult.bind, pure, EvalResult.ofOption]
    rfl
  · refine ExecBlock.consNormal (solm' := bitmapFlipBitFrame imms tick spacing)
      (ExecStmt.letDecl ?_) ?_
    · have hg : (bitmapFlipWordFrame imms tick spacing).locals.get? "__c0" =
          some (.tuple [.int (bitmapWordPos (tick.tdiv spacing)),
            .int (bitmapBitPos (tick.tdiv spacing))]) := by
        simp only [bitmapFlipWordFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        exact Std.HashMap.getElem?_insert_self
      have he := evalExpr_var_get (cfg := config) (evm := evm) hg
      simp only [evalExpr?, he, bind, EvalResult.bind, pure, EvalResult.ofOption]
      rfl
    · exact ExecBlock.consNormal (ExecStmt.letDecl (evalBitmapFlipMask imms evm tick spacing))
        ExecBlock.nil

end Benchmarks.UniswapV3.Pool
