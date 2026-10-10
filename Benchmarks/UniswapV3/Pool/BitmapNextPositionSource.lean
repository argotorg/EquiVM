import Benchmarks.UniswapV3.Pool.BitmapNextPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitmapNextBranch (lte : Bool) : List Stmt :=
  match bitmapNextFunction.body[4]! with
  | .ite _ yes no => if lte then yes else no
  | _ => []

def bitmapNextCallName (lte : Bool) : String := if lte then "__c0" else "__c3"

def bitmapNextCallFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextPrefixFrame imms tick spacing lte with
    locals := (bitmapNextPrefixFrame imms tick spacing lte).locals.insert (bitmapNextCallName lte)
      (.tuple [.int (bitmapWordPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte)),
        .int (bitmapBitPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))])}

def bitmapNextWordFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextCallFrame imms tick spacing lte with
    locals := (bitmapNextCallFrame imms tick spacing lte).locals.insert "wordPos"
      (.int (bitmapWordPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte)))}

def bitmapNextBitFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextWordFrame imms tick spacing lte with
    locals := (bitmapNextWordFrame imms tick spacing lte).locals.insert "bitPos"
      (.int (bitmapBitPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte)))}

theorem bitmapNextPositionCall (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool) :
    ExecStmt config (bitmapNextPrefixFrame imms tick spacing lte) evm (bitmapNextBranch lte)[0]!
      (.ok (bitmapNextCallFrame imms tick spacing lte) evm) := by
  have ec := evalExpr_var_get (cfg := config) (evm := evm)
    (bitmapNextPrefixGet imms tick spacing lte).1
  cases lte <;>
    exact internalCallFunctionReturn (callee := bitmapPositionFunction)
      (locals := bitmapPositionLocals (bitmapNextPosition (bitmapNextCompressed tick spacing) _))
      (calleeSolm := bitmapPositionReadyFrame imms
        (bitmapNextPosition (bitmapNextCompressed tick spacing) _))
      (value := some [
        .int (bitmapWordPos (bitmapNextPosition (bitmapNextCompressed tick spacing) _)),
        .int (bitmapBitPos (bitmapNextPosition (bitmapNextCompressed tick spacing) _))])
      (by simp only [evalExprs?, evalExpr?, ec, evalBinaryOp?, castValue?,
        bind, EvalResult.bind, pure]; rfl) bitmapPositionLookup (bitmapPositionBind _)
      (bitmapPositionReturns imms evm _)

theorem bitmapNextPositionSource (imms : Store) (evm : EVM.State)
    (tick spacing : Int) (lte : Bool) :
    ExecBlock config (bitmapNextPrefixFrame imms tick spacing lte) evm
      ((bitmapNextBranch lte).take 3) (.ok (bitmapNextBitFrame imms tick spacing lte) evm) := by
  have ew : evalExpr? config (bitmapNextCallFrame imms tick spacing lte) evm
      (.tupleGet (.var (bitmapNextCallName lte)) 0) =
      .ok (.int (bitmapWordPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))) := by
    have he : evalExpr? config (bitmapNextCallFrame imms tick spacing lte) evm
        (.var (bitmapNextCallName lte)) = .ok (.tuple [
          .int (bitmapWordPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte)),
          .int (bitmapBitPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))]) :=
      evalExpr_var_get Std.HashMap.getElem?_insert_self
    simp only [evalExpr?, he, bind, EvalResult.bind]
    rfl
  have eb : evalExpr? config (bitmapNextWordFrame imms tick spacing lte) evm
      (.tupleGet (.var (bitmapNextCallName lte)) 1) =
      .ok (.int (bitmapBitPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))) := by
    have hg : (bitmapNextWordFrame imms tick spacing lte).locals.get? (bitmapNextCallName lte) =
        some (.tuple [
          .int (bitmapWordPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte)),
          .int (bitmapBitPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))]) := by
      cases lte <;>
        simp [bitmapNextWordFrame, bitmapNextCallFrame, bitmapNextCallName,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert]
    have he := evalExpr_var_get (cfg := config) (evm := evm) hg
    simp only [evalExpr?, he, bind, EvalResult.bind]
    rfl
  cases lte <;>
    exact ExecBlock.consNormal (bitmapNextPositionCall imms evm tick spacing _)
      (ExecBlock.consNormal (ExecStmt.letDecl ew)
        (ExecBlock.consNormal (ExecStmt.letDecl eb) ExecBlock.nil))

end Benchmarks.UniswapV3.Pool
