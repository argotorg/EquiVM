import Benchmarks.UniswapV3.Pool.BitmapNextPositionSource
import Benchmarks.UniswapV3.Pool.SourceWordMask

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitmapNextMaskFrame (imms : Store) (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextBitFrame imms tick spacing lte with
    locals := (bitmapNextBitFrame imms tick spacing lte).locals.insert "mask"
      (.int (Int.ofNat (bitmapNextMask (bitmapNextCompressed tick spacing) lte).toNat))}

theorem evalBitmapNextMask (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool) :
    let expr := match (bitmapNextBranch lte)[3]! with | .letDecl _ _ e => e | _ => .intLit 0
    evalExpr? config (bitmapNextBitFrame imms tick spacing lte) evm expr =
      .ok (.int (Int.ofNat (bitmapNextMask (bitmapNextCompressed tick spacing) lte).toNat)) := by
  have hb : evalExpr? config (bitmapNextBitFrame imms tick spacing lte) evm (.var "bitPos") =
      .ok (.int (bitmapBitPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  have he := evalExpr_one_shl_int hb
    (bitmapBitPos_bounds (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))
  have hone : evalExpr? config (bitmapNextBitFrame imms tick spacing lte) evm (.intLit 1) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) := by simp only [evalExpr?, pure]; rfl
  cases lte
  · exact evalExpr_word_lnot (evalExpr_word_sub he hone)
  · exact evalExpr_word_add (evalExpr_word_sub he hone) he

theorem bitmapNextMaskSource (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool) :
    ExecStmt config (bitmapNextBitFrame imms tick spacing lte) evm (bitmapNextBranch lte)[3]!
      (.ok (bitmapNextMaskFrame imms tick spacing lte) evm) := by
  have he := evalBitmapNextMask imms evm tick spacing lte
  cases lte <;> exact ExecStmt.letDecl he

end Benchmarks.UniswapV3.Pool
