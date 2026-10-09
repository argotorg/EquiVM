import Benchmarks.Morpho.MorphoBlue.WadSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev minFunction : FunctionDecl := contract.functions[11]!

def minWord (x y : UInt256) : UInt256 := if x.toNat < y.toNat then x else y

theorem evalMinWord {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg frame evm (.ite (.binary .lt ex ey) ex ey) =
      .ok (.int (Int.ofNat (minWord x y).toNat)) := by
  have hlt : evalExpr? cfg frame evm (.binary .lt ex ey) = .ok (.bool (decide (x.toNat < y.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]
  by_cases h : x.toNat < y.toNat
  · simp only [evalExpr?, hlt, decide_eq_true h, bind, EvalResult.bind, hx, minWord, if_pos h]
  · simp only [evalExpr?, hlt, decide_eq_false h, bind, EvalResult.bind, hy, minWord, if_neg h]

theorem morphoMinBody (x y : UInt256) (evm : EVM.State) (imms : Store) :
    ExecFuncBody config (mathBinaryFrame x y imms) evm minFunction.body
      (.returned (mathBinaryFrame x y imms) evm (some [.int (Int.ofNat (minWord x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  exact evalMinWord (mathBinary_eval_x x y imms evm) (mathBinary_eval_y x y imms evm)

theorem morphoMinCall (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_min" [ex, ey] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (minWord x y).toNat)),
              immutables := imms } evm) :=
  internalCallFunctionReturn (callee := minFunction)
    (value := some [.int (Int.ofNat (minWord x y).toNat)])
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl (morphoMinBody x y evm imms)

end Benchmarks.Morpho.MorphoBlue
