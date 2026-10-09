import Benchmarks.Morpho.MorphoBlue.TaylorSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev wMulDownFunction : FunctionDecl := contract.functions[13]!

def mathBinaryFrame (x y : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x" (.int (Int.ofNat x.toNat)) }

theorem mathBinary_eval_x (x y : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (mathBinaryFrame x y imms) evm (.var "x") = .ok (.int (Int.ofNat x.toNat)) := by
  simp only [evalExpr?, mathBinaryFrame, store_get_self, EvalResult.ofOption]

theorem mathBinary_eval_y (x y : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (mathBinaryFrame x y imms) evm (.var "y") = .ok (.int (Int.ofNat y.toNat)) := by
  simp only [evalExpr?, mathBinaryFrame, store_get_ne (k := "x") (a := "y") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem evalWad (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm (.intLit 1000000000000000000) = .ok (.int (Int.ofNat wad.toNat)) := by
  simp only [evalExpr?, pure]
  rfl

def wMulDownResult (x y : UInt256) : UInt256 := UInt256.div (UInt256.mul x y) wad

def wMulDownResultFrame (x y : UInt256) (imms : Store) : Frame :=
  { mathBinaryFrame x y imms with locals :=
      (mathBinaryFrame x y imms).locals.insert "__c0" (.int (Int.ofNat (wMulDownResult x y).toNat)) }

theorem morphoWMulDownBodyOk (x y : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config (mathBinaryFrame x y imms) evm wMulDownFunction.body
      (.returned (wMulDownResultFrame x y imms) evm (some [.int (Int.ofNat (wMulDownResult x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (morphoMulDivDownCallOk x y wad evm _ imms _ _ _ _
    (mathBinary_eval_x x y imms evm) (mathBinary_eval_y x y imms evm) (evalWad _ evm) hfit (by decide))
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  rfl

theorem morphoWMulDownBodyReverts (x y : UInt256) (evm : EVM.State) (imms : Store)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config (mathBinaryFrame x y imms) evm wMulDownFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (morphoMulDivDownCallReverts x y wad evm _ imms _ _ _ _
    (mathBinary_eval_x x y imms evm) (mathBinary_eval_y x y imms evm) (evalWad _ evm) (.inl hover))

theorem morphoWMulDownCallOk (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat))) (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wMulDown" [ex, ey] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (wMulDownResult x y).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := wMulDownFunction)
    (value := some [.int (Int.ofNat (wMulDownResult x y).toNat)])
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (morphoWMulDownBodyOk x y evm imms hfit)

theorem morphoWMulDownCallReverts (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat))) (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wMulDown" [ex, ey] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := wMulDownFunction)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (morphoWMulDownBodyReverts x y evm imms hover)

end Benchmarks.Morpho.MorphoBlue
