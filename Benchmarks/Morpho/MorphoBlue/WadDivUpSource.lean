import Benchmarks.Morpho.MorphoBlue.WadSource
import Benchmarks.Morpho.MorphoBlue.MulDivUpSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev wDivUpFunction : FunctionDecl := contract.functions[18]!

def wDivUpResult (x y : UInt256) : UInt256 := mulDivUpWord x wad y

def wDivUpResultFrame (x y : UInt256) (imms : Store) : Frame :=
  { mathBinaryFrame x y imms with locals :=
      (mathBinaryFrame x y imms).locals.insert "result" (.int (Int.ofNat (wDivUpResult x y).toNat)) }

theorem morphoWDivUpBodyOk (x y : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : MulDivUpFits x wad y) :
    ExecFuncBody config (mathBinaryFrame x y imms) evm wDivUpFunction.body
      (.returned (wDivUpResultFrame x y imms) evm (some [.int (Int.ofNat (wDivUpResult x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (morphoMulDivUpCallOk x wad y evm _ imms _ _ _ _
    (mathBinary_eval_x x y imms evm) (evalWad _ evm) (mathBinary_eval_y x y imms evm) hfit)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  rfl

theorem morphoWDivUpBodyReverts (x y : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : ¬ MulDivUpFits x wad y) :
    ExecFuncBody config (mathBinaryFrame x y imms) evm wDivUpFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (morphoMulDivUpCallReverts x wad y evm _ imms _ _ _ _
    (mathBinary_eval_x x y imms evm) (evalWad _ evm) (mathBinary_eval_y x y imms evm) hbad)

theorem morphoWDivUpCallOk (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat))) (hfit : MulDivUpFits x wad y) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wDivUp" [ex, ey] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (wDivUpResult x y).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := wDivUpFunction)
    (value := some [.int (Int.ofNat (wDivUpResult x y).toNat)])
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (morphoWDivUpBodyOk x y evm imms hfit)

theorem morphoWDivUpCallReverts (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat))) (hbad : ¬ MulDivUpFits x wad y) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wDivUp" [ex, ey] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := wDivUpFunction)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (morphoWDivUpBodyReverts x y evm imms hbad)

end Benchmarks.Morpho.MorphoBlue
