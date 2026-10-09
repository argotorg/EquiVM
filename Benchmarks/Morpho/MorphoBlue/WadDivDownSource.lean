import Benchmarks.Morpho.MorphoBlue.WadSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev wDivDownFunction : FunctionDecl := contract.functions[12]!

def wDivDownResult (x y : UInt256) : UInt256 := UInt256.div (UInt256.mul x wad) y

def wDivDownResultFrame (x y : UInt256) (imms : Store) : Frame :=
  { mathBinaryFrame x y imms with locals :=
      (mathBinaryFrame x y imms).locals.insert "__c0" (.int (Int.ofNat (wDivDownResult x y).toNat)) }

theorem morphoWDivDownBodyOk (x y : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : x.toNat * wad.toNat < UInt256.size) (hn : y ≠ ⟨0⟩) :
    ExecFuncBody config (mathBinaryFrame x y imms) evm wDivDownFunction.body
      (.returned (wDivDownResultFrame x y imms) evm (some [.int (Int.ofNat (wDivDownResult x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (morphoMulDivDownCallOk x wad y evm _ imms _ _ _ _
    (mathBinary_eval_x x y imms evm) (evalWad _ evm) (mathBinary_eval_y x y imms evm) hfit hn)
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  rfl

theorem morphoWDivDownBodyReverts (x y : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : UInt256.size ≤ x.toNat * wad.toNat ∨ y = ⟨0⟩) :
    ExecFuncBody config (mathBinaryFrame x y imms) evm wDivDownFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (morphoMulDivDownCallReverts x wad y evm _ imms _ _ _ _
    (mathBinary_eval_x x y imms evm) (evalWad _ evm) (mathBinary_eval_y x y imms evm) hbad)

theorem morphoWDivDownCallOk (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat))) (hfit : x.toNat * wad.toNat < UInt256.size) (hn : y ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wDivDown" [ex, ey] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (wDivDownResult x y).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := wDivDownFunction)
    (value := some [.int (Int.ofNat (wDivDownResult x y).toNat)])
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (morphoWDivDownBodyOk x y evm imms hfit hn)

theorem morphoWDivDownCallReverts (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat))) (hbad : UInt256.size ≤ x.toNat * wad.toNat ∨ y = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wDivDown" [ex, ey] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := wDivDownFunction)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]) rfl rfl
    (morphoWDivDownBodyReverts x y evm imms hbad)

end Benchmarks.Morpho.MorphoBlue
