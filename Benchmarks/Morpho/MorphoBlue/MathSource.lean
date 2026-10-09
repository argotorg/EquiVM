import Benchmarks.Morpho.MorphoBlue.BodyCommon
import Reasoning.SolmArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev mulDivDownFunction : FunctionDecl := contract.functions[15]!

def mulDivArgs (x y d : UInt256) : Store :=
  (((∅ : Store).insert "d" (.int (Int.ofNat d.toNat))).insert "y" (.int (Int.ofNat y.toNat))).insert
    "x" (.int (Int.ofNat x.toNat))

def mulDivFrame (x y d : UInt256) (imms : Store) : Frame :=
  { contract := contract, locals := mulDivArgs x y d, immutables := imms }

theorem mulDiv_eval_x (x y d : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (mulDivFrame x y d imms) evm (.var "x") = .ok (.int (Int.ofNat x.toNat)) := by
  simp only [evalExpr?, mulDivFrame, mulDivArgs, store_get_self, EvalResult.ofOption]

theorem mulDiv_eval_y (x y d : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (mulDivFrame x y d imms) evm (.var "y") = .ok (.int (Int.ofNat y.toNat)) := by
  simp only [evalExpr?, mulDivFrame, mulDivArgs,
    store_get_ne (k := "x") (a := "y") _ _ (by decide), store_get_self, EvalResult.ofOption]

theorem mulDiv_eval_d (x y d : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (mulDivFrame x y d imms) evm (.var "d") = .ok (.int (Int.ofNat d.toNat)) := by
  simp only [evalExpr?, mulDivFrame, mulDivArgs,
    store_get_ne (k := "x") (a := "d") _ _ (by decide),
    store_get_ne (k := "y") (a := "d") _ _ (by decide), store_get_self, EvalResult.ofOption]

def mulDivDownExpr (x y d : Expr) : Expr :=
  .binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul x y)) d

theorem evalMulDivDownOk {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey ed : Expr}
    {x y d : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? cfg frame evm ed = .ok (.int (Int.ofNat d.toNat)))
    (hfit : x.toNat * y.toNat < UInt256.size) (hn : d ≠ ⟨0⟩) :
    evalExpr? cfg frame evm (mulDivDownExpr ex ey ed) =
      .ok (.int (Int.ofNat (UInt256.div (UInt256.mul x y) d).toNat)) :=
  divSourceOk (checkedMulSourceOk hx hy hfit) hd hn

theorem evalMulDivDownReverts {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey ed : Expr}
    {x y d : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? cfg frame evm ed = .ok (.int (Int.ofNat d.toNat)))
    (hbad : UInt256.size ≤ x.toNat * y.toNat ∨ d = ⟨0⟩) :
    evalExpr? cfg frame evm (mulDivDownExpr ex ey ed) = .revert := by
  by_cases hfit : x.toNat * y.toNat < UInt256.size
  · have hz := hbad.resolve_left (Nat.not_le_of_lt hfit)
    have hm := checkedMulSourceOk hx hy hfit
    simp only [mulDivDownExpr, evalExpr?, hm, hd, hz, bind, EvalResult.bind, evalBinaryOp?]
    rfl
  · have hm := checkedMulSourceOverflow hx hy (Nat.le_of_not_gt hfit)
    simp only [mulDivDownExpr, evalExpr?, hm, bind, EvalResult.bind]

theorem morphoMulDivDownBodyOk (x y d : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : x.toNat * y.toNat < UInt256.size) (hn : d ≠ ⟨0⟩) :
    ExecFuncBody config (mulDivFrame x y d imms) evm mulDivDownFunction.body
      (.returned (mulDivFrame x y d imms) evm
        (some [.int (Int.ofNat (UInt256.div (UInt256.mul x y) d).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  exact evalExprs?_singleton (evalMulDivDownOk (mulDiv_eval_x x y d imms evm)
    (mulDiv_eval_y x y d imms evm) (mulDiv_eval_d x y d imms evm) hfit hn)

theorem morphoMulDivDownBodyReverts (x y d : UInt256) (evm : EVM.State) (imms : Store)
    (hbad : UInt256.size ≤ x.toNat * y.toNat ∨ d = ⟨0⟩) :
    ExecFuncBody config (mulDivFrame x y d imms) evm mulDivDownFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  have hr := evalMulDivDownReverts (mulDiv_eval_x x y d imms evm)
    (mulDiv_eval_y x y d imms evm) (mulDiv_eval_d x y d imms evm) hbad
  change evalExprs? _ _ _ [mulDivDownExpr (.var "x") (.var "y") (.var "d")] = _
  simp only [evalExprs?, hr, bind, EvalResult.bind]

theorem morphoMulDivDownCallOk (x y d : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey ed : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ed =
      .ok (.int (Int.ofNat d.toNat)))
    (hfit : x.toNat * y.toNat < UInt256.size) (hn : d ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_mulDivDown" [ex, ey, ed] retVar)
      (.ok { contract := contract, locals := (locals.insert retVar
          (.int (Int.ofNat (UInt256.div (UInt256.mul x y) d).toNat))), immutables := imms } evm) := by
  apply internalCallFunctionReturn (callee := mulDivDownFunction)
    (value := some [.int (Int.ofNat (UInt256.div (UInt256.mul x y) d).toNat)])
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat), .int (Int.ofNat d.toNat)])
  · simp only [evalExprs?, hx, hy, hd, bind, EvalResult.bind, pure]
  · rfl
  · rfl
  · exact morphoMulDivDownBodyOk x y d evm imms hfit hn

theorem morphoMulDivDownCallReverts (x y d : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey ed : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ed =
      .ok (.int (Int.ofNat d.toNat)))
    (hbad : UInt256.size ≤ x.toNat * y.toNat ∨ d = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_mulDivDown" [ex, ey, ed] retVar) .reverted := by
  apply internalCallFunctionRevert (callee := mulDivDownFunction)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat), .int (Int.ofNat d.toNat)])
  · simp only [evalExprs?, hx, hy, hd, bind, EvalResult.bind, pure]
  · rfl
  · rfl
  · exact morphoMulDivDownBodyReverts x y d evm imms hbad

end Benchmarks.Morpho.MorphoBlue
