import Benchmarks.Morpho.MorphoBlue.AccrueSourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev mulDivUpFunction : FunctionDecl := contract.functions[14]!

def MulDivUpFits (x y d : UInt256) : Prop :=
  x.toNat * y.toNat < UInt256.size ∧ 1 ≤ d.toNat ∧
    (UInt256.mul x y).toNat + (UInt256.sub d (UInt256.ofNat 1)).toNat < UInt256.size

def mulDivUpWord (x y d : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul x y + UInt256.sub d (UInt256.ofNat 1)) d

def mulDivUpExpr (x y d : Expr) : Expr :=
  .binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .add
    (.inRange (.uint ⟨256, by decide⟩) (.binary .mul x y))
    (.inRange (.uint ⟨256, by decide⟩) (.binary .sub d (.intLit 1))))) d

theorem evalMulDivUpOk {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey ed : Expr}
    {x y d : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? cfg frame evm ed = .ok (.int (Int.ofNat d.toNat))) (hf : MulDivUpFits x y d) :
    evalExpr? cfg frame evm (mulDivUpExpr ex ey ed) = .ok (.int (Int.ofNat (mulDivUpWord x y d).toNat)) := by
  have h1 : evalExpr? cfg frame evm (.intLit 1) = .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  exact divSourceOk (checkedAddSourceOk (checkedMulSourceOk hx hy hf.1)
    (evalExpr_uint256_sub hd h1 hf.2.1) hf.2.2) hd
    (fun hz ↦ by have hn := hf.2.1; rw [hz] at hn; contradiction)

theorem evalMulDivUpReverts {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey ed : Expr}
    {x y d : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? cfg frame evm ed = .ok (.int (Int.ofNat d.toNat))) (hf : ¬ MulDivUpFits x y d) :
    evalExpr? cfg frame evm (mulDivUpExpr ex ey ed) = .revert := by
  have h1 : evalExpr? cfg frame evm (.intLit 1) = .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  by_cases hp : x.toNat * y.toNat < UInt256.size
  swap
  · have hr := checkedMulSourceOverflow hx hy (Nat.le_of_not_gt hp)
    simp only [mulDivUpExpr, evalExpr?, hr, bind, EvalResult.bind]
  have hm := checkedMulSourceOk hx hy hp
  by_cases hn : 1 ≤ d.toNat
  swap
  · have hr := evalCheckedSubUnderflow hd h1 (Nat.lt_of_not_ge hn)
    simp only [mulDivUpExpr, evalExpr?, hm, hr, bind, EvalResult.bind]
  have hs := evalExpr_uint256_sub hd h1 hn
  have hr := checkedAddSourceOverflow hm hs (Nat.le_of_not_gt (fun h ↦ hf ⟨hp, hn, h⟩))
  simp only [mulDivUpExpr, evalExpr?, hr, bind, EvalResult.bind]

theorem morphoMulDivUpBodyOk (x y d : UInt256) (evm : EVM.State) (imms : Store) (hf : MulDivUpFits x y d) :
    ExecFuncBody config (mulDivFrame x y d imms) evm mulDivUpFunction.body
      (.returned (mulDivFrame x y d imms) evm (some [.int (Int.ofNat (mulDivUpWord x y d).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  exact evalExprs?_singleton (evalMulDivUpOk (mulDiv_eval_x x y d imms evm)
    (mulDiv_eval_y x y d imms evm) (mulDiv_eval_d x y d imms evm) hf)

theorem morphoMulDivUpBodyReverts (x y d : UInt256) (evm : EVM.State) (imms : Store)
    (hf : ¬ MulDivUpFits x y d) :
    ExecFuncBody config (mulDivFrame x y d imms) evm mulDivUpFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  have hr := evalMulDivUpReverts (mulDiv_eval_x x y d imms evm)
    (mulDiv_eval_y x y d imms evm) (mulDiv_eval_d x y d imms evm) hf
  change evalExprs? _ _ _ [mulDivUpExpr (.var "x") (.var "y") (.var "d")] = _
  simp only [evalExprs?, hr, bind, EvalResult.bind]

theorem morphoMulDivUpCallOk (x y d : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey ed : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ed =
      .ok (.int (Int.ofNat d.toNat))) (hf : MulDivUpFits x y d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_mulDivUp" [ex, ey, ed] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (mulDivUpWord x y d).toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := mulDivUpFunction)
    (value := some [.int (Int.ofNat (mulDivUpWord x y d).toNat)])
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat), .int (Int.ofNat d.toNat)])
    (by simp only [evalExprs?, hx, hy, hd, bind, EvalResult.bind, pure]) rfl rfl
    (morphoMulDivUpBodyOk x y d evm imms hf)

theorem morphoMulDivUpCallReverts (x y d : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex ey ed : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ey =
      .ok (.int (Int.ofNat y.toNat)))
    (hd : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ed =
      .ok (.int (Int.ofNat d.toNat))) (hf : ¬ MulDivUpFits x y d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_mulDivUp" [ex, ey, ed] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := mulDivUpFunction)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat), .int (Int.ofNat d.toNat)])
    (by simp only [evalExprs?, hx, hy, hd, bind, EvalResult.bind, pure]) rfl rfl
    (morphoMulDivUpBodyReverts x y d evm imms hf)

end Benchmarks.Morpho.MorphoBlue
