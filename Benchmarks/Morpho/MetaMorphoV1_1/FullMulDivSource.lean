import Benchmarks.Morpho.MetaMorphoV1_1.FullMulProduct
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Source execution of unbounded multiplication followed by checked full-precision division. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def fullMulDivFunction : FunctionDecl := contract.functions[66]!

def fullMulDivFrame (imms : Store) (a b d : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert "denominator" (uint256Value d)).insert "y"
      (uint256Value b)).insert "x" (uint256Value a)
    immutables := imms }

theorem fullMulDivFrame_x (imms : Store) (a b d : UInt256) (evm : State) :
    evalExpr? config (fullMulDivFrame imms a b d) evm (.var "x") = .ok (uint256Value a) := by
  simp only [evalExpr?, fullMulDivFrame, store_get_self, EvalResult.ofOption]

theorem fullMulDivFrame_y (imms : Store) (a b d : UInt256) (evm : State) :
    evalExpr? config (fullMulDivFrame imms a b d) evm (.var "y") = .ok (uint256Value b) := by
  simp only [evalExpr?, fullMulDivFrame,
    store_get_ne _ _ (by decide : ("x" == "y") = false), store_get_self, EvalResult.ofOption]

theorem fullMulDivFrame_den (imms : Store) (a b d : UInt256) (evm : State) :
    evalExpr? config (fullMulDivFrame imms a b d) evm (.var "denominator") =
      .ok (uint256Value d) := by
  simp only [evalExpr?, fullMulDivFrame,
    store_get_ne _ _ (by decide : ("x" == "denominator") = false),
    store_get_ne _ _ (by decide : ("y" == "denominator") = false),
    store_get_self, EvalResult.ofOption]

theorem naturalMulDivSource {cfg : Config} {frame : Frame} {evm : State}
    {x y den : Expr} {a b d : UInt256}
    (ha : evalExpr? cfg frame evm x = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm y = .ok (uint256Value b))
    (hd : evalExpr? cfg frame evm den = .ok (uint256Value d)) (hn : d ≠ ⟨0⟩) :
    evalExpr? cfg frame evm (.binary .div (.binary .mul x y) den) =
      .ok (.int (Int.ofNat (a.toNat * b.toNat / d.toNat))) := by
  have hz : (d.toNat : Int) ≠ 0 := by
    intro h
    exact hn (uint256_toNat_eq_zero (by omega))
  simp only [evalExpr?, ha, hb, hd, uint256Value, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, ← Int.natCast_mul, hz, if_false, Int.natCast_ediv]

theorem fullMulDivBody (imms : Store) (a b d : UInt256) (evm : State)
    (hfit : fullMulDivFits a b d) :
    ExecFuncBody config (fullMulDivFrame imms a b d) evm fullMulDivFunction.body
      (.returned (fullMulDivFrame imms a b d) evm
        (some [uint256Value (fullMulDivWord a b d)])) := by
  have hz : evalExpr? config (fullMulDivFrame imms a b d) evm (.intLit 0) =
      .ok (uint256Value ⟨0⟩) := by simp only [evalExpr?, pure]; rfl
  have hg := SourceMemory.wordNeSource (fullMulDivFrame_den imms a b d evm) hz
  simp only [ne_eq, hfit.1, not_false_eq_true, decide_true] at hg
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.requireTrue hg)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have hv := evalExpr_uintInRange ⟨256, by decide⟩
    (naturalMulDivSource (fullMulDivFrame_x imms a b d evm)
      (fullMulDivFrame_y imms a b d evm) (fullMulDivFrame_den imms a b d evm) hfit.1) hfit.2
  simp only [evalExprs?, hv, bind, EvalResult.bind, pure]
  rw [uint256Value, fullMulDivWord, UInt256.toNat_ofNat_of_lt hfit.2]

theorem fullMulDivBodyReverts (imms : Store) (a b d : UInt256) (evm : State)
    (hbad : ¬ fullMulDivFits a b d) :
    ExecFuncBody config (fullMulDivFrame imms a b d) evm fullMulDivFunction.body .reverted := by
  have hz : evalExpr? config (fullMulDivFrame imms a b d) evm (.intLit 0) =
      .ok (uint256Value ⟨0⟩) := by simp only [evalExpr?, pure]; rfl
  have hg := SourceMemory.wordNeSource (fullMulDivFrame_den imms a b d evm) hz
  apply ExecFuncBody.execBlockRevert
  by_cases hd : d = ⟨0⟩
  · subst d
    simp only [ne_eq, not_true_eq_false, decide_false] at hg
    exact ExecBlock.consRevert (ExecStmt.requireFalse hg)
  · simp only [ne_eq, hd, not_false_eq_true, decide_true] at hg
    apply ExecBlock.consNormal (ExecStmt.requireTrue hg)
    apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
    have hv := evalExpr_uintInRange_revert ⟨256, by decide⟩
      (naturalMulDivSource (fullMulDivFrame_x imms a b d evm)
        (fullMulDivFrame_y imms a b d evm) (fullMulDivFrame_den imms a b d evm) hd)
      (Nat.le_of_not_gt (fun h ↦ hbad ⟨hd, h⟩))
    simp only [evalExprs?, hv, bind, EvalResult.bind]

theorem fullMulDivCall {locals imms : Store} {evm : State} {a b d : UInt256}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value a, uint256Value b, uint256Value d])
    (hfit : fullMulDivFits a b d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_mulDiv_uint256_uint256_uint256" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret (uint256Value (fullMulDivWord a b d))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := fullMulDivFunction) hargs rfl rfl
    (fullMulDivBody imms a b d evm hfit)

theorem fullMulDivCallReverts {locals imms : Store} {evm : State} {a b d : UInt256}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value a, uint256Value b, uint256Value d])
    (hbad : ¬ fullMulDivFits a b d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_mulDiv_uint256_uint256_uint256" args ret) .reverted := by
  exact internalCallFunctionRevert (callee := fullMulDivFunction) hargs rfl rfl
    (fullMulDivBodyReverts imms a b d evm hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
