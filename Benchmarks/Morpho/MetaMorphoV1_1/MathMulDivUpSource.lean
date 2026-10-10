import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivUp

/-! Source execution of mulDiv with upward rounding, including increment overflow. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def unsignedRoundsUpFrame (imms : Store) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "rounding" (uint256Value ⟨1⟩)
    immutables := imms }

theorem unsignedRoundsUpBody (imms : Store) (evm : State) :
    ExecFuncBody config (unsignedRoundsUpFrame imms) evm unsignedRoundsUpFunction.body
      (.returned (unsignedRoundsUpFrame imms) evm (some [.bool true])) := by
  have hg : evalExpr? config (unsignedRoundsUpFrame imms) evm
      (.binary .lt (.var "rounding") (.intLit 4)) = .ok (.bool true) := by
    simp only [evalExpr?, unsignedRoundsUpFrame, store_get_self, EvalResult.ofOption,
      uint256Value, bind, EvalResult.bind, pure, evalBinaryOp?]
    rfl
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.requireTrue hg)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, unsignedRoundsUpFrame, store_get_self,
    EvalResult.ofOption, uint256Value, bind, EvalResult.bind, pure, evalBinaryOp?, castValue?]
  rfl

theorem unsignedRoundsUpCall {locals imms : Store} {evm : State}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value ⟨1⟩]) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_unsignedRoundsUp" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret (.bool true)
          immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := unsignedRoundsUpFunction) hargs rfl rfl
    (unsignedRoundsUpBody imms evm)

def mathMulDivUpFrame (imms : Store) (a b d : UInt256) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert "rounding" (uint256Value ⟨1⟩)).insert "denominator"
      (uint256Value d)).insert "y" (uint256Value b)).insert "x" (uint256Value a)
    immutables := imms }

def mathMulDivUpResultFrame (imms : Store) (a b d : UInt256) : Frame :=
  { mathMulDivUpFrame imms a b d with
    locals := (mathMulDivUpFrame imms a b d).locals.insert "result"
      (uint256Value (fullMulDivWord a b d)) }

def mathMulDivUpTestFrame (imms : Store) (a b d : UInt256) : Frame :=
  { mathMulDivUpResultFrame imms a b d with
    locals := (mathMulDivUpResultFrame imms a b d).locals.insert "__c1" (.bool true) }

def mathMulDivUpFinalFrame (imms : Store) (a b d : UInt256) : Frame :=
  if mulDivRemainder a b d = 0 then mathMulDivUpTestFrame imms a b d else
    { mathMulDivUpTestFrame imms a b d with
      locals := (mathMulDivUpTestFrame imms a b d).locals.insert "result"
        (uint256Value (mathMulDivUpWord a b d)) }

theorem mathMulDivUpArgs (imms : Store) (a b d : UInt256) (evm : State) :
    evalExprs? config (mathMulDivUpFrame imms a b d) evm
      [.var "x", .var "y", .var "denominator"] =
      .ok [uint256Value a, uint256Value b, uint256Value d] := by
  simp only [evalExprs?, evalExpr?, mathMulDivUpFrame, store_get_self,
    store_get_ne _ _ (by decide : ("x" == "y") = false),
    store_get_ne _ _ (by decide : ("x" == "denominator") = false),
    store_get_ne _ _ (by decide : ("y" == "denominator") = false),
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem mathMulDivUpPrefix (imms : Store) (a b d : UInt256) (evm : State)
    (hfit : fullMulDivFits a b d) {outcome : ExecResult}
    (htail : ExecBlock config (mathMulDivUpTestFrame imms a b d) evm
      (mathMulDivFunction.body.drop 2) outcome) :
    ExecBlock config (mathMulDivUpFrame imms a b d) evm mathMulDivFunction.body outcome := by
  have hr : evalExprs? config (mathMulDivUpResultFrame imms a b d) evm
      [.var "rounding"] = .ok [uint256Value ⟨1⟩] := by
    simp only [evalExprs?, evalExpr?, mathMulDivUpResultFrame, mathMulDivUpFrame,
      store_get_ne _ _ (by decide : ("result" == "rounding") = false),
      store_get_ne _ _ (by decide : ("x" == "rounding") = false),
      store_get_ne _ _ (by decide : ("y" == "rounding") = false),
      store_get_ne _ _ (by decide : ("denominator" == "rounding") = false),
      store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]
  exact ExecBlock.consNormal (fullMulDivCall (mathMulDivUpArgs imms a b d evm) hfit)
    (ExecBlock.consNormal (unsignedRoundsUpCall hr (ret := "__c1")) htail)

def mathMulDivUpCondition : Expr :=
  .binary .and (.var "__c1")
    (.binary .gt (.binary .mod (.binary .mul (.var "x") (.var "y")) (.var "denominator"))
      (.intLit 0))

theorem mathMulDivUpConditionSource (imms : Store) (a b d : UInt256) (evm : State)
    (hd : d ≠ ⟨0⟩) :
    evalExpr? config (mathMulDivUpTestFrame imms a b d) evm mathMulDivUpCondition =
      .ok (.bool (decide (0 < mulDivRemainder a b d))) := by
  have hx : evalExpr? config (mathMulDivUpTestFrame imms a b d) evm (.var "x") =
      .ok (uint256Value a) := by
    simp only [evalExpr?, mathMulDivUpTestFrame, mathMulDivUpResultFrame, mathMulDivUpFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hy : evalExpr? config (mathMulDivUpTestFrame imms a b d) evm (.var "y") =
      .ok (uint256Value b) := by
    simp only [evalExpr?, mathMulDivUpTestFrame, mathMulDivUpResultFrame, mathMulDivUpFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hden : evalExpr? config (mathMulDivUpTestFrame imms a b d) evm (.var "denominator") =
      .ok (uint256Value d) := by
    simp only [evalExpr?, mathMulDivUpTestFrame, mathMulDivUpResultFrame, mathMulDivUpFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hm := naturalMulModSource hx hy hden hd
  have hc : evalExpr? config (mathMulDivUpTestFrame imms a b d) evm (.var "__c1") =
      .ok (.bool true) := by
    simp only [evalExpr?, mathMulDivUpTestFrame, store_get_self, EvalResult.ofOption]
  simp only [mathMulDivUpCondition, evalExpr?, hc, hm, bind, EvalResult.bind,
    evalBinaryOp?, Int.ofNat_eq_natCast, Int.natCast_pos, mulDivRemainder, pure]
  rfl

theorem mathMulDivUpResultValue (imms : Store) (a b d : UInt256) :
    (mathMulDivUpTestFrame imms a b d).locals.get? "result" =
      some (uint256Value (fullMulDivWord a b d)) := by
  simp only [mathMulDivUpTestFrame, mathMulDivUpResultFrame,
    store_get_ne _ _ (by decide : ("__c1" == "result") = false), store_get_self]

theorem mathMulDivUpIncrementSource (imms : Store) (a b d : UInt256) (evm : State)
    (hfit : (fullMulDivWord a b d).toNat + 1 < UInt256.size) :
    ExecBlock config (mathMulDivUpTestFrame imms a b d) evm
      [.assign .localVar ⟨"result", []⟩
        (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "result") (.intLit 1)))]
      (.ok
        { mathMulDivUpTestFrame imms a b d with
          locals := (mathMulDivUpTestFrame imms a b d).locals.insert "result"
            (uint256Value (fullMulDivWord a b d + ⟨1⟩)) } evm) := by
  refine ExecBlock.consNormal (ExecStmt.assign
    (value := uint256Value (fullMulDivWord a b d + ⟨1⟩)) ?_ ?_) ExecBlock.nil
  · apply checkedAddSourceOk (b := ⟨1⟩) _ _ hfit
    · simp only [evalExpr?, mathMulDivUpResultValue, EvalResult.ofOption]
    · simp only [evalExpr?, pure]; rfl
  · simp only [assignStorageRef?, mathMulDivUpResultValue,
      updateLocalPath?, bind, EvalResult.bind, pure]

theorem mathMulDivUpBody (imms : Store) (a b d : UInt256) (evm : State)
    (hfit : mathMulDivUpFits a b d) :
    ExecFuncBody config (mathMulDivUpFrame imms a b d) evm mathMulDivFunction.body
      (.returned (mathMulDivUpFinalFrame imms a b d) evm
        (some [uint256Value (mathMulDivUpWord a b d)])) := by
  apply ExecFuncBody.execBlockRet
  apply mathMulDivUpPrefix imms a b d evm hfit.1
  have hg := mathMulDivUpConditionSource imms a b d evm hfit.1.1
  by_cases hr : mulDivRemainder a b d = 0
  · simp only [hr, lt_self_iff_false, decide_false] at hg
    simp only [mathMulDivUpFinalFrame, mathMulDivUpWord, if_pos hr]
    apply ExecBlock.consNormal (ExecStmt.iteFalse hg ExecBlock.nil)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, mathMulDivUpResultValue,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  · have hp : 0 < mulDivRemainder a b d := Nat.pos_of_ne_zero hr
    rw [decide_eq_true hp] at hg
    simp only [mathMulDivUpFinalFrame, mathMulDivUpWord, if_neg hr]
    apply ExecBlock.consNormal
      (ExecStmt.iteTrue hg (mathMulDivUpIncrementSource imms a b d evm (hfit.2 hr)))
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem mathMulDivUpBodyReverts (imms : Store) (a b d : UInt256) (evm : State)
    (hbad : ¬ mathMulDivUpFits a b d) :
    ExecFuncBody config (mathMulDivUpFrame imms a b d) evm mathMulDivFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hf : fullMulDivFits a b d
  · apply mathMulDivUpPrefix imms a b d evm hf
    have hr : mulDivRemainder a b d ≠ 0 := by
      intro hz
      exact hbad ⟨hf, fun hn ↦ False.elim (hn hz)⟩
    have hi : UInt256.size ≤ (fullMulDivWord a b d).toNat + 1 :=
      Nat.le_of_not_gt (fun hi ↦ hbad ⟨hf, fun _ ↦ hi⟩)
    have hg := mathMulDivUpConditionSource imms a b d evm hf.1
    rw [decide_eq_true (Nat.pos_of_ne_zero hr)] at hg
    apply ExecBlock.consRevert (ExecStmt.iteTrue hg _)
    apply ExecBlock.consRevert
    apply ExecStmt.assignExprRevert (checkedAddSourceOverflow (b := ⟨1⟩) ?_ ?_ hi)
    · simp only [evalExpr?, mathMulDivUpResultValue, EvalResult.ofOption]
    · simp only [evalExpr?, pure]; rfl
  · exact ExecBlock.consRevert (fullMulDivCallReverts (mathMulDivUpArgs imms a b d evm) hf)

theorem mathMulDivUpCall {locals imms : Store} {evm : State} {a b d : UInt256}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value a, uint256Value b, uint256Value d, uint256Value ⟨1⟩])
    (hfit : mathMulDivUpFits a b d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_mulDiv" args ret)
      (.ok
        { contract := contract
          locals := locals.insert ret (uint256Value (mathMulDivUpWord a b d))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := mathMulDivFunction) hargs rfl rfl
    (mathMulDivUpBody imms a b d evm hfit)

theorem mathMulDivUpCallReverts {locals imms : Store} {evm : State} {a b d : UInt256}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [uint256Value a, uint256Value b, uint256Value d, uint256Value ⟨1⟩])
    (hbad : ¬ mathMulDivUpFits a b d) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "Math_mulDiv" args ret) .reverted := by
  exact internalCallFunctionRevert (callee := mathMulDivFunction) hargs rfl rfl
    (mathMulDivUpBodyReverts imms a b d evm hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
