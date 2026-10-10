import Benchmarks.Morpho.MetaMorphoV1_1.TaylorWords

/-! Source execution of the checked three-term Taylor calculation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def taylorFunction : FunctionDecl := contract.functions[79]!

def taylorFrame (imms : Store) (x n : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "n" (uint256Value n)).insert "x" (uint256Value x)
    immutables := imms }

def taylorFirstFrame (imms : Store) (x n : UInt256) : Frame :=
  { taylorFrame imms x n with
    locals := (taylorFrame imms x n).locals.insert "firstTerm" (uint256Value (UInt256.mul x n)) }

def taylorSecondFrame (imms : Store) (x n : UInt256) : Frame :=
  { taylorFirstFrame imms x n with
    locals := (taylorFirstFrame imms x n).locals.insert "secondTerm"
      (uint256Value (taylorSecond (UInt256.mul x n))) }

def taylorThirdFrame (imms : Store) (x n : UInt256) : Frame :=
  { taylorSecondFrame imms x n with
    locals := (taylorSecondFrame imms x n).locals.insert "thirdTerm"
      (uint256Value (taylorThird (UInt256.mul x n))) }

theorem taylorFrame_x (imms : Store) (x n : UInt256) (evm : State) :
    evalExpr? config (taylorFrame imms x n) evm (.var "x") = .ok (uint256Value x) := by
  simp only [evalExpr?, taylorFrame, store_get_self, EvalResult.ofOption]

theorem taylorFrame_n (imms : Store) (x n : UInt256) (evm : State) :
    evalExpr? config (taylorFrame imms x n) evm (.var "n") = .ok (uint256Value n) := by
  simp only [evalExpr?, taylorFrame, store_get_ne _ _ (by decide : ("x" == "n") = false),
    store_get_self, EvalResult.ofOption]

theorem taylorFirstFrame_first (imms : Store) (x n : UInt256) (evm : State) :
    evalExpr? config (taylorFirstFrame imms x n) evm (.var "firstTerm") =
      .ok (uint256Value (UInt256.mul x n)) := by
  simp only [evalExpr?, taylorFirstFrame, store_get_self, EvalResult.ofOption]

theorem taylorSecondFrame_values (imms : Store) (x n : UInt256) (evm : State) :
    evalExpr? config (taylorSecondFrame imms x n) evm (.var "firstTerm") =
      .ok (uint256Value (UInt256.mul x n)) ∧
    evalExpr? config (taylorSecondFrame imms x n) evm (.var "secondTerm") =
      .ok (uint256Value (taylorSecond (UInt256.mul x n))) := by
  simp only [evalExpr?, taylorSecondFrame, taylorFirstFrame,
    store_get_ne _ _ (by decide : ("secondTerm" == "firstTerm") = false),
    store_get_self, EvalResult.ofOption, and_self]

theorem taylorThirdFrame_values (imms : Store) (x n : UInt256) (evm : State) :
    evalExpr? config (taylorThirdFrame imms x n) evm (.var "firstTerm") =
      .ok (uint256Value (UInt256.mul x n)) ∧
    evalExpr? config (taylorThirdFrame imms x n) evm (.var "secondTerm") =
      .ok (uint256Value (taylorSecond (UInt256.mul x n))) ∧
    evalExpr? config (taylorThirdFrame imms x n) evm (.var "thirdTerm") =
      .ok (uint256Value (taylorThird (UInt256.mul x n))) := by
  simp only [evalExpr?, taylorThirdFrame, taylorSecondFrame, taylorFirstFrame,
    store_get_ne _ _ (by decide : ("thirdTerm" == "firstTerm") = false),
    store_get_ne _ _ (by decide : ("thirdTerm" == "secondTerm") = false),
    store_get_ne _ _ (by decide : ("secondTerm" == "firstTerm") = false),
    store_get_self, EvalResult.ofOption, and_self]

theorem taylorDenominatorTwo (frame : Frame) (evm : State) :
    evalExpr? config frame evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.intLit 2) (.intLit (10 ^ 18)))) =
      .ok (uint256Value (UInt256.ofNat (2 * 10 ^ 18))) :=
  checkedMulSourceOk (a := ⟨2⟩) (b := UInt256.ofNat (10 ^ 18))
    (by simp only [evalExpr?, pure]; rfl) (by simp only [evalExpr?, pure]; rfl)
    (by decide +kernel)

theorem taylorDenominatorThree (frame : Frame) (evm : State) :
    evalExpr? config frame evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.intLit 3) (.intLit (10 ^ 18)))) =
      .ok (uint256Value (UInt256.ofNat (3 * 10 ^ 18))) :=
  checkedMulSourceOk (a := ⟨3⟩) (b := UInt256.ofNat (10 ^ 18))
    (by simp only [evalExpr?, pure]; rfl) (by simp only [evalExpr?, pure]; rfl)
    (by decide +kernel)

theorem taylorFirstPrefix (imms : Store) (x n : UInt256) (evm : State)
    (hfit : x.toNat * n.toNat < UInt256.size) :
    ABlock config evm (taylorFrame imms x n) taylorFunction.body
      (taylorFirstFrame imms x n) (taylorFunction.body.drop 1) :=
  ABlock.start.letStep (checkedMulSourceOk (taylorFrame_x imms x n evm)
    (taylorFrame_n imms x n evm) hfit)

theorem taylorSecondPrefix (imms : Store) (x n : UInt256) (evm : State)
    (hfit : (UInt256.mul x n).toNat * (UInt256.mul x n).toNat < UInt256.size) :
    ABlock config evm (taylorFirstFrame imms x n) (taylorFunction.body.drop 1)
      (taylorSecondFrame imms x n) (taylorFunction.body.drop 2) := by
  constructor
  intro result htail
  exact ExecBlock.consNormal (mulDivDownCall evm _ imms (UInt256.mul x n) (UInt256.mul x n)
    (UInt256.ofNat (2 * 10 ^ 18)) "secondTerm" _ _ _ hfit (by decide)
    (taylorFirstFrame_first imms x n evm) (taylorFirstFrame_first imms x n evm)
    (taylorDenominatorTwo _ evm)) htail

theorem taylorThirdPrefix (imms : Store) (x n : UInt256) (evm : State)
    (hfit : (taylorSecond (UInt256.mul x n)).toNat * (UInt256.mul x n).toNat < UInt256.size) :
    ABlock config evm (taylorSecondFrame imms x n) (taylorFunction.body.drop 2)
      (taylorThirdFrame imms x n) (taylorFunction.body.drop 3) := by
  constructor
  intro result htail
  exact ExecBlock.consNormal (mulDivDownCall evm _ imms (taylorSecond (UInt256.mul x n))
    (UInt256.mul x n) (UInt256.ofNat (3 * 10 ^ 18)) "thirdTerm" _ _ _ hfit (by decide)
    (taylorSecondFrame_values imms x n evm).2 (taylorSecondFrame_values imms x n evm).1
    (taylorDenominatorThree _ evm)) htail

theorem taylorBody (imms : Store) (x n : UInt256) (evm : State) (hfit : taylorFits x n) :
    ExecFuncBody config (taylorFrame imms x n) evm taylorFunction.body
      (.returned (taylorThirdFrame imms x n) evm
        [uint256Value (taylorSum (UInt256.mul x n))]) := by
  apply ExecFuncBody.execBlockRet
  apply (taylorFirstPrefix imms x n evm hfit.1).run
  apply (taylorSecondPrefix imms x n evm hfit.2.1).run
  apply (taylorThirdPrefix imms x n evm hfit.2.2).run
  have hv := taylorThirdFrame_values imms x n evm
  have hsum := taylorSumsFit (UInt256.mul x n) hfit.2.1
  exact ABlock.start.returns
    (checkedAddSourceOk (checkedAddSourceOk hv.1 hv.2.1 hsum.1) hv.2.2 hsum.2)

theorem taylorBodyReverts (imms : Store) (x n : UInt256) (evm : State)
    (hbad : ¬ taylorFits x n) :
    ExecFuncBody config (taylorFrame imms x n) evm taylorFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hp : x.toNat * n.toNat < UInt256.size
  · apply (taylorFirstPrefix imms x n evm hp).run
    by_cases hsq : (UInt256.mul x n).toNat * (UInt256.mul x n).toNat < UInt256.size
    · apply (taylorSecondPrefix imms x n evm hsq).run
      exact ExecBlock.consRevert (mulDivDownCallReverts evm _ imms
        (taylorSecond (UInt256.mul x n)) (UInt256.mul x n) (UInt256.ofNat (3 * 10 ^ 18))
        "thirdTerm" _ _ _ (fun h ↦ hbad ⟨hp, hsq, h.1⟩)
        (taylorSecondFrame_values imms x n evm).2 (taylorSecondFrame_values imms x n evm).1
        (taylorDenominatorThree _ evm))
    · exact ExecBlock.consRevert (mulDivDownCallReverts evm _ imms
        (UInt256.mul x n) (UInt256.mul x n) (UInt256.ofNat (2 * 10 ^ 18))
        "secondTerm" _ _ _ (fun h ↦ hsq h.1)
        (taylorFirstFrame_first imms x n evm) (taylorFirstFrame_first imms x n evm)
        (taylorDenominatorTwo _ evm))
  · exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (checkedMulSourceOverflow (taylorFrame_x imms x n evm) (taylorFrame_n imms x n evm)
        (Nat.le_of_not_lt hp)))

set_option maxRecDepth 2000 in
theorem taylorCall (evm : State) (locals imms : Store) (x n : UInt256)
    (retVar : Ident) (lhs rhs : Expr) (hfit : taylorFits x n)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (uint256Value x))
    (hn : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (uint256Value n)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wTaylorCompounded" [lhs, rhs] retVar)
      (.ok { contract := contract,
             locals := locals.insert retVar (uint256Value (taylorSum (UInt256.mul x n))),
             immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := taylorFunction)
    (caller := { contract := contract, locals := locals, immutables := imms })
    (value := some [uint256Value (taylorSum (UInt256.mul x n))])
    (argVals := [uint256Value x, uint256Value n])
    (by simp only [evalExprs?, hx, hn, bind, EvalResult.bind, pure]) rfl rfl
    (taylorBody imms x n evm hfit)

set_option maxRecDepth 2000 in
theorem taylorCallReverts (evm : State) (locals imms : Store) (x n : UInt256)
    (retVar : Ident) (lhs rhs : Expr) (hbad : ¬ taylorFits x n)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (uint256Value x))
    (hn : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (uint256Value n)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_wTaylorCompounded" [lhs, rhs] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := taylorFunction)
    (argVals := [uint256Value x, uint256Value n])
    (by simp only [evalExprs?, hx, hn, bind, EvalResult.bind, pure]) rfl rfl
    (taylorBodyReverts imms x n evm hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
