import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.FeeMutation
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Source guards, interest accrual, and the packed fee assignment. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def setFeeLocals (value : UInt256) : Store :=
  (∅ : Store).insert "newFee" (uint256Value value)

abbrev setFeeFrame (evm : State) (imms : Store) (value : UInt256) : Frame :=
  adminFrame evm (setFeeLocals value) imms

def setFeeResumeFrame (evm : State) (imms : Store) (value ptr : UInt256) : Frame :=
  { setFeeFrame evm imms value with
    locals := (setFeeFrame evm imms value).locals.insert "__c1" (uint256Value ptr) }

def setFeeFinalFrame (evm evm' : State) (imms : Store) (value ptr : UInt256) : Frame :=
  { setFeeResumeFrame evm imms value ptr with
    locals := (setFeeResumeFrame evm imms value ptr).locals.insert "__c2"
      (.address evm'.executionEnv.source) }

def setFeeOld (evm : State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨18⟩)
    (UInt256.ofNat (2 ^ 96 - 1))

def setFeeDifferent : Expr := .binary .ne (.var "newFee") (.storage ⟨"fee", []⟩)

def setFeeBound : Expr := .binary .le (.var "newFee") (.intLit 500000000000000000)

def setFeeValid : Expr :=
  .unary .not (.binary .and (.binary .ne (.var "newFee") (.intLit 0))
    (.binary .eq (.storage ⟨"feeRecipient", []⟩) (.cast (.intLit 0) (.elem .address))))

def setFeeTail : List Stmt :=
  [.internalCall allocatedAccrueInterestFunction.name [.intLit 128] "__c1",
    .assign .storage ⟨"fee", []⟩ (.cast (.var "newFee") (.elem (.int (.uint ⟨96, by decide⟩)))),
    .internalCall "_msgSender" [] "__c2", .emit "SetFee" [.var "__c2", .storage ⟨"fee", []⟩]]

def setFeeAdminTail : List Stmt :=
  [.require setFeeDifferent, .require setFeeBound, .require setFeeValid] ++ setFeeTail

def setFeeAllowed (evm : State) (value : UInt256) : Prop :=
  value ≠ setFeeOld evm ∧ value.toNat ≤ 500000000000000000 ∧
    ¬ (value ≠ ⟨0⟩ ∧ accrueFeeRecipient evm = AccountAddress.ofNat 0)

theorem setFeeValue (evm : State) (imms : Store) (value : UInt256) :
    evalExpr? config (setFeeFrame evm imms value) evm (.var "newFee") =
      .ok (uint256Value value) := by
  simp [evalExpr?, setFeeFrame, adminFrame, setFeeLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem setFeeDifferentSource (evm : State) (imms : Store) (value : UInt256) :
    evalExpr? config (setFeeFrame evm imms value) evm setFeeDifferent =
      .ok (.bool (decide (value ≠ setFeeOld evm))) := by
  exact wordNeSource (setFeeValue evm imms value)
    (evalStorage_fee evm _ imms (by simp [setFeeLocals]))

theorem setFeeBoundSource (evm : State) (imms : Store) (value : UInt256) :
    evalExpr? config (setFeeFrame evm imms value) evm setFeeBound =
      .ok (.bool (decide (value.toNat ≤ 500000000000000000))) := by
  exact naturalLeSource (setFeeValue evm imms value) (by simp only [evalExpr?, pure]; rfl)

theorem setFeeValidSource (evm : State) (imms : Store) (value : UInt256) :
    evalExpr? config (setFeeFrame evm imms value) evm setFeeValid =
      .ok (.bool (decide
        (¬ (value ≠ ⟨0⟩ ∧ accrueFeeRecipient evm = AccountAddress.ofNat 0)))) := by
  have ha := evalExpr_addressEq
    (evalStorage_feeRecipient evm (setFeeFrame evm imms value).locals imms
      (by simp [setFeeFrame, adminFrame, setFeeLocals]))
    (show evalExpr? config (setFeeFrame evm imms value) evm
      (.cast (.intLit 0) (.elem .address)) = .ok (.address (AccountAddress.ofNat 0)) from
      evalAddressLiteral _ _ _ (AccountAddress.ofNat 0))
  have hz : evalExpr? config (setFeeFrame evm imms value) evm (.intLit 0) =
      .ok (uint256Value ⟨0⟩) := by simp only [evalExpr?, pure]; rfl
  have hc := boolAndSource (wordNeSource (setFeeValue evm imms value) hz) ha
  simp only [setFeeValid, evalExpr?, hc, bind, EvalResult.bind, evalUnaryOp?,
    EvalResult.ofOption, decide_not, Bool.decide_and]
  rfl

theorem setFeePrefix (evm : State) (imms : Store) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hgood : setFeeAllowed evm value) :
    ABlock config evm ⟨contract, setFeeLocals value, imms⟩ setFeeTransition.body
      (setFeeFrame evm imms value) setFeeTail := by
  have hpre := adminPrefix evm (setFeeLocals value) imms setFeeAdminTail hwv hhi howner
  apply ABlock.requireStep (ABlock.requireStep (ABlock.requireStep hpre ?_) ?_) ?_
  · rw [setFeeDifferentSource evm imms value, decide_eq_true hgood.1]
  · rw [setFeeBoundSource evm imms value, decide_eq_true hgood.2.1]
  · rw [setFeeValidSource evm imms value, decide_eq_true hgood.2.2]

theorem setFeeRevertsGuard (evm : State) (imms : Store) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbad : ¬ setFeeAllowed evm value) :
    ExecTransitionBody config contract evm (setFeeLocals value)
      setFeeTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hpre := adminPrefix evm (setFeeLocals value) imms setFeeAdminTail hwv hhi howner
  by_cases hd : value = setFeeOld evm
  · exact hpre.requireRevert (by rw [setFeeDifferentSource evm imms value]; simp [hd])
  · have hdiff := hpre.requireStep
      (by rw [setFeeDifferentSource evm imms value, decide_eq_true hd])
    by_cases hb : value.toNat ≤ 500000000000000000
    · have hbound := hdiff.requireStep
        (by rw [setFeeBoundSource evm imms value, decide_eq_true hb])
      exact hbound.requireRevert (by
        rw [setFeeValidSource evm imms value, decide_eq_false (fun hv ↦ hbad ⟨hd, hb, hv⟩)])
    · exact hdiff.requireRevert
        (by rw [setFeeBoundSource evm imms value, decide_eq_false hb])

theorem setFeeAccrualReverts (evm : State) (imms : Store) (value : UInt256)
    (hpre : ABlock config evm ⟨contract, setFeeLocals value, imms⟩
      setFeeTransition.body (setFeeFrame evm imms value) setFeeTail)
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .reverted) :
    ExecTransitionBody config contract evm (setFeeLocals value)
      setFeeTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply hpre.run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedAccrueInterestFunction)
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]; rfl) rfl rfl hbody)

theorem setFeeAccrualStatic (evm : State) (imms : Store) (value : UInt256)
    (hpre : ABlock config evm ⟨contract, setFeeLocals value, imms⟩
      setFeeTransition.body (setFeeFrame evm imms value) setFeeTail)
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .staticViolation) :
    ExecTransitionBody config contract evm (setFeeLocals value)
      setFeeTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply hpre.run
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (callee := allocatedAccrueInterestFunction.toCallable)
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]; rfl) rfl rfl hbody)

theorem setFeeBodyReturns (evm evm' : State) (imms : Store) (value : UInt256)
    (final : Frame) (ptr : UInt256) (hfit : value.toNat < 2 ^ 96)
    (hpre : ABlock config evm ⟨contract, setFeeLocals value, imms⟩
      setFeeTransition.body (setFeeFrame evm imms value) setFeeTail)
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body (.returned final evm' [uint256Value ptr])) :
    ExecTransitionBody config contract evm (setFeeLocals value) setFeeTransition.body
      (.returned (setFeeFinalFrame evm evm' imms value ptr) (setFeeState evm' value) none)
      imms := by
  apply ExecFuncBody.execBlockOK
  apply hpre.run
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedAccrueInterestFunction)
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]; rfl) rfl rfl hbody)
  have hv : evalExpr? config (setFeeResumeFrame evm imms value ptr) evm' (.var "newFee") =
      .ok (uint256Value value) := by
    simp [evalExpr?, setFeeResumeFrame, setFeeFrame, adminFrame,
      setFeeLocals, Std.HashMap.getElem_insert, EvalResult.ofOption]
  apply ExecBlock.consNormal (ExecStmt.assign (uintCastSource _ hv hfit)
    (assignStorage_fee evm' _ imms value (by
      simp [setFeeFrame, adminFrame, setFeeLocals])))
  apply ExecBlock.consNormal (msgSenderCall _ imms (setFeeState evm' value) "__c2")
  rw [show (setFeeState evm' value).executionEnv = evm'.executionEnv from
    storageStore_executionEnv _ _ _ _]
  change ExecBlock config (setFeeFinalFrame evm evm' imms value ptr) (setFeeState evm' value)
    [.emit "SetFee" [.var "__c2", .storage ⟨"fee", []⟩]]
    (.ok (setFeeFinalFrame evm evm' imms value ptr) (setFeeState evm' value))
  have hf : evalExpr? config (setFeeFinalFrame evm evm' imms value ptr)
      (setFeeState evm' value) (.storage ⟨"fee", []⟩) =
      .ok (uint256Value (setFeeOld (setFeeState evm' value))) :=
    evalStorage_fee (setFeeState evm' value) _ imms (by
      simp [setFeeResumeFrame, setFeeFrame, adminFrame, setFeeLocals])
  have hc : evalExpr? config (setFeeFinalFrame evm evm' imms value ptr)
      (setFeeState evm' value) (.var "__c2") = .ok (.address evm'.executionEnv.source) := by
    simp [evalExpr?, setFeeFinalFrame, EvalResult.ofOption]
  have he : evalExprs? config (setFeeFinalFrame evm evm' imms value ptr) (setFeeState evm' value)
      [.var "__c2", .storage ⟨"fee", []⟩] =
      .ok [.address evm'.executionEnv.source,
        uint256Value (setFeeOld (setFeeState evm' value))] := by
    simp only [evalExprs?, hc, hf, bind, EvalResult.bind, pure]
  exact ExecBlock.consNormal (ExecStmt.emit he) ExecBlock.nil

end Benchmarks.Morpho.MetaMorphoV1_1
