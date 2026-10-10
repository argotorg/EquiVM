import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.FeeRecipientMutation
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! Source guards, interest accrual, and the packed fee-recipient assignment. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def setFeeRecipientLocals (recipient : AccountAddress) : Store :=
  (∅ : Store).insert "newFeeRecipient" (.address recipient)

abbrev setFeeRecipientFrame (evm : State) (imms : Store) (recipient : AccountAddress) : Frame :=
  adminFrame evm (setFeeRecipientLocals recipient) imms

def setFeeRecipientResumeFrame (evm : State) (imms : Store) (recipient : AccountAddress)
    (ptr : UInt256) : Frame :=
  { setFeeRecipientFrame evm imms recipient with
    locals := (setFeeRecipientFrame evm imms recipient).locals.insert "__c1" (uint256Value ptr) }

def feeRecipientFee (evm : State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨18⟩)
    (UInt256.ofNat (2 ^ 96 - 1))

def setFeeRecipientDifferent : Expr :=
  .binary .ne (.var "newFeeRecipient") (.storage ⟨"feeRecipient", []⟩)

def setFeeRecipientValid : Expr :=
  .unary .not (.binary .and
    (.binary .eq (.var "newFeeRecipient") (.cast (.intLit 0) (.elem .address)))
    (.binary .ne (.storage ⟨"fee", []⟩) (.intLit 0)))

def setFeeRecipientTail : List Stmt :=
  [.internalCall allocatedAccrueInterestFunction.name [.intLit 128] "__c1",
    .assign .storage ⟨"feeRecipient", []⟩ (.var "newFeeRecipient"),
    .emit "SetFeeRecipient" [.var "newFeeRecipient"]]

def setFeeRecipientAdminTail : List Stmt :=
  [.require setFeeRecipientDifferent, .require setFeeRecipientValid] ++ setFeeRecipientTail

theorem setFeeRecipientValue (evm : State) (imms : Store) (recipient : AccountAddress) :
    evalExpr? config (setFeeRecipientFrame evm imms recipient) evm (.var "newFeeRecipient") =
      .ok (.address recipient) := by
  simp [evalExpr?, setFeeRecipientFrame, adminFrame, setFeeRecipientLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem setFeeRecipientDifferentSource (evm : State) (imms : Store)
    (recipient : AccountAddress) :
    evalExpr? config (setFeeRecipientFrame evm imms recipient) evm setFeeRecipientDifferent =
      .ok (.bool (decide (recipient ≠ accrueFeeRecipient evm))) := by
  exact evalExpr_addressNe (setFeeRecipientValue evm imms recipient)
    (evalStorage_feeRecipient evm _ imms
      (by simp [setFeeRecipientFrame, adminFrame, setFeeRecipientLocals]))

theorem setFeeRecipientValidSource (evm : State) (imms : Store) (recipient : AccountAddress) :
    evalExpr? config (setFeeRecipientFrame evm imms recipient) evm setFeeRecipientValid =
      .ok (.bool (decide
        (¬ (recipient = AccountAddress.ofNat 0 ∧ feeRecipientFee evm ≠ ⟨0⟩)))) := by
  have ha := evalExpr_addressEq (setFeeRecipientValue evm imms recipient)
    (show evalExpr? config (setFeeRecipientFrame evm imms recipient) evm
      (.cast (.intLit 0) (.elem .address)) = .ok (.address (AccountAddress.ofNat 0)) from
      evalAddressLiteral _ _ _ (AccountAddress.ofNat 0))
  have hf : evalExpr? config (setFeeRecipientFrame evm imms recipient) evm
      (.storage ⟨"fee", []⟩) = .ok (uint256Value (feeRecipientFee evm)) :=
    evalStorage_fee evm _ imms (by simp [setFeeRecipientFrame, adminFrame, setFeeRecipientLocals])
  have hz : evalExpr? config (setFeeRecipientFrame evm imms recipient) evm (.intLit 0) =
      .ok (uint256Value ⟨0⟩) := by simp only [evalExpr?, pure]; rfl
  have hc := boolAndSource ha (wordNeSource hf hz)
  simp only [setFeeRecipientValid, evalExpr?, hc, bind, EvalResult.bind, evalUnaryOp?,
    EvalResult.ofOption, decide_not, Bool.decide_and]

theorem setFeeRecipientPrefix (evm : State) (imms : Store) (recipient : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hne : recipient ≠ accrueFeeRecipient evm)
    (hvalid : ¬ (recipient = AccountAddress.ofNat 0 ∧ feeRecipientFee evm ≠ ⟨0⟩)) :
    ABlock config evm ⟨contract, setFeeRecipientLocals recipient, imms⟩
      setFeeRecipientTransition.body (setFeeRecipientFrame evm imms recipient)
      setFeeRecipientTail := by
  have hpre := adminPrefix evm (setFeeRecipientLocals recipient) imms setFeeRecipientAdminTail
    hwv hhi howner
  apply ABlock.requireStep (ABlock.requireStep hpre ?_) ?_
  · rw [setFeeRecipientDifferentSource evm imms recipient, decide_eq_true hne]
  · rw [setFeeRecipientValidSource evm imms recipient, decide_eq_true hvalid]

theorem setFeeRecipientRevertsSame (evm : State) (imms : Store) (recipient : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (heq : recipient = accrueFeeRecipient evm) :
    ExecTransitionBody config contract evm (setFeeRecipientLocals recipient)
      setFeeRecipientTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hpre := adminPrefix evm (setFeeRecipientLocals recipient) imms setFeeRecipientAdminTail
    hwv hhi howner
  exact hpre.requireRevert (by
    rw [setFeeRecipientDifferentSource evm imms recipient]
    simp only [heq, ne_eq, not_true_eq_false, decide_false])

theorem setFeeRecipientRevertsZero (evm : State) (imms : Store) (recipient : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hne : recipient ≠ accrueFeeRecipient evm)
    (hbad : recipient = AccountAddress.ofNat 0 ∧ feeRecipientFee evm ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (setFeeRecipientLocals recipient)
      setFeeRecipientTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have hpre := adminPrefix evm (setFeeRecipientLocals recipient) imms setFeeRecipientAdminTail
    hwv hhi howner
  have hdiff := hpre.requireStep
    (by rw [setFeeRecipientDifferentSource evm imms recipient, decide_eq_true hne])
  exact hdiff.requireRevert (by
    rw [setFeeRecipientValidSource evm imms recipient, decide_eq_false (not_not_intro hbad)])

theorem setFeeRecipientAccrualReverts (evm : State) (imms : Store) (recipient : AccountAddress)
    (hpre : ABlock config evm ⟨contract, setFeeRecipientLocals recipient, imms⟩
      setFeeRecipientTransition.body (setFeeRecipientFrame evm imms recipient) setFeeRecipientTail)
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .reverted) :
    ExecTransitionBody config contract evm (setFeeRecipientLocals recipient)
      setFeeRecipientTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply hpre.run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedAccrueInterestFunction)
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]; rfl) rfl rfl hbody)

theorem setFeeRecipientAccrualStatic (evm : State) (imms : Store) (recipient : AccountAddress)
    (hpre : ABlock config evm ⟨contract, setFeeRecipientLocals recipient, imms⟩
      setFeeRecipientTransition.body (setFeeRecipientFrame evm imms recipient) setFeeRecipientTail)
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body .staticViolation) :
    ExecTransitionBody config contract evm (setFeeRecipientLocals recipient)
      setFeeRecipientTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply hpre.run
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (callee := allocatedAccrueInterestFunction.toCallable)
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]; rfl) rfl rfl hbody)

theorem setFeeRecipientBodyReturns (evm evm' : State) (imms : Store) (recipient : AccountAddress)
    (final : Frame) (ptr : UInt256)
    (hpre : ABlock config evm ⟨contract, setFeeRecipientLocals recipient, imms⟩
      setFeeRecipientTransition.body (setFeeRecipientFrame evm imms recipient) setFeeRecipientTail)
    (hbody : ExecFuncBody config (accrueInterestFrame imms ⟨128⟩) evm
      allocatedAccrueInterestFunction.body (.returned final evm' [uint256Value ptr])) :
    ExecTransitionBody config contract evm (setFeeRecipientLocals recipient)
      setFeeRecipientTransition.body
      (.returned (setFeeRecipientResumeFrame evm imms recipient ptr)
        (setFeeRecipientState evm' recipient) none) imms := by
  apply ExecFuncBody.execBlockOK
  apply hpre.run
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedAccrueInterestFunction)
    (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]; rfl) rfl rfl hbody)
  have hvalue : evalExpr? config (setFeeRecipientResumeFrame evm imms recipient ptr) evm'
      (.var "newFeeRecipient") = .ok (.address recipient) := by
    simp [evalExpr?, setFeeRecipientResumeFrame, setFeeRecipientFrame, adminFrame,
      setFeeRecipientLocals, Std.HashMap.getElem_insert, EvalResult.ofOption]
  apply ExecBlock.consNormal (ExecStmt.assign hvalue
    (assignStorage_feeRecipient evm' _ imms recipient (by
      simp [setFeeRecipientResumeFrame, setFeeRecipientFrame, adminFrame, setFeeRecipientLocals])))
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [.address recipient]) ?_) ExecBlock.nil
  simp [evalExprs?, evalExpr?, setFeeRecipientResumeFrame, setFeeRecipientFrame, adminFrame,
    setFeeRecipientLocals, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1
