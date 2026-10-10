import Benchmarks.Morpho.MetaMorphoV1_1.BalanceMutation
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! The nonzero-address branch of the shared ERC20 update helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def balanceUpdateFunction : FunctionDecl := contract.functions[73]!

def balanceUpdateFrame (imms : Store) (sender recipient : AccountAddress) (value : UInt256) :
    Frame :=
  ⟨contract, (((∅ : Store).insert "value" (uint256Value value)).insert "to" (.address recipient))
    |>.insert "from" (.address sender), imms⟩

def balanceUpdateReadFrame (imms : Store) (sender recipient : AccountAddress)
    (value balance : UInt256) : Frame :=
  { balanceUpdateFrame imms sender recipient value with
    locals := (balanceUpdateFrame imms sender recipient value).locals.insert "fromBalance"
      (uint256Value balance) }

def balanceUpdateDebitBody : List Stmt :=
  [.letDecl "fromBalance" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.storage ⟨"_balances", [.mindex (.var "from")]⟩),
    .require (.binary .ge (.var "fromBalance") (.var "value")),
    .assign .storage ⟨"_balances", [.mindex (.var "from")]⟩
      (.cast (.binary .sub (.var "fromBalance") (.var "value"))
        (.elem (.int (.uint ⟨256, by decide⟩))))]

def balanceUpdateTail : List Stmt :=
  [.ite (.binary .eq (.var "to") (.cast (.intLit 0) (.elem .address)))
      [.assign .storage ⟨"_totalSupply", []⟩
        (.cast (.binary .sub (.storage ⟨"_totalSupply", []⟩) (.var "value"))
          (.elem (.int (.uint ⟨256, by decide⟩))))]
      [.assign .storage ⟨"_balances", [.mindex (.var "to")]⟩
        (.cast (.binary .add (.storage ⟨"_balances", [.mindex (.var "to")]⟩) (.var "value"))
          (.elem (.int (.uint ⟨256, by decide⟩))))],
    .emit "Transfer" [.var "from", .var "to", .var "value"]]

theorem balanceUpdateFunction_body :
    balanceUpdateFunction.body =
      [.ite (.binary .eq (.var "from") (.cast (.intLit 0) (.elem .address)))
        [.assign .storage ⟨"_totalSupply", []⟩
          (.inRange (.uint ⟨256, by decide⟩)
            (.binary .add (.storage ⟨"_totalSupply", []⟩) (.var "value")))]
        balanceUpdateDebitBody] ++ balanceUpdateTail := by decide +kernel

theorem balanceUpdateFromCondition (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256) :
    evalExpr? config (balanceUpdateFrame imms sender recipient value) evm
      (.binary .eq (.var "from") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (sender = ⟨0, by decide⟩))) := by
  apply evalExpr_addressEq
  · simp only [evalExpr?, balanceUpdateFrame, store_get_self, EvalResult.ofOption]
  · exact evalAddressLiteral _ _ _ ⟨0, by decide⟩

theorem balanceUpdateRead (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256) :
    ABlock config evm (balanceUpdateFrame imms sender recipient value) balanceUpdateDebitBody
      (balanceUpdateReadFrame imms sender recipient value (balanceWord evm sender))
      (balanceUpdateDebitBody.drop 1) := by
  apply ABlock.letStep ABlock.start
  exact evalStorage_balance evm _ imms "from" sender (by simp) (by simp)

theorem balanceUpdateEnough (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value balance : UInt256) :
    evalExpr? config (balanceUpdateReadFrame imms sender recipient value balance) evm
      (.binary .ge (.var "fromBalance") (.var "value")) =
      .ok (.bool (decide (value.toNat ≤ balance.toNat))) := by
  apply naturalGeSource
  · simp only [evalExpr?, balanceUpdateReadFrame, store_get_self, EvalResult.ofOption]
  · simp [evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
      Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem balanceUpdateDebit (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256) :
    ExecStmt config (balanceUpdateReadFrame imms sender recipient value (balanceWord evm sender))
      evm (balanceUpdateDebitBody[2]!)
      (.ok (balanceUpdateReadFrame imms sender recipient value (balanceWord evm sender))
        (balanceDebitState evm sender value)) := by
  apply ExecStmt.assign (value := uint256Value (UInt256.sub (balanceWord evm sender) value))
  · apply wrappingSubSource
    · simp only [evalExpr?, balanceUpdateReadFrame, store_get_self, EvalResult.ofOption]
    · simp [evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
        Std.HashMap.getElem_insert, EvalResult.ofOption]
  · exact assignStorage_balance evm _ imms "from" sender _
      (by simp [balanceUpdateFrame])
      (by simp [balanceUpdateFrame, Std.HashMap.getElem_insert])

theorem balanceUpdateTailReturns (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value balance : UInt256)
    (hto : recipient ≠ ⟨0, by decide⟩) :
    ExecBlock config (balanceUpdateReadFrame imms sender recipient value balance) evm
      balanceUpdateTail
      (.ok (balanceUpdateReadFrame imms sender recipient value balance)
        (balanceStore evm recipient (balanceWord evm recipient + value))) := by
  have hc : evalExpr? config (balanceUpdateReadFrame imms sender recipient value balance) evm
      (.binary .eq (.var "to") (.cast (.intLit 0) (.elem .address))) = .ok (.bool false) := by
    have h := evalExpr_addressEq (cfg := config)
      (solm := balanceUpdateReadFrame imms sender recipient value balance) (evm := evm)
      (a := recipient) (b := ⟨0, by decide⟩)
      (lhs := .var "to") (rhs := .cast (.intLit 0) (.elem .address))
      (by simp [evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
        Std.HashMap.getElem_insert, EvalResult.ofOption])
      (evalAddressLiteral _ _ _ ⟨0, by decide⟩)
    simpa only [decide_eq_false hto] using h
  refine ExecBlock.consNormal
    (solm' := balanceUpdateReadFrame imms sender recipient value balance)
    (evm' := balanceStore evm recipient (balanceWord evm recipient + value))
    (ExecStmt.iteFalse hc ?_) ?_
  · apply ExecBlock.consNormal (ExecStmt.assign (value := uint256Value
      (balanceWord evm recipient + value)) ?_ ?_) ExecBlock.nil
    · apply wrappingAddSource
      · exact evalStorage_balance evm _ imms "to" recipient
          (by simp [balanceUpdateFrame])
          (by simp [balanceUpdateFrame, Std.HashMap.getElem_insert])
      · simp [evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
          Std.HashMap.getElem_insert, EvalResult.ofOption]
    · exact assignStorage_balance evm _ imms "to" recipient _
        (by simp [balanceUpdateFrame])
        (by simp [balanceUpdateFrame, Std.HashMap.getElem_insert])
  · apply ExecBlock.consNormal (ExecStmt.emit
      (vals := [.address sender, .address recipient, uint256Value value]) ?_) ExecBlock.nil
    simp [evalExprs?, evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
      Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem balanceUpdateMoveBody (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256)
    (hfrom : sender ≠ ⟨0, by decide⟩) (hto : recipient ≠ ⟨0, by decide⟩)
    (hbal : value.toNat ≤ (balanceWord evm sender).toNat) :
    ExecFuncBody config (balanceUpdateFrame imms sender recipient value) evm
      balanceUpdateFunction.body
      (.returned (balanceUpdateReadFrame imms sender recipient value (balanceWord evm sender))
        (balanceMoveState evm sender recipient value) none) := by
  apply ExecFuncBody.execBlockOK
  rw [balanceUpdateFunction_body]
  refine ExecBlock.consNormal
    (solm' := balanceUpdateReadFrame imms sender recipient value (balanceWord evm sender))
    (evm' := balanceDebitState evm sender value)
    (ExecStmt.iteFalse (by rw [balanceUpdateFromCondition, decide_eq_false hfrom]) ?_) ?_
  · apply (balanceUpdateRead imms evm sender recipient value).run
    apply ExecBlock.consNormal (ExecStmt.requireTrue
      (by rw [balanceUpdateEnough, decide_eq_true hbal]))
    exact ExecBlock.consNormal (balanceUpdateDebit imms evm sender recipient value) ExecBlock.nil
  · exact balanceUpdateTailReturns imms _ sender recipient value _ hto

theorem balanceUpdateMoveReverts (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256)
    (hfrom : sender ≠ ⟨0, by decide⟩)
    (hbal : ¬ value.toNat ≤ (balanceWord evm sender).toNat) :
    ExecFuncBody config (balanceUpdateFrame imms sender recipient value) evm
      balanceUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [balanceUpdateFunction_body]
  apply ExecBlock.consRevert (ExecStmt.iteFalse
    (by rw [balanceUpdateFromCondition, decide_eq_false hfrom]) ?_)
  apply (balanceUpdateRead imms evm sender recipient value).requireRevert
  rw [balanceUpdateEnough, decide_eq_false hbal]

theorem balanceUpdateMoveStatic (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256)
    (hfrom : sender ≠ ⟨0, by decide⟩)
    (hbal : value.toNat ≤ (balanceWord evm sender).toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (balanceUpdateFrame imms sender recipient value) evm
      balanceUpdateFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [balanceUpdateFunction_body]
  apply ExecBlock.consStatic (ExecStmt.iteFalse
    (by rw [balanceUpdateFromCondition, decide_eq_false hfrom]) ?_)
  apply (balanceUpdateRead imms evm sender recipient value).run
  apply ExecBlock.consNormal (ExecStmt.requireTrue
    (by rw [balanceUpdateEnough, decide_eq_true hbal]))
  exact ExecBlock.consStatic
    (execStmt_assign_static (balanceUpdateDebit imms evm sender recipient value) hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
