import Benchmarks.Morpho.MetaMorphoV1_1.BalanceUpdateSource

/-! Address guards and internal-call composition for ERC20 transfers. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def transferFunction : FunctionDecl := contract.functions[42]!

def transferAllowed (evm : State) (sender recipient : AccountAddress) (value : UInt256) : Prop :=
  sender ≠ ⟨0, by decide⟩ ∧ recipient ≠ ⟨0, by decide⟩ ∧
    value.toNat ≤ (balanceWord evm sender).toNat

def transferInternalTail : List Stmt :=
  [.internalCall "_update" [.var "from", .var "to", .var "value"] "__c0"]

theorem transferFunction_body :
    transferFunction.body =
      [.require (.binary .ne (.var "from") (.cast (.intLit 0) (.elem .address))),
        .require (.binary .ne (.var "to") (.cast (.intLit 0) (.elem .address)))] ++
      transferInternalTail := by decide +kernel

theorem transferFromCondition (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256) :
    evalExpr? config (balanceUpdateFrame imms sender recipient value) evm
      (.binary .ne (.var "from") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (sender ≠ ⟨0, by decide⟩))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, balanceUpdateFrame, store_get_self, EvalResult.ofOption]
  · exact evalAddressLiteral _ _ _ ⟨0, by decide⟩

theorem transferToCondition (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256) :
    evalExpr? config (balanceUpdateFrame imms sender recipient value) evm
      (.binary .ne (.var "to") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (recipient ≠ ⟨0, by decide⟩))) := by
  apply evalExpr_addressNe
  · simp [evalExpr?, balanceUpdateFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · exact evalAddressLiteral _ _ _ ⟨0, by decide⟩

theorem transferInternalPrefix (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256)
    (hfrom : sender ≠ ⟨0, by decide⟩) (hto : recipient ≠ ⟨0, by decide⟩) :
    ABlock config evm (balanceUpdateFrame imms sender recipient value) transferFunction.body
      (balanceUpdateFrame imms sender recipient value) transferInternalTail := by
  rw [transferFunction_body]
  apply ABlock.requireStep (ABlock.requireStep ABlock.start ?_) ?_
  · rw [transferFromCondition, decide_eq_true hfrom]
  · rw [transferToCondition, decide_eq_true hto]

theorem transferUpdateArgs (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256) :
    evalExprs? config (balanceUpdateFrame imms sender recipient value) evm
      [.var "from", .var "to", .var "value"] =
      .ok [.address sender, .address recipient, uint256Value value] := by
  simp [evalExprs?, evalExpr?, balanceUpdateFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem transferInternalBody (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256)
    (hgood : transferAllowed evm sender recipient value) :
    ExecFuncBody config (balanceUpdateFrame imms sender recipient value) evm transferFunction.body
      (.returned { balanceUpdateFrame imms sender recipient value with
        locals := (balanceUpdateFrame imms sender recipient value).locals.insert "__c0" .unit }
        (balanceMoveState evm sender recipient value) none) := by
  apply ExecFuncBody.execBlockOK
  apply (transferInternalPrefix imms evm sender recipient value hgood.1 hgood.2.1).run
  exact ExecBlock.consNormal
    (internalCallFunctionReturn (callee := balanceUpdateFunction)
      (transferUpdateArgs imms evm sender recipient value) rfl rfl
      (balanceUpdateMoveBody imms evm sender recipient value hgood.1 hgood.2.1 hgood.2.2))
    ExecBlock.nil

theorem transferInternalReverts (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256)
    (hbad : ¬ transferAllowed evm sender recipient value) :
    ExecFuncBody config (balanceUpdateFrame imms sender recipient value) evm transferFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hfrom : sender ≠ ⟨0, by decide⟩
  · by_cases hto : recipient ≠ ⟨0, by decide⟩
    · apply (transferInternalPrefix imms evm sender recipient value hfrom hto).run
      exact ExecBlock.consRevert
        (internalCallFunctionRevert (callee := balanceUpdateFunction)
          (transferUpdateArgs imms evm sender recipient value) rfl rfl
          (balanceUpdateMoveReverts imms evm sender recipient value hfrom
            (fun hbal ↦ hbad ⟨hfrom, hto, hbal⟩)))
    · rw [transferFunction_body]
      apply (ABlock.start.requireStep ?_).requireRevert
      · rw [transferToCondition, decide_eq_false hto]
      · rw [transferFromCondition, decide_eq_true hfrom]
  · rw [transferFunction_body]
    exact ABlock.start.requireRevert (by rw [transferFromCondition, decide_eq_false hfrom])

theorem transferInternalStatic (imms : Store) (evm : State)
    (sender recipient : AccountAddress) (value : UInt256)
    (hgood : transferAllowed evm sender recipient value) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (balanceUpdateFrame imms sender recipient value) evm transferFunction.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply (transferInternalPrefix imms evm sender recipient value hgood.1 hgood.2.1).run
  exact ExecBlock.consStatic
    (ExecStmt.internalCallStatic (callee := balanceUpdateFunction.toCallable)
      (transferUpdateArgs imms evm sender recipient value) rfl rfl
      (balanceUpdateMoveStatic imms evm sender recipient value hgood.1 hgood.2.2 hperm))

theorem transferCall {locals imms : Store} {evm : State} {sender recipient : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address sender, .address recipient, uint256Value value])
    (hgood : transferAllowed evm sender recipient value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_transfer" args ret)
      (.ok ⟨contract, locals.insert ret .unit, imms⟩
        (balanceMoveState evm sender recipient value)) :=
  internalCallFunctionReturn (callee := transferFunction) hargs rfl rfl
    (transferInternalBody imms evm sender recipient value hgood)

theorem transferCallReverts {locals imms : Store} {evm : State} {sender recipient : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address sender, .address recipient, uint256Value value])
    (hbad : ¬ transferAllowed evm sender recipient value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_transfer" args ret) .reverted :=
  internalCallFunctionRevert (callee := transferFunction) hargs rfl rfl
    (transferInternalReverts imms evm sender recipient value hbad)

theorem transferCallStatic {locals imms : Store} {evm : State} {sender recipient : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address sender, .address recipient, uint256Value value])
    (hgood : transferAllowed evm sender recipient value) (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_transfer" args ret)
      .staticViolation :=
  ExecStmt.internalCallStatic (callee := transferFunction.toCallable) hargs rfl rfl
    (transferInternalStatic imms evm sender recipient value hgood hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
