import Benchmarks.Morpho.MetaMorphoV1_1.MintSupplySource

/-! The recipient guard and internal update call for ERC20 minting. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def mintInternalFunction : FunctionDecl := contract.functions[48]!

def mintInternalFrame (imms : Store) (recipient : AccountAddress) (value : UInt256) : Frame :=
  ⟨contract,
    ((∅ : Store).insert "value" (uint256Value value)).insert "account" (.address recipient), imms⟩

def mintAllowed (evm : State) (recipient : AccountAddress) (value : UInt256) : Prop :=
  recipient ≠ AccountAddress.ofNat 0 ∧ mintSupplyFits evm value

def mintInternalTail : List Stmt :=
  [.internalCall "_update" [.cast (.intLit 0) (.elem .address), .var "account", .var "value"]
    "__c0"]

theorem mintInternalFunction_body :
    mintInternalFunction.body =
      [.require (.binary .ne (.var "account") (.cast (.intLit 0) (.elem .address)))] ++
      mintInternalTail := by decide +kernel

theorem mintRecipientCondition (imms : Store) (evm : State)
    (recipient : AccountAddress) (value : UInt256) :
    evalExpr? config (mintInternalFrame imms recipient value) evm
      (.binary .ne (.var "account") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (recipient ≠ AccountAddress.ofNat 0))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, mintInternalFrame, store_get_self, EvalResult.ofOption]
  · exact evalAddressLiteral _ _ _ (AccountAddress.ofNat 0)

theorem mintUpdateArgs (imms : Store) (evm : State)
    (recipient : AccountAddress) (value : UInt256) :
    evalExprs? config (mintInternalFrame imms recipient value) evm
      [.cast (.intLit 0) (.elem .address), .var "account", .var "value"] =
      .ok [.address (AccountAddress.ofNat 0), .address recipient, uint256Value value] := by
  have hz : evalExpr? config (mintInternalFrame imms recipient value) evm
      (.cast (.intLit 0) (.elem .address)) = .ok (.address (AccountAddress.ofNat 0)) :=
    evalAddressLiteral _ _ _ (AccountAddress.ofNat 0)
  simp only [evalExprs?, hz, bind, EvalResult.bind]
  simp [evalExpr?, mintInternalFrame, Std.HashMap.getElem_insert, EvalResult.ofOption, pure]

theorem mintInternalPrefix (imms : Store) (evm : State)
    (recipient : AccountAddress) (value : UInt256) (hto : recipient ≠ AccountAddress.ofNat 0) :
    ABlock config evm (mintInternalFrame imms recipient value) mintInternalFunction.body
      (mintInternalFrame imms recipient value) mintInternalTail := by
  rw [mintInternalFunction_body]
  exact ABlock.start.requireStep (by rw [mintRecipientCondition, decide_eq_true hto])

theorem mintInternalBody (imms : Store) (evm : State)
    (recipient : AccountAddress) (value : UInt256) (hgood : mintAllowed evm recipient value) :
    ExecFuncBody config (mintInternalFrame imms recipient value) evm mintInternalFunction.body
      (.returned { mintInternalFrame imms recipient value with
        locals := (mintInternalFrame imms recipient value).locals.insert "__c0" .unit }
        (mintBalanceState evm recipient value) none) := by
  apply ExecFuncBody.execBlockOK
  apply (mintInternalPrefix imms evm recipient value hgood.1).run
  exact ExecBlock.consNormal
    (internalCallFunctionReturn (callee := balanceUpdateFunction)
      (mintUpdateArgs imms evm recipient value) rfl rfl
      (balanceMintBody imms evm recipient value hgood.1 hgood.2)) ExecBlock.nil

theorem mintInternalReverts (imms : Store) (evm : State)
    (recipient : AccountAddress) (value : UInt256) (hbad : ¬ mintAllowed evm recipient value) :
    ExecFuncBody config (mintInternalFrame imms recipient value) evm mintInternalFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hto : recipient ≠ AccountAddress.ofNat 0
  · apply (mintInternalPrefix imms evm recipient value hto).run
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := balanceUpdateFunction)
      (mintUpdateArgs imms evm recipient value) rfl rfl
      (balanceMintBodyReverts imms evm recipient value (fun hfit ↦ hbad ⟨hto, hfit⟩)))
  · rw [mintInternalFunction_body]
    exact ABlock.start.requireRevert (by rw [mintRecipientCondition, decide_eq_false hto])

theorem mintInternalStatic (imms : Store) (evm : State)
    (recipient : AccountAddress) (value : UInt256) (hgood : mintAllowed evm recipient value)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (mintInternalFrame imms recipient value) evm mintInternalFunction.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply (mintInternalPrefix imms evm recipient value hgood.1).run
  exact ExecBlock.consStatic
    (ExecStmt.internalCallStatic (callee := balanceUpdateFunction.toCallable)
      (mintUpdateArgs imms evm recipient value) rfl rfl
      (balanceMintBodyStatic imms evm recipient value hgood.2 hperm))

theorem mintCall {locals imms : Store} {evm : State} {recipient : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address recipient, uint256Value value])
    (hgood : mintAllowed evm recipient value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_mint" args ret)
      (.ok ⟨contract, locals.insert ret .unit, imms⟩ (mintBalanceState evm recipient value)) :=
  internalCallFunctionReturn (callee := mintInternalFunction) hargs rfl rfl
    (mintInternalBody imms evm recipient value hgood)

theorem mintCallReverts {locals imms : Store} {evm : State} {recipient : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address recipient, uint256Value value])
    (hbad : ¬ mintAllowed evm recipient value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_mint" args ret) .reverted :=
  internalCallFunctionRevert (callee := mintInternalFunction) hargs rfl rfl
    (mintInternalReverts imms evm recipient value hbad)

theorem mintCallStatic {locals imms : Store} {evm : State} {recipient : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address recipient, uint256Value value])
    (hgood : mintAllowed evm recipient value) (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_mint" args ret)
      .staticViolation :=
  ExecStmt.internalCallStatic (callee := mintInternalFunction.toCallable) hargs rfl rfl
    (mintInternalStatic imms evm recipient value hgood hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
