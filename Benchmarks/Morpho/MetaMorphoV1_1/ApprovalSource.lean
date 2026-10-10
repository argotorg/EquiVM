import Benchmarks.Morpho.MetaMorphoV1_1.NestedMappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation

/-! Allowance writes and the internal approval helper, including static execution. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def approvalFunction : FunctionDecl := contract.functions[72]!

def approveFunction : FunctionDecl := contract.functions[36]!

def approvalSlot (owner spender : AccountAddress) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨1⟩ (UInt256.ofNat owner.toNat))
    (UInt256.ofNat spender.toNat)

def approvalState (evm : State) (owner spender : AccountAddress) (value : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approvalSlot owner spender) value

def approvalFrame (imms : Store) (owner spender : AccountAddress) (value : UInt256)
    (emitEvent : Bool) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert "emitEvent" (.bool emitEvent)).insert "value"
      (uint256Value value)).insert "spender" (.address spender)).insert "owner" (.address owner)
    immutables := imms }

def approvalTail : List Stmt :=
  [.assign .storage ⟨"_allowances", [.mindex (.var "owner"), .mindex (.var "spender")]⟩
    (.var "value"),
    .ite (.var "emitEvent") [.emit "Approval" [.var "owner", .var "spender", .var "value"]] []]

theorem approvalFunction_body :
    approvalFunction.body =
      [.require (.binary .ne (.var "owner") (.cast (.intLit 0) (.elem .address))),
        .require (.binary .ne (.var "spender") (.cast (.intLit 0) (.elem .address)))] ++
      approvalTail := by decide +kernel

theorem assignStorage_allowances (evm : State) (locals imms : Store)
    (owner spender : AccountAddress) (value : UInt256)
    (hbase : locals.get? "_allowances" = none)
    (ho : locals.get? "owner" = some (.address owner))
    (hs : locals.get? "spender" = some (.address spender)) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨"_allowances", [.mindex (.var "owner"), .mindex (.var "spender")]⟩
      (uint256Value value) =
      .ok (⟨contract, locals, imms⟩, approvalState evm owner spender value) := by
  apply assignStorageRef_storage_scalar_value
    (er := ⟨"_allowances", [.mindex (.address owner), .mindex (.address spender)]⟩)
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) hbase
    (evalStorageRef_twoAddressIndices "_allowances" "owner" "spender" owner spender ho hs)
    rfl rfl (loc := uint256Loc (approvalSlot owner spender))
  · change some (StorageAddr.leaf (uint256Loc
      (solcMappingSlot (solcMappingSlot ⟨1⟩ (keyValueToWord (.address owner)))
        (keyValueToWord (.address spender))))) = _
    rw [keyValueToWord_address, keyValueToWord_address]
    rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm _ value

theorem approvalOwnerCondition (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) (emitEvent : Bool) :
    evalExpr? config (approvalFrame imms owner spender value emitEvent) evm
      (.binary .ne (.var "owner") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (owner ≠ ⟨0, by decide⟩))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, approvalFrame, store_get_self, EvalResult.ofOption]
  · exact evalAddressLiteral _ _ _ ⟨0, by decide⟩

theorem approvalSpenderCondition (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) (emitEvent : Bool) :
    evalExpr? config (approvalFrame imms owner spender value emitEvent) evm
      (.binary .ne (.var "spender") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (spender ≠ ⟨0, by decide⟩))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, approvalFrame,
      store_get_ne _ _ (by decide : ("owner" == "spender") = false),
      store_get_self, EvalResult.ofOption]
  · exact evalAddressLiteral _ _ _ ⟨0, by decide⟩

theorem approvalPrefix (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) (emitEvent : Bool)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩) :
    ABlock config evm (approvalFrame imms owner spender value emitEvent) approvalFunction.body
      (approvalFrame imms owner spender value emitEvent) approvalTail := by
  rw [approvalFunction_body]
  apply ABlock.requireStep (ABlock.requireStep ABlock.start ?_) ?_
  · rw [approvalOwnerCondition, decide_eq_true ho]
  · rw [approvalSpenderCondition, decide_eq_true hs]

theorem approvalAssign (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) (emitEvent : Bool) :
    ExecStmt config (approvalFrame imms owner spender value emitEvent) evm
      (.assign .storage ⟨"_allowances", [.mindex (.var "owner"), .mindex (.var "spender")]⟩
        (.var "value"))
      (.ok (approvalFrame imms owner spender value emitEvent)
        (approvalState evm owner spender value)) := by
  apply ExecStmt.assign (value := uint256Value value)
  · simp [evalExpr?, approvalFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  · exact assignStorage_allowances evm _ imms owner spender value
      (by simp)
      (by simp)
      (by simp [Std.HashMap.getElem_insert])

theorem approvalBody (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) (emitEvent : Bool)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩) :
    ExecFuncBody config (approvalFrame imms owner spender value emitEvent) evm
      approvalFunction.body
      (.returned (approvalFrame imms owner spender value emitEvent)
        (approvalState evm owner spender value) none) := by
  apply ExecFuncBody.execBlockOK
  apply (approvalPrefix imms evm owner spender value emitEvent ho hs).run
  apply ExecBlock.consNormal (approvalAssign imms evm owner spender value emitEvent)
  have hc : evalExpr? config (approvalFrame imms owner spender value emitEvent)
      (approvalState evm owner spender value) (.var "emitEvent") = .ok (.bool emitEvent) := by
    simp [evalExpr?, approvalFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  cases emitEvent with
  | false => exact ExecBlock.consNormal (ExecStmt.iteFalse hc ExecBlock.nil) ExecBlock.nil
  | true =>
      apply ExecBlock.consNormal (ExecStmt.iteTrue hc ?_) ExecBlock.nil
      apply ExecBlock.consNormal (ExecStmt.emit
        (vals := [.address owner, .address spender, uint256Value value]) ?_) ExecBlock.nil
      simp [evalExprs?, evalExpr?, approvalFrame, Std.HashMap.getElem_insert,
        EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem approvalBodyStatic (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) (emitEvent : Bool)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (approvalFrame imms owner spender value emitEvent) evm
      approvalFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply (approvalPrefix imms evm owner spender value emitEvent ho hs).run
  exact ExecBlock.consStatic
    (execStmt_assign_static (approvalAssign imms evm owner spender value emitEvent) hperm)

theorem approvalBodyReverts (imms : Store) (evm : State)
    (owner spender : AccountAddress) (value : UInt256) (emitEvent : Bool)
    (hbad : ¬ (owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)) :
    ExecFuncBody config (approvalFrame imms owner spender value emitEvent) evm
      approvalFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [approvalFunction_body]
  by_cases ho : owner ≠ ⟨0, by decide⟩
  · apply (ABlock.start.requireStep ?_).requireRevert
    · rw [approvalSpenderCondition, decide_eq_false (fun hs ↦ hbad ⟨ho, hs⟩)]
    · rw [approvalOwnerCondition, decide_eq_true ho]
  · exact ABlock.start.requireRevert (by rw [approvalOwnerCondition, decide_eq_false ho])

end Benchmarks.Morpho.MetaMorphoV1_1
