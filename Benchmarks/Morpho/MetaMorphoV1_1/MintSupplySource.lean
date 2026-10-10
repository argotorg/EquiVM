import Benchmarks.Morpho.MetaMorphoV1_1.BalanceUpdateSource

/-! The minting branch of the ERC20 update helper, including checked supply growth. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def mintOldSupply (evm : State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

abbrev mintSupplyFits (evm : State) (value : UInt256) : Prop :=
  (mintOldSupply evm).toNat + value.toNat < UInt256.size

def mintSupplyState (evm : State) (value : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ (mintOldSupply evm + value)

def mintBalanceState (evm : State) (recipient : AccountAddress) (value : UInt256) : State :=
  let changed := mintSupplyState evm value
  balanceStore changed recipient (balanceWord changed recipient + value)

def mintSupplyExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.storage ⟨"_totalSupply", []⟩) (.var "value"))

def mintSupplyAssign : Stmt := .assign .storage ⟨"_totalSupply", []⟩ mintSupplyExpr

theorem balanceMintValueSource (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) :
    evalExpr? config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
      evm (.var "value") = .ok (uint256Value value) := by
  simp [evalExpr?, balanceUpdateFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem balanceMintSupplySource (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) :
    evalExpr? config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
      evm (.storage ⟨"_totalSupply", []⟩) = .ok (uint256Value (mintOldSupply evm)) := by
  exact evalStorage_totalSupply evm _ imms (by simp)

theorem mintSupplyExprSource (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) (hfit : mintSupplyFits evm value) :
    evalExpr? config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
      evm mintSupplyExpr = .ok (uint256Value (mintOldSupply evm + value)) := by
  exact checkedAddSourceOk (balanceMintSupplySource imms evm recipient value)
    (balanceMintValueSource imms evm recipient value) hfit

theorem mintSupplyAssignment (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) (hfit : mintSupplyFits evm value) :
    ExecStmt config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value) evm
      mintSupplyAssign
      (.ok (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
        (mintSupplyState evm value)) := by
  apply ExecStmt.assign (mintSupplyExprSource imms evm recipient value hfit)
  exact assignStorageRef_storage_scalar_value (er := ⟨"_totalSupply", []⟩)
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) (by simp [balanceUpdateFrame])
    (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
    rfl rfl rfl (.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm ⟨2⟩ _)

theorem balanceMintTail (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) (hto : recipient ≠ AccountAddress.ofNat 0) :
    ExecBlock config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value) evm
      balanceUpdateTail
      (.ok (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
        (balanceStore evm recipient (balanceWord evm recipient + value))) := by
  have hc : evalExpr? config
      (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value) evm
      (.binary .eq (.var "to") (.cast (.intLit 0) (.elem .address))) = .ok (.bool false) := by
    have h := evalExpr_addressEq (cfg := config)
      (solm := balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value) (evm := evm)
      (a := recipient) (b := AccountAddress.ofNat 0)
      (lhs := .var "to") (rhs := .cast (.intLit 0) (.elem .address))
      (by simp [evalExpr?, balanceUpdateFrame, Std.HashMap.getElem_insert, EvalResult.ofOption])
      (evalAddressLiteral _ _ _ (AccountAddress.ofNat 0))
    simpa only [decide_eq_false hto] using h
  refine ExecBlock.consNormal
    (solm' := balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
    (evm' := balanceStore evm recipient (balanceWord evm recipient + value))
    (ExecStmt.iteFalse hc ?_) ?_
  · apply ExecBlock.consNormal (ExecStmt.assign (value := uint256Value
      (balanceWord evm recipient + value)) ?_ ?_) ExecBlock.nil
    · apply wrappingAddSource
      · exact evalStorage_balance evm _ imms "to" recipient
          (by simp [balanceUpdateFrame])
          (by simp [balanceUpdateFrame, Std.HashMap.getElem_insert])
      · exact balanceMintValueSource imms evm recipient value
    · exact assignStorage_balance evm _ imms "to" recipient _
        (by simp [balanceUpdateFrame])
        (by simp [balanceUpdateFrame, Std.HashMap.getElem_insert])
  · apply ExecBlock.consNormal (ExecStmt.emit
      (vals := [.address (AccountAddress.ofNat 0), .address recipient, uint256Value value]) ?_)
      ExecBlock.nil
    simp [evalExprs?, evalExpr?, balanceUpdateFrame, Std.HashMap.getElem_insert,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem balanceMintBody (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) (hto : recipient ≠ AccountAddress.ofNat 0)
    (hfit : mintSupplyFits evm value) :
    ExecFuncBody config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value) evm
      balanceUpdateFunction.body
      (.returned (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
        (mintBalanceState evm recipient value) none) := by
  apply ExecFuncBody.execBlockOK
  rw [balanceUpdateFunction_body]
  refine ExecBlock.consNormal
    (solm' := balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value)
    (evm' := mintSupplyState evm value) (ExecStmt.iteTrue ?_ ?_) ?_
  · rw [balanceUpdateFromCondition]; rfl
  · exact ExecBlock.consNormal (mintSupplyAssignment imms evm recipient value hfit) ExecBlock.nil
  · exact balanceMintTail imms (mintSupplyState evm value) recipient value hto

theorem balanceMintBodyReverts (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) (hbad : ¬ mintSupplyFits evm value) :
    ExecFuncBody config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value) evm
      balanceUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [balanceUpdateFunction_body]
  apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
  · rw [balanceUpdateFromCondition]; rfl
  · exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (checkedAddSourceOverflow (balanceMintSupplySource imms evm recipient value)
        (balanceMintValueSource imms evm recipient value) (Nat.le_of_not_gt hbad)))

theorem balanceMintBodyStatic (imms : Store) (evm : State) (recipient : AccountAddress)
    (value : UInt256) (hfit : mintSupplyFits evm value) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (balanceUpdateFrame imms (AccountAddress.ofNat 0) recipient value) evm
      balanceUpdateFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [balanceUpdateFunction_body]
  apply ExecBlock.consStatic (ExecStmt.iteTrue ?_ ?_)
  · rw [balanceUpdateFromCondition]; rfl
  · exact ExecBlock.consStatic
      (execStmt_assign_static (mintSupplyAssignment imms evm recipient value hfit) hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
