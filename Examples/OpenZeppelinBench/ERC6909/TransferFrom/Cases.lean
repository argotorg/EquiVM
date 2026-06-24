import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

abbrev transferFromTailReceiverBody : List Stmt :=
  [ .letDecl "toBalance" (some uint256)
      (.storage (balanceRef (.var "receiver") (.var "id"))),
    .assign .storage (balanceRef (.var "receiver") (.var "id"))
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))),
    .return (.boolLit true) ]

abbrev transferFromAfterAllowanceBody : List Stmt :=
  [ .require (.binary .ne (.var "sender") zeroAddr),
    .require (.binary .ne (.var "receiver") zeroAddr),
    .letDecl "fromBalance" (some uint256)
      (.storage (balanceRef (.var "sender") (.var "id"))),
    .require (.binary .ge (.var "fromBalance") (.var "amount")),
    .assign .storage (balanceRef (.var "sender") (.var "id"))
      (.binary .sub (.var "fromBalance") (.var "amount")),
    .letDecl "toBalance" (some uint256)
      (.storage (balanceRef (.var "receiver") (.var "id"))),
    .assign .storage (balanceRef (.var "receiver") (.var "id"))
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))),
    .return (.boolLit true) ]

theorem erc6909TransferFromAllowanceMaxPrefixBlock (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    {result : ExecResult}
    (htail :
      ExecBlock config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm transferFromAfterAllowanceBody result) :
    ExecBlock config { contract := contract, locals := transferFromStore I }
      evm transferFromTransition.body result := by
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm)
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteFalse
        (result := .ok currentFrame evm)
        hallowanceMax ?_) ?_
    · exact ExecBlock.nil
    · exact ExecBlock.nil
  simpa [transferFromAfterAllowanceBody] using htail

theorem erc6909TransferFromTailReceiverCoreCurrentAllowance
    (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ExecBlock config
      { contract := contract,
        locals := transferFromTailStoreFromBalance (transferFromStoreCurrentAllowance evm I)
          evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      transferFromTailReceiverBody
      (.returned
        { contract := contract,
          locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I)
            evm I }
        (transferFromTailPostState evm I) (some (.bool true))) := by
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  dsimp [transferFromTailReceiverBody]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_receiver_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_receiver evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_tail_receiver_credit_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hfit)
      (transferFromTailAssignReceiverBalance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_receiver evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

set_option maxHeartbeats 50000000 in
theorem erc6909TransferFromAfterAllowanceCore (evm : EVM.State) (I : ExecutionEnv)
    (hsenderNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord evm I).toNat)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody
      (.returned
        { contract := contract,
          locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I)
            evm I }
        (transferFromTailPostState evm I) (some (.bool true))) := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsenderNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreceiverNonzero) ?_
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_sender_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_tail_sender_debit_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hbalanceEnough)
      (transferFromTailAssignSenderBalance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  change ExecBlock config
    { contract := contract,
      locals := transferFromTailStoreFromBalance (transferFromStoreCurrentAllowance evm I)
        evm I }
    (transferFromTailAfterSenderBalanceState evm I)
    transferFromTailReceiverBody
    (.returned
      { contract := contract,
        locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I)
          evm I }
      (transferFromTailPostState evm I) (some (.bool true)))
  exact erc6909TransferFromTailReceiverCoreCurrentAllowance evm I hfit

theorem erc6909TransferFromAfterAllowanceReverts_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_sender_nonzero_false_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hz))

theorem erc6909TransferFromAfterAllowanceReverts_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_receiver_nonzero_false_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hz))

set_option maxHeartbeats 50000000 in
theorem erc6909TransferFromAfterAllowanceReverts_insufficient_balance
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_sender_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_tail_sender_balance_ge_false_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hlt))

set_option maxHeartbeats 50000000 in
theorem erc6909TransferFromAfterAllowanceReverts_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_sender_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_tail_sender_debit_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) henough)
      (transferFromTailAssignSenderBalance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_receiver_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_receiver evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (evalExpr_transferFrom_tail_receiver_credit_revert_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hover))

/-- Source-side core for the allowance-debit success path of
`transferFrom(address,address,uint256,uint256)`.

The hypotheses name the branch guards that the EVM body at pc 388 must establish on this path.  The
state threading below is deliberately explicit: the sender balance is read from
`transferFromAfterAllowanceState`, after the allowance write.
-/
theorem erc6909TransferFromBodyCoreAllowanceDebit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsenderNonzero :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I)
        (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I)
        (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := transferFromStoreToBalance evm I }
        (transferFromPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax hsenderNonzero hreceiverNonzero ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsenderNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreceiverNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_balance_ge_true evm I hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_sender_debit evm I hbalanceEnough)
      (transferFromAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_receiver_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_receiver_credit evm I hfit)
      (transferFromAssignReceiverBalance evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

set_option maxHeartbeats 12000000 in
theorem erc6909TransferFromBodyCoreAllowanceMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsenderNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord evm I).toNat)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ∃ cs, ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body
      (.returned cs (transferFromTailPostState evm I) (some (.bool true))) := by
  let cs : Frame :=
    { contract := contract
      locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I) evm I }
  refine ⟨cs, ExecFuncBody.execBlockRet ?_⟩
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceCore evm I hsenderNonzero hreceiverNonzero
      hbalanceEnough hfit)

theorem erc6909TransferFromBodyRevertsAllowanceMax_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_sender_zero evm I hz)

theorem erc6909TransferFromBodyRevertsAllowanceMax_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_receiver_zero evm I hsender hz)

set_option maxHeartbeats 12000000 in
theorem erc6909TransferFromBodyRevertsAllowanceMax_insufficient_balance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_insufficient_balance evm I hsender hreceiver hlt)

set_option maxHeartbeats 12000000 in
theorem erc6909TransferFromBodyRevertsAllowanceMax_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_overflow evm I hsender hreceiver henough hover)

theorem erc6909TransferFromBodyCoreNoAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsenderNonzero :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord evm I).toNat)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
        (transferFromTailPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsenderNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreceiverNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true evm I hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_tail_sender_debit evm I hbalanceEnough)
      (transferFromTailAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_receiver_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_tail_receiver_credit evm I hfit)
      (transferFromTailAssignReceiverBalance evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem erc6909TransferFromBodyRevertsAllowance_insufficient
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue hallowanceGate ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    change ExecBlock config currentFrame evm
      [ .ite (.binary .lt (.var "currentAllowance") maxUint256Lit)
          [ .require (.binary .ge (.var "currentAllowance") (.var "amount")),
            .assign .storage (allowanceRef (.var "sender") sender (.var "id"))
              (.binary .sub (.var "currentAllowance") (.var "amount")) ]
          [] ]
      .reverted
    refine ExecBlock.consRevert ?_
    refine ExecStmt.iteTrue (result := .reverted) hallowanceNotMax ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (by
          simpa [transferFromStoreCurrentAllowance] using
            evalExpr_transferFrom_allowance_ge_false evm I hlt))

theorem erc6909TransferFromBodyRevertsAllowance_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_sender_nonzero_false_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hz))

theorem erc6909TransferFromBodyRevertsAllowance_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_receiver_nonzero_false_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hz))

theorem erc6909TransferFromBodyRevertsAllowance_insufficient_balance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_sender_balance_ge_false evm I hlt))

theorem erc6909TransferFromBodyRevertsAllowance_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hover : UInt256.size ≤ transferFromReceiverCreditNat evm I) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_balance_ge_true evm I hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_sender_debit evm I hbalanceEnough)
      (transferFromAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_receiver_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (evalExpr_transferFrom_receiver_credit_revert evm I hover))

theorem erc6909TransferFromBodyRevertsNoAllowance_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_sender_nonzero_false_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hz))

theorem erc6909TransferFromBodyRevertsNoAllowance_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hsender)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_receiver_nonzero_false_of_get evm (transferFromStore I) I
        (transferFromStore_receiver I) hz))

theorem erc6909TransferFromBodyRevertsNoAllowance_insufficient
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_receiver I) hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_tail_sender_balance_ge_false evm I hlt))

theorem erc6909TransferFromBodyRevertsNoAllowance_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_receiver I) hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_tail_sender_debit evm I henough)
      (transferFromTailAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_receiver_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (evalExpr_transferFrom_tail_receiver_credit_revert evm I hover))

/-! ## Generic scratch-memory helpers for `transferFrom` EVM tails -/


end OpenZeppelinBench.ERC6909
