import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

private theorem evalBinaryOp_ne_address_ok (a b : AccountAddress) :
    evalBinaryOp? .ne (.address a) (.address b) =
      .ok (.bool (!(Value.address a == Value.address b))) := by
  rfl

def transferFromOperatorEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_operatorApprovals",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)),
      .mindex (.address evm.executionEnv.source)] }

def transferFromAllowanceEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_allowances",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)),
      .mindex (.address evm.executionEnv.source),
      .mindex (.int (Int.ofNat (transferFromIdWord I).toNat))] }

def transferFromSenderBalanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_balances",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)),
      .mindex (.int (Int.ofNat (transferFromIdWord I).toNat))] }

def transferFromReceiverBalanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_balances",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromReceiverWord I).toNat)),
      .mindex (.int (Int.ofNat (transferFromIdWord I).toNat))] }

theorem evalExpr_transferFrom_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_sender]

theorem evalExpr_transferFrom_id (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_id]

theorem evalExpr_transferFrom_sender_currentAllowance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_sender]

theorem evalExpr_transferFrom_id_currentAllowance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem evalExpr_transferFrom_sender_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_sender]

theorem evalExpr_transferFrom_receiver_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_receiver]

theorem evalExpr_transferFrom_id_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem evalExpr_transferFrom_receiver_toBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreToBalance_receiver]

theorem evalExpr_transferFrom_id_toBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem evalExpr_transferFrom_amount_currentAllowance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_amount]

theorem evalExpr_transferFrom_amount_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_amount]

theorem evalExpr_transferFrom_tail_sender_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "sender" = some (transferFromSenderValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_receiver_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_id_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "id" = some (transferFromIdValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_amount_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "amount" = some (transferFromAmountValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_receiver_toBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
    transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_id_toBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "id" = some (transferFromIdValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
    transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_amount_toBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "amount" = some (transferFromAmountValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
    transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_sender_nonzero_true_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "sender" = some (transferFromSenderValue I))
    (hnz : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  have hne : ((transferFromSenderValue I : Value) == .address zeroAccountAddress) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromSenderValue, Value.address.injEq] at h
    exact hnz h
  simp [evalBinaryOp?, transferFromSenderValue, hne]

theorem evalExpr_transferFrom_sender_nonzero_false_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "sender" = some (transferFromSenderValue I))
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "sender") zeroAddr) = .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  simp [evalBinaryOp?, transferFromSenderValue, zeroAccountAddress, hz]

theorem evalExpr_transferFrom_receiver_nonzero_true_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hnz : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  have hne :
      ((transferFromReceiverValue I : Value) == .address zeroAccountAddress) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromReceiverValue, Value.address.injEq] at h
    exact hnz h
  simp [evalBinaryOp?, transferFromReceiverValue, hne]

theorem evalExpr_transferFrom_receiver_nonzero_false_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  simp [evalBinaryOp?, transferFromReceiverValue, zeroAccountAddress, hz]

theorem evalStorageRef_transferFrom_operator (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (operatorApprovalRef (.var "sender") sender) =
        .ok (transferFromOperatorEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, operatorApprovalRef, sender, envValue,
    evalExpr_transferFrom_sender, transferFromOperatorEvaledRef, transferFromSenderValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transferFrom_operator (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (operatorApprovalRef (.var "sender") sender)) =
        .ok (transferFromOperatorValue evm I) := by
  rw [evalExpr_storage_scalar (t := .bool) (loc := boolLoc (transferFromOperatorSlot evm I))
    (hbase := by simp [transferFromStore, operatorApprovalRef])
    (her := evalStorageRef_transferFrom_operator evm I)
    (hty := by
      simp [storageTypeAt?, transferFromOperatorEvaledRef, contract, storageDecls, boolSt,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromOperatorEvaledRef,
      transferFromOperatorSlot])]
  simpa [transferFromOperatorValue, transferFromOperatorWord, boolLoc, boolOffset0Loc] using
    storageLocLoad_bool_offset0 evm (transferFromOperatorSlot evm I)

theorem evalExpr_transferFrom_env_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_transferFrom_sender_ne_env_false (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source)
    (haddr : AccountAddress.ofNat (transferFromSenderWord I).toNat = I.source) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.var "sender") sender) = .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_sender]
  have hcaller :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm sender =
        .ok (.address I.source) := by
    simpa [hsource] using evalExpr_transferFrom_env_sender evm I
  rw [hcaller]
  simp only [EvalResult.bind, bind]
  change evalBinaryOp? .ne (transferFromSenderValue I) (.address I.source) =
    .ok (.bool false)
  change evalBinaryOp? .ne
      (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
      (.address I.source) = .ok (.bool false)
  rw [evalBinaryOp_ne_address_ok]
  simp [transferFromSenderValue, haddr]
  all_goals decide

theorem evalExpr_transferFrom_sender_ne_env_true (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source)
    (hne : ((transferFromSenderValue I : Value) == .address I.source) = false) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.var "sender") sender) = .ok (.bool true) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_sender]
  have hcaller :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm sender =
        .ok (.address I.source) := by
    simpa [hsource] using evalExpr_transferFrom_env_sender evm I
  rw [hcaller]
  simp only [EvalResult.bind, bind]
  change evalBinaryOp? .ne (transferFromSenderValue I) (.address I.source) =
    .ok (.bool true)
  change evalBinaryOp? .ne
      (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
      (.address I.source) = .ok (.bool true)
  rw [evalBinaryOp_ne_address_ok]
  simp [hne]
  all_goals decide

theorem evalExpr_transferFrom_operator_not_true (evm : EVM.State) (I : ExecutionEnv)
    (hop : transferFromOperatorWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.unary .not (.storage (operatorApprovalRef (.var "sender") sender))) =
        .ok (.bool true) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_operator]
  have hval : ((transferFromOperatorWord evm I).val == 0) = true := by
    rw [hop]
    rfl
  simp only [EvalResult.bind, bind, EvalResult.ofOption]
  simp [evalUnaryOp?, transferFromOperatorValue, wordToElem, hval]

theorem evalExpr_transferFrom_operator_not_false (evm : EVM.State) (I : ExecutionEnv)
    (hop : transferFromOperatorWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.unary .not (.storage (operatorApprovalRef (.var "sender") sender))) =
        .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_operator]
  have hval : ((transferFromOperatorWord evm I).val == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro hv
    apply hop
    apply u256_inj
    change (transferFromOperatorWord evm I).val.val = 0
    exact congrArg Fin.val hv
  simp only [EvalResult.bind, bind, EvalResult.ofOption]
  simp [evalUnaryOp?, transferFromOperatorValue, wordToElem, hval]

theorem evalExpr_transferFrom_allowance_gate_false_sender (evm : EVM.State)
    (I : ExecutionEnv) (hsource : evm.executionEnv.source = I.source)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "sender") sender)
        (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
        .ok (.bool false) := by
  have haddr : AccountAddress.ofNat (transferFromSenderWord I).toNat = I.source := by
    rw [hsenderCaller]
    exact transferFromCaller_ofNat I
  have hleft :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") sender) = .ok (.bool false) := by
    exact evalExpr_transferFrom_sender_ne_env_false evm I hsource haddr
  rw [evalExpr?]
  by_cases hop : transferFromOperatorWord evm I = ⟨0⟩
  · have hright := evalExpr_transferFrom_operator_not_true evm I hop
    rw [hleft, hright]
    simp [EvalResult.bind, bind, pure, evalBinaryOp?]
  · have hright := evalExpr_transferFrom_operator_not_false evm I hop
    rw [hleft, hright]
    simp [EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalExpr_transferFrom_allowance_gate_true (evm : EVM.State)
    (I : ExecutionEnv) (hsource : evm.executionEnv.source = I.source)
    (hsenderNe : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ I.source)
    (hop : transferFromOperatorWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "sender") sender)
        (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
        .ok (.bool true) := by
  have hne : ((transferFromSenderValue I : Value) == .address I.source) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromSenderValue, Value.address.injEq] at h
    exact hsenderNe h
  have hleft :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") sender) = .ok (.bool true) := by
    exact evalExpr_transferFrom_sender_ne_env_true evm I hsource hne
  have hright := evalExpr_transferFrom_operator_not_true evm I hop
  rw [evalExpr?]
  rw [hleft, hright]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalExpr_transferFrom_allowance_gate_false_operator (evm : EVM.State)
    (I : ExecutionEnv) (hsource : evm.executionEnv.source = I.source)
    (hsenderNe : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ I.source)
    (hop : transferFromOperatorWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "sender") sender)
        (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
        .ok (.bool false) := by
  have hne : ((transferFromSenderValue I : Value) == .address I.source) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromSenderValue, Value.address.injEq] at h
    exact hsenderNe h
  have hleft :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") sender) = .ok (.bool true) := by
    exact evalExpr_transferFrom_sender_ne_env_true evm I hsource hne
  have hright := evalExpr_transferFrom_operator_not_false evm I hop
  rw [evalExpr?]
  rw [hleft, hright]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalStorageRef_transferFrom_allowance_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (allowanceRef (.var "sender") sender (.var "id")) =
        .ok (transferFromAllowanceEvaledRef evm' I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue,
    evalExpr_transferFrom_sender_currentAllowance, evalExpr_transferFrom_id_currentAllowance,
    transferFromAllowanceEvaledRef, transferFromSenderValue, transferFromIdValue, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_transferFrom_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (allowanceRef (.var "sender") sender (.var "id")) =
        .ok (transferFromAllowanceEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue,
    evalExpr_transferFrom_sender, evalExpr_transferFrom_id, transferFromAllowanceEvaledRef,
    transferFromSenderValue, transferFromIdValue, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transferFrom_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (allowanceRef (.var "sender") sender (.var "id"))) =
        .ok (transferFromCurrentAllowanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromAllowanceSlot evm I))
    (hbase := by simp [allowanceRef, transferFromStore])
    (her := evalStorageRef_transferFrom_allowance evm I)
    (hty := by
      simp [storageTypeAt?, transferFromAllowanceEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromAllowanceEvaledRef,
      transferFromAllowanceSlot])]
  simp [transferFromCurrentAllowanceValue, transferFromCurrentAllowanceWord,
    erc6909StorageLocLoad_uint256]

theorem transferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      .storage (allowanceRef (.var "sender") sender (.var "id"))
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStoreCurrentAllowance evm I },
          transferFromAfterAllowanceState evm I) := by
  simp only [allowanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromAllowanceSlot evm I))
      (hbase := by simp [allowanceRef, transferFromStoreCurrentAllowance, transferFromStore])
      (her := evalStorageRef_transferFrom_allowance_currentAllowance evm evm I)
      (hty := by
        simp [storageTypeAt?, transferFromAllowanceEvaledRef, contract, storageDecls, uint256St,
          storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, transferFromAllowanceEvaledRef, transferFromAllowanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromAfterAllowanceState, transferFromAllowanceSlot]

theorem evalExpr_transferFrom_allowance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_amount]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_allowance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_amount]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_allowance_lt_max_true (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat < UInt256.size - 1) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true) := by
  have hlt' : (transferFromCurrentAllowanceWord evm I).toNat < 2 ^ 256 - 1 := by
    simpa [UInt256.size] using hlt
  simp only [maxUint256Lit, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, maxUint256, UInt256.size]
  omega

theorem evalExpr_transferFrom_allowance_lt_max_false (evm : EVM.State) (I : ExecutionEnv)
    (hge : UInt256.size - 1 ≤ (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false) := by
  have hge' : 2 ^ 256 - 1 ≤ (transferFromCurrentAllowanceWord evm I).toNat := by
    simpa [UInt256.size] using hge
  simp only [maxUint256Lit, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, maxUint256, UInt256.size]
  omega

theorem evalExpr_transferFrom_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .sub (.var "currentAllowance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat
          ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromCurrentAllowanceWord evm I).toNat - (transferFromAmountWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromCurrentAllowanceWord evm I).toNat (transferFromAmountWord I).toNat)
      (transferFromCurrentAllowanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_amount]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalStorageRef_transferFrom_sender_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_sender_fromBalance,
    evalExpr_transferFrom_id_fromBalance,
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem transferFromAssignSenderBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I) .storage (balanceRef (.var "sender") (.var "id"))
      (.int (Int.ofNat (transferFromSenderDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterSenderBalanceState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromSenderBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromStoreFromBalance, transferFromStoreCurrentAllowance,
        transferFromStore])
      (her := evalStorageRef_transferFrom_sender_balance_fromBalance evm
        (transferFromAfterAllowanceState evm I) I)
      (hty := by
        simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
        transferFromSenderBalanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromAfterSenderBalanceState, transferFromSenderBalanceSlot,
    transferFromAfterAllowance_codeOwner]

theorem evalStorageRef_transferFrom_sender_balance_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_sender_currentAllowance, evalExpr_transferFrom_id_currentAllowance,
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      (transferFromAfterAllowanceState evm I) (.storage (balanceRef (.var "sender") (.var "id"))) =
        .ok (transferFromSenderBalanceValue (transferFromAfterAllowanceState evm I) I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromSenderBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromStoreCurrentAllowance, transferFromStore])
    (her := evalStorageRef_transferFrom_sender_balance_currentAllowance evm
      (transferFromAfterAllowanceState evm I) I)
    (hty := by
      simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
      transferFromSenderBalanceSlot])]
  simp [transferFromSenderBalanceValue, transferFromSenderBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromAfterAllowance_codeOwner]

theorem evalExpr_transferFrom_sender_balance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_amount]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_sender_balance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_amount]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_sender_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .sub (.var "fromBalance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromSenderDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat
          ((transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
            (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromSenderDebitWord evm I).toNat =
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
        (transferFromAmountWord I).toNat := by
    unfold transferFromSenderDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_amount]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalStorageRef_transferFrom_receiver_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_receiver_fromBalance,
    evalExpr_transferFrom_id_fromBalance, transferFromReceiverBalanceEvaledRef,
    transferFromReceiverValue, transferFromIdValue, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_receiver_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterSenderBalanceState evm I)
      (.storage (balanceRef (.var "receiver") (.var "id"))) =
        .ok (transferFromReceiverBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromReceiverBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromStoreFromBalance, transferFromStoreCurrentAllowance,
      transferFromStore])
    (her := evalStorageRef_transferFrom_receiver_balance_fromBalance evm
      (transferFromAfterSenderBalanceState evm I) I)
    (hty := by
      simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
      transferFromReceiverBalanceSlot])]
  simp [transferFromReceiverBalanceValue, transferFromReceiverBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromAfterSenderBalance_codeOwner]

theorem evalExpr_transferFrom_receiver_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) =
        .ok (transferFromReceiverCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_amount]
  simp [evalBinaryOp?, transferFromReceiverCreditValue, transferFromReceiverCreditNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromReceiverBalanceWord evm I).toNat + (transferFromAmountWord I).toNat <
          2 ^ 256 := by
      simpa [transferFromReceiverCreditNat, UInt256.size] using hfit
    omega

theorem evalExpr_transferFrom_receiver_credit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromReceiverCreditNat evm I) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) = .revert := by
  have hge : Int.ofNat (transferFromReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_amount]
  simp [evalBinaryOp?, transferFromReceiverBalanceValue, transferFromAmountValue,
    transferFromReceiverCreditValue, transferFromReceiverCreditNat, uint256Int]
  intro _
  simpa [transferFromReceiverCreditNat] using hge

theorem evalStorageRef_transferFrom_receiver_balance_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreToBalance evm I } evm'
      (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_receiver_toBalance,
    evalExpr_transferFrom_id_toBalance, transferFromReceiverBalanceEvaledRef,
    transferFromReceiverValue, transferFromIdValue, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem transferFromAssignReceiverBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterSenderBalanceState evm I) .storage
      (balanceRef (.var "receiver") (.var "id")) (transferFromReceiverCreditValue evm I) =
        .ok ({ contract := contract, locals := transferFromStoreToBalance evm I },
          transferFromPostState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromReceiverBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromStoreToBalance, transferFromStoreFromBalance,
        transferFromStoreCurrentAllowance, transferFromStore])
      (her := evalStorageRef_transferFrom_receiver_balance_toBalance evm
        (transferFromAfterSenderBalanceState evm I) I)
      (hty := by
        simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
        transferFromReceiverBalanceSlot])
  rw [← transferFromReceiverCreditWord_toNat evm I hfit]
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromPostState, transferFromReceiverBalanceSlot,
    transferFromAfterSenderBalance_codeOwner]

theorem evalStorageRef_transferFrom_tail_sender_balance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm'
      (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_sender,
    evalExpr_transferFrom_id, transferFromSenderBalanceEvaledRef, transferFromSenderValue,
    transferFromIdValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_tail_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (balanceRef (.var "sender") (.var "id"))) =
        .ok (transferFromSenderBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromSenderBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromStore])
    (her := evalStorageRef_transferFrom_tail_sender_balance evm evm I)
    (hty := by
      simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
      transferFromSenderBalanceSlot])]
  simp [transferFromSenderBalanceValue, transferFromSenderBalanceWord,
    erc6909StorageLocLoad_uint256]

theorem evalStorageRef_transferFrom_tail_sender_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm' (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_sender_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_sender I),
    evalExpr_transferFrom_tail_id_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_id I),
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_transferFrom_tail_sender_balance_fromBalance_of_get
    (locals : Store) (evm evm' : EVM.State) (I : ExecutionEnv)
    (hsender : locals.get? "sender" = some (transferFromSenderValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I)) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm' (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_sender_fromBalance locals evm evm' I hsender,
    evalExpr_transferFrom_tail_id_fromBalance locals evm evm' I hid,
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem transferFromTailAssignSenderBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm .storage (balanceRef (.var "sender") (.var "id"))
      (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I },
          transferFromTailAfterSenderBalanceState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromSenderBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, transferFromStore])
      (her := evalStorageRef_transferFrom_tail_sender_balance_fromBalance evm evm I)
      (hty := by
        simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
        transferFromSenderBalanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailAfterSenderBalanceState, transferFromSenderBalanceSlot]

theorem transferFromTailAssignSenderBalance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : locals.get? "sender" = some (transferFromSenderValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm .storage (balanceRef (.var "sender") (.var "id"))
      (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromTailStoreFromBalance locals evm I },
          transferFromTailAfterSenderBalanceState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromSenderBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, hbase])
      (her := evalStorageRef_transferFrom_tail_sender_balance_fromBalance_of_get
        locals evm evm I hsender hid)
      (hty := by
        simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
        transferFromSenderBalanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailAfterSenderBalanceState, transferFromSenderBalanceSlot]

theorem evalExpr_transferFrom_tail_sender_balance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : locals.get? "sender" = some (transferFromSenderValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals) :
    evalExpr? config
      { contract := contract, locals := locals } evm
      (.storage (balanceRef (.var "sender") (.var "id"))) =
        .ok (transferFromSenderBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromSenderBalanceSlot I))
    (hbase := by simp [balanceRef, hbase])
    (her := by
      change evalStorageRef config { contract := contract, locals := locals } evm
        (balanceRef (.var "sender") (.var "id")) =
          .ok (transferFromSenderBalanceEvaledRef I)
      simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceRef, evalExpr?,
        EvalResult.bind, EvalResult.ofOption, bind, pure]
      rw [hsender, hid]
      simp [transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
        valueToKey?])
    (hty := by
      simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
      transferFromSenderBalanceSlot])]
  simp [transferFromSenderBalanceValue, transferFromSenderBalanceWord,
    erc6909StorageLocLoad_uint256]

theorem evalExpr_transferFrom_tail_sender_balance_ge_true (evm : EVM.State)
    (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_tail_sender_balance_ge_true_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_tail_sender_balance_ge_false (evm : EVM.State)
    (I : ExecutionEnv)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_tail_sender_balance_ge_false_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_tail_sender_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm (.binary .sub (.var "fromBalance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSenderBalanceWord evm I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat ((transferFromSenderBalanceWord evm I).toNat -
          (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromTailSenderDebitWord evm I).toNat =
      (transferFromSenderBalanceWord evm I).toNat - (transferFromAmountWord I).toNat := by
    unfold transferFromTailSenderDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromSenderBalanceWord evm I).toNat (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalExpr_transferFrom_tail_sender_debit_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm (.binary .sub (.var "fromBalance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSenderBalanceWord evm I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat ((transferFromSenderBalanceWord evm I).toNat -
          (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromTailSenderDebitWord evm I).toNat =
      (transferFromSenderBalanceWord evm I).toNat - (transferFromAmountWord I).toNat := by
    unfold transferFromTailSenderDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromSenderBalanceWord evm I).toNat (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalStorageRef_transferFrom_tail_receiver_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_receiver I),
    evalExpr_transferFrom_tail_id_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_id I),
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_transferFrom_tail_receiver_balance_fromBalance_of_get
    (locals : Store) (evm evm' : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I)) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_fromBalance locals evm evm' I hreceiver,
    evalExpr_transferFrom_tail_id_fromBalance locals evm evm' I hid,
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_tail_receiver_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (.storage (balanceRef (.var "receiver") (.var "id"))) =
        .ok (transferFromTailReceiverBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromReceiverBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, transferFromStore])
    (her := evalStorageRef_transferFrom_tail_receiver_balance_fromBalance evm
      (transferFromTailAfterSenderBalanceState evm I) I)
    (hty := by
      simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
      transferFromReceiverBalanceSlot])]
  simp [transferFromTailReceiverBalanceValue, transferFromTailReceiverBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromTailAfterSenderBalance_codeOwner]

theorem evalExpr_transferFrom_tail_receiver_balance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (.storage (balanceRef (.var "receiver") (.var "id"))) =
        .ok (transferFromTailReceiverBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromReceiverBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, hbase])
    (her := evalStorageRef_transferFrom_tail_receiver_balance_fromBalance_of_get locals evm
      (transferFromTailAfterSenderBalanceState evm I) I hreceiver hid)
    (hty := by
      simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
      transferFromReceiverBalanceSlot])]
  simp [transferFromTailReceiverBalanceValue, transferFromTailReceiverBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromTailAfterSenderBalance_codeOwner]

theorem evalExpr_transferFrom_tail_receiver_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) =
        .ok (transferFromTailReceiverCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?, transferFromTailReceiverCreditValue,
    transferFromTailReceiverCreditNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromTailReceiverBalanceWord evm I).toNat +
            (transferFromAmountWord I).toNat < 2 ^ 256 := by
      simpa [transferFromTailReceiverCreditNat, UInt256.size] using hfit
    omega

theorem evalExpr_transferFrom_tail_receiver_credit_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) =
        .ok (transferFromTailReceiverCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?, transferFromTailReceiverCreditValue,
    transferFromTailReceiverCreditNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromTailReceiverBalanceWord evm I).toNat +
            (transferFromAmountWord I).toNat < 2 ^ 256 := by
      simpa [transferFromTailReceiverCreditNat, UInt256.size] using hfit
    omega

theorem evalExpr_transferFrom_tail_receiver_credit_revert (evm : EVM.State)
    (I : ExecutionEnv) (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) = .revert := by
  have hge : Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?, transferFromTailReceiverBalanceValue, transferFromAmountValue,
    transferFromTailReceiverCreditValue, transferFromTailReceiverCreditNat, uint256Int]
  intro _
  simpa [transferFromTailReceiverCreditNat] using hge

theorem evalExpr_transferFrom_tail_receiver_credit_revert_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) = .revert := by
  have hge : Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?, transferFromTailReceiverBalanceValue, transferFromAmountValue,
    transferFromTailReceiverCreditValue, transferFromTailReceiverCreditNat, uint256Int]
  intro _
  simpa [transferFromTailReceiverCreditNat] using hge

theorem evalStorageRef_transferFrom_tail_receiver_balance_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_toBalance (transferFromStore I) evm evm' I
      (transferFromStore_receiver I),
    evalExpr_transferFrom_tail_id_toBalance (transferFromStore I) evm evm' I
      (transferFromStore_id I),
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_transferFrom_tail_receiver_balance_toBalance_of_get
    (locals : Store) (evm evm' : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I)) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_toBalance locals evm evm' I hreceiver,
    evalExpr_transferFrom_tail_id_toBalance locals evm evm' I hid,
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem transferFromTailAssignReceiverBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I) .storage
      (balanceRef (.var "receiver") (.var "id"))
      (transferFromTailReceiverCreditValue evm I) =
        .ok ({ contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I },
          transferFromTailPostState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromReceiverBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromTailStoreToBalance,
        transferFromTailStoreFromBalance, transferFromStore])
      (her := evalStorageRef_transferFrom_tail_receiver_balance_toBalance evm
        (transferFromTailAfterSenderBalanceState evm I) I)
      (hty := by
        simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
        transferFromReceiverBalanceSlot])
  rw [← transferFromTailReceiverCreditWord_toNat evm I hfit]
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailPostState, transferFromReceiverBalanceSlot,
    transferFromTailAfterSenderBalance_codeOwner]

theorem transferFromTailAssignReceiverBalance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I) .storage
      (balanceRef (.var "receiver") (.var "id"))
      (transferFromTailReceiverCreditValue evm I) =
        .ok ({ contract := contract, locals := transferFromTailStoreToBalance locals evm I },
          transferFromTailPostState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromReceiverBalanceSlot I))
      (hbase := by
        simp [balanceRef, transferFromTailStoreToBalance, transferFromTailStoreFromBalance,
          hbase])
      (her := evalStorageRef_transferFrom_tail_receiver_balance_toBalance_of_get locals evm
        (transferFromTailAfterSenderBalanceState evm I) I hreceiver hid)
      (hty := by
        simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
        transferFromReceiverBalanceSlot])
  rw [← transferFromTailReceiverCreditWord_toNat evm I hfit]
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailPostState, transferFromReceiverBalanceSlot,
    transferFromTailAfterSenderBalance_codeOwner]



end OpenZeppelinBench.ERC6909
