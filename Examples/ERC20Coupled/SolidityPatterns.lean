import Examples.ERC20Coupled.Standalone.TransferFromBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace ERC20Coupled

open ERC20Standalone

theorem transferSourceAfterFromBalanceReturns (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferStoreFromBalance evm I }
      evm
      [ .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return (.boolLit true) ]
      (ExecResult.returned
        { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
        (transferPostState evm I) (some (.bool true))) := by
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough)
      (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_newToBalance evm I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_newToBalance_var evm I)
      (transferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem transferSourceAfterFromBalanceReverts_insufficient (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferStoreFromBalance evm I }
      evm
      [ .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return (.boolLit true) ] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_require_from_false evm I hlt))

theorem transferSourceAfterFromBalanceReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferStoreFromBalance evm I }
      evm
      [ .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return (.boolLit true) ] .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough)
      (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_transfer_newToBalance_revert evm I hover))

theorem transferSourceBlockReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferStore I } evm
      transferTransition.body
      (ExecResult.returned
        { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
        (transferPostState evm I) (some (.bool true))) := by
  change ExecBlock erc20Config { contract := erc20Contract, locals := transferStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ]
    (ExecResult.returned
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
      (transferPostState evm I) (some (.bool true)))
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough)
      (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_newToBalance evm I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_newToBalance_var evm I)
      (transferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem transferSourceBlockReverts_insufficient (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferStore I } evm
      transferTransition.body .reverted := by
  change ExecBlock erc20Config { contract := erc20Contract, locals := transferStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ] .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_require_from_false evm I hlt))

theorem transferSourceBlockReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferStore I } evm
      transferTransition.body .reverted := by
  change ExecBlock erc20Config { contract := erc20Contract, locals := transferStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ] .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough)
      (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_transfer_newToBalance_revert evm I hover))

theorem transferFromSourceBlockReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat)
    (hfit : transferFromNewToNat evm I < UInt256.size) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      transferFromTransition.body
      (ExecResult.returned
        { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
        (transferFromPostState evm I) (some (.bool true))) := by
  change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256)
        (.storage (allowanceRef (.var "from") sender)),
      .require (.binary .ge (.var "currentAllowance") (.var "value")),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (allowanceRef (.var "from") sender)
        (.binary .sub (.var "currentAllowance") (.var "value")),
      .assign (balanceOfRef (.var "from"))
        (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ]
    (ExecResult.returned
      { contract := erc20Contract, locals := transferFromStoreNewToBalance evm I }
      (transferFromPostState evm I) (some (.bool true)))
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I hallowance)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowance)
      (transferFromAssignAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_balance_debit evm (transferFromAfterAllowanceState evm I) I
        hbalance)
      (transferFromAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transferFrom_newToBalance evm I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_newToBalance_var evm I)
      (transferFromAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem transferFromSourceBlockReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      transferFromTransition.body .reverted := by
  change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256)
        (.storage (allowanceRef (.var "from") sender)),
      .require (.binary .ge (.var "currentAllowance") (.var "value")),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (allowanceRef (.var "from") sender)
        (.binary .sub (.var "currentAllowance") (.var "value")),
      .assign (balanceOfRef (.var "from"))
        (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ] .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_require_allowance_false evm I hlt))

theorem transferFromSourceBlockReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hlt : (transferFromFromBalanceWord evm I).toNat <
      (transferFromValueWord I).toNat) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      transferFromTransition.body .reverted := by
  change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256)
        (.storage (allowanceRef (.var "from") sender)),
      .require (.binary .ge (.var "currentAllowance") (.var "value")),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (allowanceRef (.var "from") sender)
        (.binary .sub (.var "currentAllowance") (.var "value")),
      .assign (balanceOfRef (.var "from"))
        (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ] .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I hallowance)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_require_from_false evm I hlt))

theorem transferFromSourceBlockReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromNewToNat evm I) :
    ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
      transferFromTransition.body .reverted := by
  change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "currentAllowance" (some uint256)
        (.storage (allowanceRef (.var "from") sender)),
      .require (.binary .ge (.var "currentAllowance") (.var "value")),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (allowanceRef (.var "from") sender)
        (.binary .sub (.var "currentAllowance") (.var "value")),
      .assign (balanceOfRef (.var "from"))
        (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ] .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true evm I hallowance)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_from_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true evm I hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowance)
      (transferFromAssignAllowance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_balance_debit evm (transferFromAfterAllowanceState evm I) I
        hbalance)
      (transferFromAssignFrom evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_transferFrom_newToBalance_revert evm I hover))

end ERC20Coupled
