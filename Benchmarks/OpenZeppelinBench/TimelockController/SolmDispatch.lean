import Benchmarks.OpenZeppelinBench.TimelockController.Trusted

/-!
# OpenZeppelin TimelockController Solm dispatch routing facts

For each named selector, `selectorDispatchMsg contract I.calldata = some <Fn>Transition`.  These are
consumed by the per-function refinement bridges in `Routines.lean` (TimelockController has
`contract.receive = some …`, so the library `dispatchMsg`-based bridges do not apply and we route on
`selectorDispatchMsg` directly).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace OpenZeppelinBench.TimelockController

attribute [local simp]
  cancellerRoleSelectorBytes cancelSelectorBytes defaultAdminRoleSelectorBytes
  executeBatchSelectorBytes executeSelectorBytes executorRoleSelectorBytes
  getMinDelaySelectorBytes getOperationStateSelectorBytes getRoleAdminSelectorBytes
  getTimestampSelectorBytes grantRoleSelectorBytes hasRoleSelectorBytes
  hashOperationBatchSelectorBytes hashOperationSelectorBytes isOperationDoneSelectorBytes
  isOperationPendingSelectorBytes isOperationReadySelectorBytes isOperationSelectorBytes
  onERC1155BatchReceivedSelectorBytes onERC1155ReceivedSelectorBytes onERC721ReceivedSelectorBytes
  proposerRoleSelectorBytes renounceRoleSelectorBytes revokeRoleSelectorBytes
  scheduleBatchSelectorBytes scheduleSelectorBytes supportsInterfaceSelectorBytes
  updateDelaySelectorBytes

theorem tlcSelectorDispatchCancellerRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 0)) :
    selectorDispatchMsg contract I.calldata = some cancellerRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchCancel {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 1)) :
    selectorDispatchMsg contract I.calldata = some cancelTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchDefaultAdminRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 2)) :
    selectorDispatchMsg contract I.calldata = some defaultAdminRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchExecuteBatch {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 3)) :
    selectorDispatchMsg contract I.calldata = some executeBatchTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchExecute {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 4)) :
    selectorDispatchMsg contract I.calldata = some executeTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchExecutorRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 5)) :
    selectorDispatchMsg contract I.calldata = some executorRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchGetMinDelay {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 6)) :
    selectorDispatchMsg contract I.calldata = some getMinDelayTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchGetOperationState {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 7)) :
    selectorDispatchMsg contract I.calldata = some getOperationStateTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchGetRoleAdmin {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 8)) :
    selectorDispatchMsg contract I.calldata = some getRoleAdminTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchGetTimestamp {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 9)) :
    selectorDispatchMsg contract I.calldata = some getTimestampTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchGrantRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 10)) :
    selectorDispatchMsg contract I.calldata = some grantRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchHasRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 11)) :
    selectorDispatchMsg contract I.calldata = some hasRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchHashOperationBatch {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 12)) :
    selectorDispatchMsg contract I.calldata = some hashOperationBatchTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchHashOperation {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 13)) :
    selectorDispatchMsg contract I.calldata = some hashOperationTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchIsOperationDone {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 14)) :
    selectorDispatchMsg contract I.calldata = some isOperationDoneTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchIsOperationPending {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 15)) :
    selectorDispatchMsg contract I.calldata = some isOperationPendingTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchIsOperationReady {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 16)) :
    selectorDispatchMsg contract I.calldata = some isOperationReadyTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchIsOperation {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 17)) :
    selectorDispatchMsg contract I.calldata = some isOperationTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 17 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchOnERC1155BatchReceived {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 18)) :
    selectorDispatchMsg contract I.calldata = some onERC1155BatchReceivedTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 18 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchOnERC1155Received {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 19)) :
    selectorDispatchMsg contract I.calldata = some onERC1155ReceivedTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 19 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchOnERC721Received {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 20)) :
    selectorDispatchMsg contract I.calldata = some onERC721ReceivedTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 20 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchProposerRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 21)) :
    selectorDispatchMsg contract I.calldata = some proposerRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 21 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchRenounceRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 22)) :
    selectorDispatchMsg contract I.calldata = some renounceRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 22 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchRevokeRole {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 23)) :
    selectorDispatchMsg contract I.calldata = some revokeRoleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 23 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchScheduleBatch {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 24)) :
    selectorDispatchMsg contract I.calldata = some scheduleBatchTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 24 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchSchedule {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 25)) :
    selectorDispatchMsg contract I.calldata = some scheduleTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 25 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchSupportsInterface {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 26)) :
    selectorDispatchMsg contract I.calldata = some supportsInterfaceTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 26 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

theorem tlcSelectorDispatchUpdateDelay {I : ExecutionEnv} (hsel : selIs I (tlcSelBytes 27)) :
    selectorDispatchMsg contract I.calldata = some updateDelayTransition := by
  have hcd : I.calldata.extract 0 4 = tlcSelBytes 27 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp [contract, dispatchList, selectorOf, hcd]; native_decide

end OpenZeppelinBench.TimelockController
