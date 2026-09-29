import Benchmarks.Scaffolds.TimelockController.Common

/-!
# OpenZeppelin TimelockController selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
Each proof evaluates the canonical ABI signature's Keccak selector.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.TimelockController

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("CANCELLER_ROLE()")[0:4] = 0xb08e51c0`. -/
theorem cancellerRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cancellerRoleTransition))).extract 0 4 =
      tlcSelBytes 0 := by decide +kernel

/-- `keccak("cancel(bytes32)")[0:4] = 0xc4d252f5`. -/
theorem cancelSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cancelTransition))).extract 0 4 =
      tlcSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, cancelTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("DEFAULT_ADMIN_ROLE()")[0:4] = 0xa217fddf`. -/
theorem defaultAdminRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr defaultAdminRoleTransition))).extract 0 4 =
      tlcSelBytes 2 := by decide +kernel

/-- `keccak("executeBatch(address[],uint256[],bytes[],bytes32,bytes32)")[0:4] = 0xe38335e5`. -/
theorem executeBatchSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr executeBatchTransition))).extract 0 4 =
      tlcSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, executeBatchTransition, addrArray, addr, uint256Array, uint256, uint256Int, bytesArray, bytesTy, bytes32, bytes32Width]; decide +kernel

/-- `keccak("execute(address,uint256,bytes,bytes32,bytes32)")[0:4] = 0x134008d3`. -/
theorem executeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr executeTransition))).extract 0 4 =
      tlcSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, executeTransition, addr, uint256, uint256Int, bytesTy, bytes32, bytes32Width]; decide +kernel

/-- `keccak("EXECUTOR_ROLE()")[0:4] = 0x07bd0265`. -/
theorem executorRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr executorRoleTransition))).extract 0 4 =
      tlcSelBytes 5 := by decide +kernel

/-- `keccak("getMinDelay()")[0:4] = 0xf27a0c92`. -/
theorem getMinDelaySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getMinDelayTransition))).extract 0 4 =
      tlcSelBytes 6 := by decide +kernel

/-- `keccak("getOperationState(bytes32)")[0:4] = 0x7958004c`. -/
theorem getOperationStateSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getOperationStateTransition))).extract 0 4 =
      tlcSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, getOperationStateTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("getRoleAdmin(bytes32)")[0:4] = 0x248a9ca3`. -/
theorem getRoleAdminSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getRoleAdminTransition))).extract 0 4 =
      tlcSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, getRoleAdminTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("getTimestamp(bytes32)")[0:4] = 0xd45c4435`. -/
theorem getTimestampSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getTimestampTransition))).extract 0 4 =
      tlcSelBytes 9 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, getTimestampTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("grantRole(bytes32,address)")[0:4] = 0x2f2ff15d`. -/
theorem grantRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr grantRoleTransition))).extract 0 4 =
      tlcSelBytes 10 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, grantRoleTransition, bytes32, bytes32Width, addr]; decide +kernel

/-- `keccak("hasRole(bytes32,address)")[0:4] = 0x91d14854`. -/
theorem hasRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr hasRoleTransition))).extract 0 4 =
      tlcSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, hasRoleTransition, bytes32, bytes32Width, addr]; decide +kernel

/-- `keccak("hashOperationBatch(address[],uint256[],bytes[],bytes32,bytes32)")[0:4] = 0xb1c5f427`. -/
theorem hashOperationBatchSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr hashOperationBatchTransition))).extract 0 4 =
      tlcSelBytes 12 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, hashOperationBatchTransition, addrArray, addr, uint256Array, uint256, uint256Int, bytesArray, bytesTy, bytes32, bytes32Width]; decide +kernel

/-- `keccak("hashOperation(address,uint256,bytes,bytes32,bytes32)")[0:4] = 0x8065657f`. -/
theorem hashOperationSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr hashOperationTransition))).extract 0 4 =
      tlcSelBytes 13 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, hashOperationTransition, addr, uint256, uint256Int, bytesTy, bytes32, bytes32Width]; decide +kernel

/-- `keccak("isOperationDone(bytes32)")[0:4] = 0x2ab0f529`. -/
theorem isOperationDoneSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr isOperationDoneTransition))).extract 0 4 =
      tlcSelBytes 14 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, isOperationDoneTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("isOperationPending(bytes32)")[0:4] = 0x584b153e`. -/
theorem isOperationPendingSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr isOperationPendingTransition))).extract 0 4 =
      tlcSelBytes 15 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, isOperationPendingTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("isOperationReady(bytes32)")[0:4] = 0x13bc9f20`. -/
theorem isOperationReadySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr isOperationReadyTransition))).extract 0 4 =
      tlcSelBytes 16 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, isOperationReadyTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("isOperation(bytes32)")[0:4] = 0x31d50750`. -/
theorem isOperationSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr isOperationTransition))).extract 0 4 =
      tlcSelBytes 17 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, isOperationTransition, bytes32, bytes32Width]; decide +kernel

/-- `keccak("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)")[0:4] = 0xbc197c81`. -/
theorem onERC1155BatchReceivedSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr onERC1155BatchReceivedTransition))).extract 0 4 =
      tlcSelBytes 18 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, onERC1155BatchReceivedTransition, addr, uint256Array, uint256, uint256Int, bytesTy]; decide +kernel

/-- `keccak("onERC1155Received(address,address,uint256,uint256,bytes)")[0:4] = 0xf23a6e61`. -/
theorem onERC1155ReceivedSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr onERC1155ReceivedTransition))).extract 0 4 =
      tlcSelBytes 19 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, onERC1155ReceivedTransition, addr, uint256, uint256Int, bytesTy]; decide +kernel

/-- `keccak("onERC721Received(address,address,uint256,bytes)")[0:4] = 0x150b7a02`. -/
theorem onERC721ReceivedSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr onERC721ReceivedTransition))).extract 0 4 =
      tlcSelBytes 20 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, onERC721ReceivedTransition, addr, uint256, uint256Int, bytesTy]; decide +kernel

/-- `keccak("PROPOSER_ROLE()")[0:4] = 0x8f61f4f5`. -/
theorem proposerRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr proposerRoleTransition))).extract 0 4 =
      tlcSelBytes 21 := by decide +kernel

/-- `keccak("renounceRole(bytes32,address)")[0:4] = 0x36568abe`. -/
theorem renounceRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr renounceRoleTransition))).extract 0 4 =
      tlcSelBytes 22 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, renounceRoleTransition, bytes32, bytes32Width, addr]; decide +kernel

/-- `keccak("revokeRole(bytes32,address)")[0:4] = 0xd547741f`. -/
theorem revokeRoleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr revokeRoleTransition))).extract 0 4 =
      tlcSelBytes 23 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, revokeRoleTransition, bytes32, bytes32Width, addr]; decide +kernel

/-- `keccak("scheduleBatch(address[],uint256[],bytes[],bytes32,bytes32,uint256)")[0:4] = 0x8f2a0bb0`. -/
theorem scheduleBatchSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr scheduleBatchTransition))).extract 0 4 =
      tlcSelBytes 24 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, scheduleBatchTransition, addrArray, addr, uint256Array, uint256, uint256Int, bytesArray, bytesTy, bytes32, bytes32Width]; decide +kernel

/-- `keccak("schedule(address,uint256,bytes,bytes32,bytes32,uint256)")[0:4] = 0x01d5062a`. -/
theorem scheduleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr scheduleTransition))).extract 0 4 =
      tlcSelBytes 25 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, scheduleTransition, addr, uint256, uint256Int, bytesTy, bytes32, bytes32Width]; decide +kernel

/-- `keccak("supportsInterface(bytes4)")[0:4] = 0x01ffc9a7`. -/
theorem supportsInterfaceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr supportsInterfaceTransition))).extract 0 4 =
      tlcSelBytes 26 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, supportsInterfaceTransition, bytes4, bytes4Width]; decide +kernel

/-- `keccak("updateDelay(uint256)")[0:4] = 0x64d62353`. -/
theorem updateDelaySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr updateDelayTransition))).extract 0 4 =
      tlcSelBytes 27 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, updateDelayTransition, uint256, uint256Int]; decide +kernel

end OpenZeppelinBench.TimelockController
