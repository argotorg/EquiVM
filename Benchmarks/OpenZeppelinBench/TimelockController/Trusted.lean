import Benchmarks.OpenZeppelinBench.TimelockController.Common

/-!
# OpenZeppelin TimelockController trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
They are part of the accepted trusted base (selector bytes of each function). Values verified by
`cast`/keccak against the canonical ABI signatures.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.TimelockController

/-- `keccak("CANCELLER_ROLE()")[0:4] = 0xb08e51c0`. -/
axiom cancellerRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cancellerRoleTransition))).extract 0 4 =
      tlcSelBytes 0

/-- `keccak("cancel(bytes32)")[0:4] = 0xc4d252f5`. -/
axiom cancelSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cancelTransition))).extract 0 4 =
      tlcSelBytes 1

/-- `keccak("DEFAULT_ADMIN_ROLE()")[0:4] = 0xa217fddf`. -/
axiom defaultAdminRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr defaultAdminRoleTransition))).extract 0 4 =
      tlcSelBytes 2

/-- `keccak("executeBatch(address[],uint256[],bytes[],bytes32,bytes32)")[0:4] = 0xe38335e5`. -/
axiom executeBatchSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr executeBatchTransition))).extract 0 4 =
      tlcSelBytes 3

/-- `keccak("execute(address,uint256,bytes,bytes32,bytes32)")[0:4] = 0x134008d3`. -/
axiom executeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr executeTransition))).extract 0 4 =
      tlcSelBytes 4

/-- `keccak("EXECUTOR_ROLE()")[0:4] = 0x07bd0265`. -/
axiom executorRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr executorRoleTransition))).extract 0 4 =
      tlcSelBytes 5

/-- `keccak("getMinDelay()")[0:4] = 0xf27a0c92`. -/
axiom getMinDelaySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getMinDelayTransition))).extract 0 4 =
      tlcSelBytes 6

/-- `keccak("getOperationState(bytes32)")[0:4] = 0x7958004c`. -/
axiom getOperationStateSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getOperationStateTransition))).extract 0 4 =
      tlcSelBytes 7

/-- `keccak("getRoleAdmin(bytes32)")[0:4] = 0x248a9ca3`. -/
axiom getRoleAdminSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getRoleAdminTransition))).extract 0 4 =
      tlcSelBytes 8

/-- `keccak("getTimestamp(bytes32)")[0:4] = 0xd45c4435`. -/
axiom getTimestampSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getTimestampTransition))).extract 0 4 =
      tlcSelBytes 9

/-- `keccak("grantRole(bytes32,address)")[0:4] = 0x2f2ff15d`. -/
axiom grantRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr grantRoleTransition))).extract 0 4 =
      tlcSelBytes 10

/-- `keccak("hasRole(bytes32,address)")[0:4] = 0x91d14854`. -/
axiom hasRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr hasRoleTransition))).extract 0 4 =
      tlcSelBytes 11

/-- `keccak("hashOperationBatch(address[],uint256[],bytes[],bytes32,bytes32)")[0:4] = 0xb1c5f427`. -/
axiom hashOperationBatchSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr hashOperationBatchTransition))).extract 0 4 =
      tlcSelBytes 12

/-- `keccak("hashOperation(address,uint256,bytes,bytes32,bytes32)")[0:4] = 0x8065657f`. -/
axiom hashOperationSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr hashOperationTransition))).extract 0 4 =
      tlcSelBytes 13

/-- `keccak("isOperationDone(bytes32)")[0:4] = 0x2ab0f529`. -/
axiom isOperationDoneSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr isOperationDoneTransition))).extract 0 4 =
      tlcSelBytes 14

/-- `keccak("isOperationPending(bytes32)")[0:4] = 0x584b153e`. -/
axiom isOperationPendingSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr isOperationPendingTransition))).extract 0 4 =
      tlcSelBytes 15

/-- `keccak("isOperationReady(bytes32)")[0:4] = 0x13bc9f20`. -/
axiom isOperationReadySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr isOperationReadyTransition))).extract 0 4 =
      tlcSelBytes 16

/-- `keccak("isOperation(bytes32)")[0:4] = 0x31d50750`. -/
axiom isOperationSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr isOperationTransition))).extract 0 4 =
      tlcSelBytes 17

/-- `keccak("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)")[0:4] = 0xbc197c81`. -/
axiom onERC1155BatchReceivedSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr onERC1155BatchReceivedTransition))).extract 0 4 =
      tlcSelBytes 18

/-- `keccak("onERC1155Received(address,address,uint256,uint256,bytes)")[0:4] = 0xf23a6e61`. -/
axiom onERC1155ReceivedSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr onERC1155ReceivedTransition))).extract 0 4 =
      tlcSelBytes 19

/-- `keccak("onERC721Received(address,address,uint256,bytes)")[0:4] = 0x150b7a02`. -/
axiom onERC721ReceivedSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr onERC721ReceivedTransition))).extract 0 4 =
      tlcSelBytes 20

/-- `keccak("PROPOSER_ROLE()")[0:4] = 0x8f61f4f5`. -/
axiom proposerRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr proposerRoleTransition))).extract 0 4 =
      tlcSelBytes 21

/-- `keccak("renounceRole(bytes32,address)")[0:4] = 0x36568abe`. -/
axiom renounceRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr renounceRoleTransition))).extract 0 4 =
      tlcSelBytes 22

/-- `keccak("revokeRole(bytes32,address)")[0:4] = 0xd547741f`. -/
axiom revokeRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr revokeRoleTransition))).extract 0 4 =
      tlcSelBytes 23

/-- `keccak("scheduleBatch(address[],uint256[],bytes[],bytes32,bytes32,uint256)")[0:4] = 0x8f2a0bb0`. -/
axiom scheduleBatchSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr scheduleBatchTransition))).extract 0 4 =
      tlcSelBytes 24

/-- `keccak("schedule(address,uint256,bytes,bytes32,bytes32,uint256)")[0:4] = 0x01d5062a`. -/
axiom scheduleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr scheduleTransition))).extract 0 4 =
      tlcSelBytes 25

/-- `keccak("supportsInterface(bytes4)")[0:4] = 0x01ffc9a7`. -/
axiom supportsInterfaceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr supportsInterfaceTransition))).extract 0 4 =
      tlcSelBytes 26

/-- `keccak("updateDelay(uint256)")[0:4] = 0x64d62353`. -/
axiom updateDelaySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr updateDelayTransition))).extract 0 4 =
      tlcSelBytes 27

end OpenZeppelinBench.TimelockController
