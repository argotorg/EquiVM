import Benchmarks.Safe.Common
import Solm.Dispatch

/-!
# Safe trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by Solm dispatch. These facts connect
the canonical ABI signatures in `Spec.lean` with the selector constants used by the runtime proof.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Safe

/-- `keccak("VERSION()")[0:4] = 0xffa1ad74`. -/
axiom safeVersionSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr versionTransition))).extract 0 4 =
      safeSelBytes 0

/-- `keccak("addOwnerWithThreshold(address,uint256)")[0:4] = 0x0d582f13`. -/
axiom safeAddOwnerWithThresholdSelectorBytes :
    (ffi.KEC (String.toByteArray
      (transitionSigStr addownerwiththresholdTransition))).extract 0 4 =
      safeSelBytes 1

/-- `keccak("approveHash(bytes32)")[0:4] = 0xd4d9bdcd`. -/
axiom safeApproveHashSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr approvehashTransition))).extract 0 4 =
      safeSelBytes 2

/-- `keccak("approvedHashes(address,bytes32)")[0:4] = 0x7d832974`. -/
axiom safeApprovedHashesSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr approvedhashesTransition))).extract 0 4 =
      safeSelBytes 3

/-- `keccak("changeThreshold(uint256)")[0:4] = 0x694e80c3`. -/
axiom safeChangeThresholdSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr changethresholdTransition))).extract 0 4 =
      safeSelBytes 4

/-- `keccak("checkNSignatures(bytes32,bytes,bytes,uint256)")[0:4] = 0x12fb68e0`. -/
axiom safeCheckNSignaturesSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr checknsignaturesTransition))).extract 0 4 =
      safeSelBytes 5

/-- `keccak("checkNSignatures(address,bytes32,bytes,uint256)")[0:4] = 0x1fcac7f3`. -/
axiom safeCheckNSignaturesWithExecutorSelectorBytes :
    (ffi.KEC (String.toByteArray
      (transitionSigStr checknsignaturesAddressBytes32BytesUint256Transition))).extract 0 4 =
      safeSelBytes 6

/-- `keccak("checkSignatures(bytes32,bytes,bytes)")[0:4] = 0x934f3a11`. -/
axiom safeCheckSignaturesSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr checksignaturesTransition))).extract 0 4 =
      safeSelBytes 7

/-- `keccak("checkSignatures(address,bytes32,bytes)")[0:4] = 0xf855438b`. -/
axiom safeCheckSignaturesWithExecutorSelectorBytes :
    (ffi.KEC (String.toByteArray
      (transitionSigStr checksignaturesAddressBytes32BytesTransition))).extract 0 4 =
      safeSelBytes 8

/-- `keccak("disableModule(address,address)")[0:4] = 0xe009cfde`. -/
axiom safeDisableModuleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr disablemoduleTransition))).extract 0 4 =
      safeSelBytes 9

/-- `keccak("domainSeparator()")[0:4] = 0xf698da25`. -/
axiom safeDomainSeparatorSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr domainseparatorTransition))).extract 0 4 =
      safeSelBytes 10

/-- `keccak("enableModule(address)")[0:4] = 0x610b5925`. -/
axiom safeEnableModuleSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr enablemoduleTransition))).extract 0 4 =
      safeSelBytes 11

/-- Selector for `execTransaction`. -/
axiom safeExecTransactionSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr exectransactionTransition))).extract 0 4 =
      safeSelBytes 12

/-- `keccak("execTransactionFromModule(address,uint256,bytes,uint8)")[0:4] = 0x468721a7`. -/
axiom safeExecTransactionFromModuleSelectorBytes :
    (ffi.KEC (String.toByteArray
      (transitionSigStr exectransactionfrommoduleTransition))).extract 0 4 =
      safeSelBytes 13

/-- Selector for `execTransactionFromModuleReturnData`. -/
axiom safeExecTransactionFromModuleReturnDataSelectorBytes :
    (ffi.KEC (String.toByteArray
      (transitionSigStr exectransactionfrommodulereturndataTransition))).extract 0 4 =
      safeSelBytes 14

/-- `keccak("getModulesPaginated(address,uint256)")[0:4] = 0xcc2f8452`. -/
axiom safeGetModulesPaginatedSelectorBytes :
    (ffi.KEC (String.toByteArray
      (transitionSigStr getmodulespaginatedTransition))).extract 0 4 =
      safeSelBytes 15

/-- `keccak("getOwners()")[0:4] = 0xa0e67e2b`. -/
axiom safeGetOwnersSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getownersTransition))).extract 0 4 =
      safeSelBytes 16

/-- `keccak("getStorageAt(uint256,uint256)")[0:4] = 0x5624b25b`. -/
axiom safeGetStorageAtSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getstorageatTransition))).extract 0 4 =
      safeSelBytes 17

/-- `keccak("getThreshold()")[0:4] = 0xe75235b8`. -/
axiom safeGetThresholdSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getthresholdTransition))).extract 0 4 =
      safeSelBytes 18

/-- Selector for `getTransactionHash`. -/
axiom safeGetTransactionHashSelectorBytes :
    (ffi.KEC (String.toByteArray
      (transitionSigStr gettransactionhashTransition))).extract 0 4 =
      safeSelBytes 19

/-- `keccak("isModuleEnabled(address)")[0:4] = 0x2d9ad53d`. -/
axiom safeIsModuleEnabledSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ismoduleenabledTransition))).extract 0 4 =
      safeSelBytes 20

/-- `keccak("isOwner(address)")[0:4] = 0x2f54bf6e`. -/
axiom safeIsOwnerSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr isownerTransition))).extract 0 4 =
      safeSelBytes 21

/-- `keccak("nonce()")[0:4] = 0xaffed0e0`. -/
axiom safeNonceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr nonceTransition))).extract 0 4 =
      safeSelBytes 22

/-- `keccak("removeOwner(address,address,uint256)")[0:4] = 0xf8dc5dd9`. -/
axiom safeRemoveOwnerSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr removeownerTransition))).extract 0 4 =
      safeSelBytes 23

/-- `keccak("setFallbackHandler(address)")[0:4] = 0xf08a0323`. -/
axiom safeSetFallbackHandlerSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setfallbackhandlerTransition))).extract 0 4 =
      safeSelBytes 24

/-- `keccak("setGuard(address)")[0:4] = 0xe19a9dd9`. -/
axiom safeSetGuardSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setguardTransition))).extract 0 4 =
      safeSelBytes 25

/-- `keccak("setModuleGuard(address)")[0:4] = 0xe068df37`. -/
axiom safeSetModuleGuardSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setmoduleguardTransition))).extract 0 4 =
      safeSelBytes 26

/-- Selector for `setup`. -/
axiom safeSetupSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr setupTransition))).extract 0 4 =
      safeSelBytes 27

/-- `keccak("signedMessages(bytes32)")[0:4] = 0x5ae6bd37`. -/
axiom safeSignedMessagesSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr signedmessagesTransition))).extract 0 4 =
      safeSelBytes 28

/-- `keccak("simulateAndRevert(address,bytes)")[0:4] = 0xb4faba09`. -/
axiom safeSimulateAndRevertSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr simulateandrevertTransition))).extract 0 4 =
      safeSelBytes 29

/-- `keccak("swapOwner(address,address,address)")[0:4] = 0xe318b52b`. -/
axiom safeSwapOwnerSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr swapownerTransition))).extract 0 4 =
      safeSelBytes 30

end Benchmarks.Safe
