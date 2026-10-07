import Benchmarks.Safe.Spec

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.Safe

-- VERSION(); runtime entry PC 1688.
set_option maxRecDepth 1000000 in
theorem versionSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr versionTransition))).extract 0 4 =
      ⟨#[0xff, 0xa1, 0xad, 0x74]⟩ := by
  have hsig : transitionSigStr versionTransition =
      "VERSION()" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, versionTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- addOwnerWithThreshold(address,uint256); runtime entry PC 633.
set_option maxRecDepth 1000000 in
theorem addownerwiththresholdSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr addownerwiththresholdTransition))).extract 0 4 =
      ⟨#[0x0d, 0x58, 0x2f, 0x13]⟩ := by
  have hsig : transitionSigStr addownerwiththresholdTransition =
      "addOwnerWithThreshold(address,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, addownerwiththresholdTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- approveHash(bytes32); runtime entry PC 1315.
set_option maxRecDepth 1000000 in
theorem approvehashSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr approvehashTransition))).extract 0 4 =
      ⟨#[0xd4, 0xd9, 0xbd, 0xcd]⟩ := by
  have hsig : transitionSigStr approvehashTransition =
      "approveHash(bytes32)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, approvehashTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- approvedHashes(address,bytes32); runtime entry PC 1069.
set_option maxRecDepth 1000000 in
theorem approvedhashesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr approvedhashesTransition))).extract 0 4 =
      ⟨#[0x7d, 0x83, 0x29, 0x74]⟩ := by
  have hsig : transitionSigStr approvedhashesTransition =
      "approvedHashes(address,bytes32)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, approvedhashesTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- changeThreshold(uint256); runtime entry PC 1019.
set_option maxRecDepth 1000000 in
theorem changethresholdSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr changethresholdTransition))).extract 0 4 =
      ⟨#[0x69, 0x4e, 0x80, 0xc3]⟩ := by
  have hsig : transitionSigStr changethresholdTransition =
      "changeThreshold(uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, changethresholdTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- checkNSignatures(bytes32,bytes,bytes,uint256); runtime entry PC 666.
set_option maxRecDepth 1000000 in
theorem checknsignaturesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr checknsignaturesTransition))).extract 0 4 =
      ⟨#[0x12, 0xfb, 0x68, 0xe0]⟩ := by
  have hsig : transitionSigStr checknsignaturesTransition =
      "checkNSignatures(bytes32,bytes,bytes,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, checknsignaturesTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- checkNSignatures(address,bytes32,bytes,uint256); runtime entry PC 697.
set_option maxRecDepth 1000000 in
theorem checknsignaturesAddressBytes32BytesUint256SelectorBytes :
    (KEC (String.toByteArray (transitionSigStr checknsignaturesAddressBytes32BytesUint256Transition))).extract 0 4 =
      ⟨#[0x1f, 0xca, 0xc7, 0xf3]⟩ := by
  have hsig : transitionSigStr checknsignaturesAddressBytes32BytesUint256Transition =
      "checkNSignatures(address,bytes32,bytes,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, checknsignaturesAddressBytes32BytesUint256Transition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- checkSignatures(bytes32,bytes,bytes); runtime entry PC 1123.
set_option maxRecDepth 1000000 in
theorem checksignaturesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr checksignaturesTransition))).extract 0 4 =
      ⟨#[0x93, 0x4f, 0x3a, 0x11]⟩ := by
  have hsig : transitionSigStr checksignaturesTransition =
      "checkSignatures(bytes32,bytes,bytes)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, checksignaturesTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- checkSignatures(address,bytes32,bytes); runtime entry PC 1626.
set_option maxRecDepth 1000000 in
theorem checksignaturesAddressBytes32BytesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr checksignaturesAddressBytes32BytesTransition))).extract 0 4 =
      ⟨#[0xf8, 0x55, 0x43, 0x8b]⟩ := by
  have hsig : transitionSigStr checksignaturesAddressBytes32BytesTransition =
      "checkSignatures(address,bytes32,bytes)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, checksignaturesAddressBytes32BytesTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- disableModule(address,address); runtime entry PC 1377.
set_option maxRecDepth 1000000 in
theorem disablemoduleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr disablemoduleTransition))).extract 0 4 =
      ⟨#[0xe0, 0x09, 0xcf, 0xde]⟩ := by
  have hsig : transitionSigStr disablemoduleTransition =
      "disableModule(address,address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, disablemoduleTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- domainSeparator(); runtime entry PC 1552.
set_option maxRecDepth 1000000 in
theorem domainseparatorSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr domainseparatorTransition))).extract 0 4 =
      ⟨#[0xf6, 0x98, 0xda, 0x25]⟩ := by
  have hsig : transitionSigStr domainseparatorTransition =
      "domainSeparator()" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, domainseparatorTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- enableModule(address); runtime entry PC 988.
set_option maxRecDepth 1000000 in
theorem enablemoduleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr enablemoduleTransition))).extract 0 4 =
      ⟨#[0x61, 0x0b, 0x59, 0x25]⟩ := by
  have hsig : transitionSigStr enablemoduleTransition =
      "enableModule(address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, enablemoduleTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes); runtime entry PC 1050.
set_option maxRecDepth 1000000 in
theorem exectransactionSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr exectransactionTransition))).extract 0 4 =
      ⟨#[0x6a, 0x76, 0x12, 0x02]⟩ := by
  have hsig : transitionSigStr exectransactionTransition =
      "execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, exectransactionTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- execTransactionFromModule(address,uint256,bytes,uint8); runtime entry PC 811.
set_option maxRecDepth 1000000 in
theorem exectransactionfrommoduleSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr exectransactionfrommoduleTransition))).extract 0 4 =
      ⟨#[0x46, 0x87, 0x21, 0xa7]⟩ := by
  have hsig : transitionSigStr exectransactionfrommoduleTransition =
      "execTransactionFromModule(address,uint256,bytes,uint8)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, exectransactionfrommoduleTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- execTransactionFromModuleReturnData(address,uint256,bytes,uint8); runtime entry PC 842.
set_option maxRecDepth 1000000 in
theorem exectransactionfrommodulereturndataSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr exectransactionfrommodulereturndataTransition))).extract 0 4 =
      ⟨#[0x52, 0x29, 0x07, 0x3f]⟩ := by
  have hsig : transitionSigStr exectransactionfrommodulereturndataTransition =
      "execTransactionFromModuleReturnData(address,uint256,bytes,uint8)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, exectransactionfrommodulereturndataTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- getModulesPaginated(address,uint256); runtime entry PC 1270.
set_option maxRecDepth 1000000 in
theorem getmodulespaginatedSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getmodulespaginatedTransition))).extract 0 4 =
      ⟨#[0xcc, 0x2f, 0x84, 0x52]⟩ := by
  have hsig : transitionSigStr getmodulespaginatedTransition =
      "getModulesPaginated(address,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, getmodulespaginatedTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- getOwners(); runtime entry PC 1154.
set_option maxRecDepth 1000000 in
theorem getownersSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getownersTransition))).extract 0 4 =
      ⟨#[0xa0, 0xe6, 0x7e, 0x2b]⟩ := by
  have hsig : transitionSigStr getownersTransition =
      "getOwners()" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, getownersTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- getStorageAt(uint256,uint256); runtime entry PC 887.
set_option maxRecDepth 1000000 in
theorem getstorageatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getstorageatTransition))).extract 0 4 =
      ⟨#[0x56, 0x24, 0xb2, 0x5b]⟩ := by
  have hsig : transitionSigStr getstorageatTransition =
      "getStorageAt(uint256,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, getstorageatTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- getThreshold(); runtime entry PC 1501.
set_option maxRecDepth 1000000 in
theorem getthresholdSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getthresholdTransition))).extract 0 4 =
      ⟨#[0xe7, 0x52, 0x35, 0xb8]⟩ := by
  have hsig : transitionSigStr getthresholdTransition =
      "getThreshold()" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, getthresholdTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256); runtime entry PC 1346.
set_option maxRecDepth 1000000 in
theorem gettransactionhashSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr gettransactionhashTransition))).extract 0 4 =
      ⟨#[0xd8, 0xd1, 0x1f, 0x78]⟩ := by
  have hsig : transitionSigStr gettransactionhashTransition =
      "getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, gettransactionhashTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- isModuleEnabled(address); runtime entry PC 728.
set_option maxRecDepth 1000000 in
theorem ismoduleenabledSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ismoduleenabledTransition))).extract 0 4 =
      ⟨#[0x2d, 0x9a, 0xd5, 0x3d]⟩ := by
  have hsig : transitionSigStr ismoduleenabledTransition =
      "isModuleEnabled(address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, ismoduleenabledTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- isOwner(address); runtime entry PC 780.
set_option maxRecDepth 1000000 in
theorem isownerSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr isownerTransition))).extract 0 4 =
      ⟨#[0x2f, 0x54, 0xbf, 0x6e]⟩ := by
  have hsig : transitionSigStr isownerTransition =
      "isOwner(address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, isownerTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- nonce(); runtime entry PC 1187.
set_option maxRecDepth 1000000 in
theorem nonceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr nonceTransition))).extract 0 4 =
      ⟨#[0xaf, 0xfe, 0xd0, 0xe0]⟩ := by
  have hsig : transitionSigStr nonceTransition =
      "nonce()" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, nonceTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- removeOwner(address,address,uint256); runtime entry PC 1657.
set_option maxRecDepth 1000000 in
theorem removeownerSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr removeownerTransition))).extract 0 4 =
      ⟨#[0xf8, 0xdc, 0x5d, 0xd9]⟩ := by
  have hsig : transitionSigStr removeownerTransition =
      "removeOwner(address,address,uint256)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, removeownerTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- setFallbackHandler(address); runtime entry PC 1521.
set_option maxRecDepth 1000000 in
theorem setfallbackhandlerSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr setfallbackhandlerTransition))).extract 0 4 =
      ⟨#[0xf0, 0x8a, 0x03, 0x23]⟩ := by
  have hsig : transitionSigStr setfallbackhandlerTransition =
      "setFallbackHandler(address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, setfallbackhandlerTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- setGuard(address); runtime entry PC 1439.
set_option maxRecDepth 1000000 in
theorem setguardSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr setguardTransition))).extract 0 4 =
      ⟨#[0xe1, 0x9a, 0x9d, 0xd9]⟩ := by
  have hsig : transitionSigStr setguardTransition =
      "setGuard(address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, setguardTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- setModuleGuard(address); runtime entry PC 1408.
set_option maxRecDepth 1000000 in
theorem setmoduleguardSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr setmoduleguardTransition))).extract 0 4 =
      ⟨#[0xe0, 0x68, 0xdf, 0x37]⟩ := by
  have hsig : transitionSigStr setmoduleguardTransition =
      "setModuleGuard(address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, setmoduleguardTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- setup(address[],uint256,address,bytes,address,address,uint256,address); runtime entry PC 1239.
set_option maxRecDepth 1000000 in
theorem setupSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr setupTransition))).extract 0 4 =
      ⟨#[0xb6, 0x3e, 0x80, 0x0d]⟩ := by
  have hsig : transitionSigStr setupTransition =
      "setup(address[],uint256,address,bytes,address,address,uint256,address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, setupTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- signedMessages(bytes32); runtime entry PC 931.
set_option maxRecDepth 1000000 in
theorem signedmessagesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr signedmessagesTransition))).extract 0 4 =
      ⟨#[0x5a, 0xe6, 0xbd, 0x37]⟩ := by
  have hsig : transitionSigStr signedmessagesTransition =
      "signedMessages(bytes32)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, signedmessagesTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- simulateAndRevert(address,bytes); runtime entry PC 1208.
set_option maxRecDepth 1000000 in
theorem simulateandrevertSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr simulateandrevertTransition))).extract 0 4 =
      ⟨#[0xb4, 0xfa, 0xba, 0x09]⟩ := by
  have hsig : transitionSigStr simulateandrevertTransition =
      "simulateAndRevert(address,bytes)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, simulateandrevertTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

-- swapOwner(address,address,address); runtime entry PC 1470.
set_option maxRecDepth 1000000 in
theorem swapownerSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr swapownerTransition))).extract 0 4 =
      ⟨#[0xe3, 0x18, 0xb5, 0x2b]⟩ := by
  have hsig : transitionSigStr swapownerTransition =
      "swapOwner(address,address,address)" := by
    simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr,
      ABI.elemToSigStr, ABI.intTypeToSigStr, swapownerTransition,
      addr, uint8, uint256, uint8Int, uint256Int, bytes32, bytes32Width, bytesTy] <;>
      decide +kernel
  rw [hsig]
  decide +kernel

end Benchmarks.Safe
