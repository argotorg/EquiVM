import Benchmarks.Safe.Trusted

/-!
# Safe runtime dispatcher reach lemmas

The optimized Safe runtime has a payable receive path and a payable `execTransaction`, so the
runtime prologue does not contain a shared non-payable guard. This file proves the payable
prologue/selector-load prefix and the selector-tree path needed by simple getter proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeRootSplitPc : UInt256 := ⟨18⟩
abbrev safeLowSplitPc : UInt256 := ⟨258⟩
abbrev safeLowMidSplitPc : UInt256 := ⟨269⟩
abbrev safeLowUpperFirstArmPc : UInt256 := ⟨280⟩
abbrev safeLowLowerJumpdestPc : UInt256 := ⟨377⟩
abbrev safeLowLowerSplitPc : UInt256 := ⟨378⟩
abbrev safeLowLowerFirstArmPc : UInt256 := ⟨389⟩
abbrev safeLowLowerHighJumpdestPc : UInt256 := ⟨437⟩
abbrev safeLowLowerHighFirstArmPc : UInt256 := ⟨438⟩
abbrev safeLowHighJumpdestPc : UInt256 := ⟨328⟩
abbrev safeLowHighFirstArmPc : UInt256 := ⟨329⟩
abbrev safeHighSplitPc : UInt256 := ⟨29⟩
abbrev safeHighLowJumpdestPc : UInt256 := ⟨148⟩
abbrev safeHighLowSplitPc : UInt256 := ⟨149⟩
abbrev safeHighLowLowFirstArmPc : UInt256 := ⟨160⟩
abbrev safeHighLowHighJumpdestPc : UInt256 := ⟨208⟩
abbrev safeHighLowHighFirstArmPc : UInt256 := ⟨209⟩
abbrev safeHighHighSplitPc : UInt256 := ⟨40⟩
abbrev safeHighHighLowJumpdestPc : UInt256 := ⟨99⟩
abbrev safeHighHighLowFirstArmPc : UInt256 := ⟨100⟩
abbrev safeHighHighHighFirstArmPc : UInt256 := ⟨51⟩

/-! ## Selector dispatch facts -/

theorem safeSelectorDispatchGetThreshold {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 18)) :
    selectorDispatchMsg contract I.calldata = some getthresholdTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 18 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some getthresholdTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition ] ++
      getthresholdTransition ::
      [ gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition,
        nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes, safeDomainSeparatorSelectorBytes,
        safeEnableModuleSelectorBytes, safeExecTransactionSelectorBytes,
        safeExecTransactionFromModuleSelectorBytes,
        safeExecTransactionFromModuleReturnDataSelectorBytes,
        safeGetModulesPaginatedSelectorBytes, safeGetOwnersSelectorBytes,
        safeGetStorageAtSelectorBytes]
      native_decide
  · rw [selectorOf, safeGetThresholdSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchVersion {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 0)) :
    selectorDispatchMsg contract I.calldata = some versionTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some versionTransition
  rw [show transitions = [] ++ versionTransition ::
      [ addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition,
        nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
  · rw [selectorOf, safeVersionSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchApprovedHashes {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 3)) :
    selectorDispatchMsg contract I.calldata = some approvedhashesTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some approvedhashesTransition
  simp [transitions, dispatchList, selectorOf, hcd, safeSelBytes,
    safeVersionSelectorBytes, safeAddOwnerWithThresholdSelectorBytes,
    safeApproveHashSelectorBytes, safeApprovedHashesSelectorBytes]
  native_decide

theorem safeSelectorDispatchApproveHash {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 2)) :
    selectorDispatchMsg contract I.calldata = some approvehashTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some approvehashTransition
  simp [transitions, dispatchList, selectorOf, hcd, safeSelBytes,
    safeVersionSelectorBytes, safeAddOwnerWithThresholdSelectorBytes,
    safeApproveHashSelectorBytes]
  native_decide

theorem safeSelectorDispatchChangeThreshold {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 4)) :
    selectorDispatchMsg contract I.calldata = some changethresholdTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some changethresholdTransition
  simp [transitions, dispatchList, selectorOf, hcd, safeSelBytes,
    safeVersionSelectorBytes, safeAddOwnerWithThresholdSelectorBytes,
    safeApproveHashSelectorBytes, safeApprovedHashesSelectorBytes,
    safeChangeThresholdSelectorBytes]
  native_decide

theorem safeSelectorDispatchDisableModule {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 9)) :
    selectorDispatchMsg contract I.calldata = some disablemoduleTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some disablemoduleTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition ] ++
      disablemoduleTransition ::
      [ domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition,
        nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes]
      native_decide
  · rw [selectorOf, safeDisableModuleSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchSetFallbackHandler {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 24)) :
    selectorDispatchMsg contract I.calldata = some setfallbackhandlerTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 24 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some setfallbackhandlerTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition,
        nonceTransition,
        removeownerTransition ] ++
      setfallbackhandlerTransition ::
      [ setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes, safeDomainSeparatorSelectorBytes,
        safeEnableModuleSelectorBytes, safeExecTransactionSelectorBytes,
        safeExecTransactionFromModuleSelectorBytes,
        safeExecTransactionFromModuleReturnDataSelectorBytes,
        safeGetModulesPaginatedSelectorBytes, safeGetOwnersSelectorBytes,
        safeGetStorageAtSelectorBytes, safeGetThresholdSelectorBytes,
        safeGetTransactionHashSelectorBytes, safeIsModuleEnabledSelectorBytes,
        safeIsOwnerSelectorBytes, safeNonceSelectorBytes, safeRemoveOwnerSelectorBytes]
      native_decide
  · rw [selectorOf, safeSetFallbackHandlerSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchIsModuleEnabled {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 20)) :
    selectorDispatchMsg contract I.calldata = some ismoduleenabledTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 20 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some ismoduleenabledTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition ] ++
      ismoduleenabledTransition ::
      [ isownerTransition,
        nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes, safeDomainSeparatorSelectorBytes,
        safeEnableModuleSelectorBytes, safeExecTransactionSelectorBytes,
        safeExecTransactionFromModuleSelectorBytes,
        safeExecTransactionFromModuleReturnDataSelectorBytes,
        safeGetModulesPaginatedSelectorBytes, safeGetOwnersSelectorBytes,
        safeGetStorageAtSelectorBytes, safeGetThresholdSelectorBytes,
        safeGetTransactionHashSelectorBytes]
      native_decide
  · rw [selectorOf, safeIsModuleEnabledSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchIsOwner {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 21)) :
    selectorDispatchMsg contract I.calldata = some isownerTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 21 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some isownerTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition ] ++
      isownerTransition ::
      [ nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes, safeDomainSeparatorSelectorBytes,
        safeEnableModuleSelectorBytes, safeExecTransactionSelectorBytes,
        safeExecTransactionFromModuleSelectorBytes,
        safeExecTransactionFromModuleReturnDataSelectorBytes,
        safeGetModulesPaginatedSelectorBytes, safeGetOwnersSelectorBytes,
        safeGetStorageAtSelectorBytes, safeGetThresholdSelectorBytes,
        safeGetTransactionHashSelectorBytes, safeIsModuleEnabledSelectorBytes]
      native_decide
  · rw [selectorOf, safeIsOwnerSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchNonce {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 22)) :
    selectorDispatchMsg contract I.calldata = some nonceTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 22 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some nonceTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition ] ++
      nonceTransition ::
      [ removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes, safeDomainSeparatorSelectorBytes,
        safeEnableModuleSelectorBytes, safeExecTransactionSelectorBytes,
        safeExecTransactionFromModuleSelectorBytes,
        safeExecTransactionFromModuleReturnDataSelectorBytes,
        safeGetModulesPaginatedSelectorBytes, safeGetOwnersSelectorBytes,
        safeGetStorageAtSelectorBytes, safeGetThresholdSelectorBytes,
        safeGetTransactionHashSelectorBytes, safeIsModuleEnabledSelectorBytes,
        safeIsOwnerSelectorBytes]
      native_decide
  · rw [selectorOf, safeNonceSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchDomainSeparator {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 10)) :
    selectorDispatchMsg contract I.calldata = some domainseparatorTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some domainseparatorTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition ] ++
      domainseparatorTransition ::
      [ enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition,
        nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes]
      native_decide
  · rw [selectorOf, safeDomainSeparatorSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchEnableModule {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 11)) :
    selectorDispatchMsg contract I.calldata = some enablemoduleTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some enablemoduleTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition ] ++
      enablemoduleTransition ::
      [ exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition,
        nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition,
        signedmessagesTransition,
        simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes, safeDomainSeparatorSelectorBytes]
      native_decide
  · rw [selectorOf, safeEnableModuleSelectorBytes]
    rw [hcd]
    native_decide

theorem safeSelectorDispatchSignedMessages {I : ExecutionEnv}
    (hsel : selIs I (safeSelBytes 28)) :
    selectorDispatchMsg contract I.calldata = some signedmessagesTransition := by
  have hcd : I.calldata.extract 0 4 = safeSelBytes 28 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  change dispatchList transitions I.calldata = some signedmessagesTransition
  rw [show transitions =
      [ versionTransition,
        addownerwiththresholdTransition,
        approvehashTransition,
        approvedhashesTransition,
        changethresholdTransition,
        checknsignaturesTransition,
        checknsignaturesAddressBytes32BytesUint256Transition,
        checksignaturesTransition,
        checksignaturesAddressBytes32BytesTransition,
        disablemoduleTransition,
        domainseparatorTransition,
        enablemoduleTransition,
        exectransactionTransition,
        exectransactionfrommoduleTransition,
        exectransactionfrommodulereturndataTransition,
        getmodulespaginatedTransition,
        getownersTransition,
        getstorageatTransition,
        getthresholdTransition,
        gettransactionhashTransition,
        ismoduleenabledTransition,
        isownerTransition,
        nonceTransition,
        removeownerTransition,
        setfallbackhandlerTransition,
        setguardTransition,
        setmoduleguardTransition,
        setupTransition ] ++
      signedmessagesTransition ::
      [ simulateandrevertTransition,
        swapownerTransition ] by rfl]
  apply dispatchList_eq_some_of_split
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, hcd, safeSelBytes, safeVersionSelectorBytes,
        safeAddOwnerWithThresholdSelectorBytes, safeApproveHashSelectorBytes,
        safeApprovedHashesSelectorBytes, safeChangeThresholdSelectorBytes,
        safeCheckNSignaturesSelectorBytes, safeCheckNSignaturesWithExecutorSelectorBytes,
        safeCheckSignaturesSelectorBytes, safeCheckSignaturesWithExecutorSelectorBytes,
        safeDisableModuleSelectorBytes, safeDomainSeparatorSelectorBytes,
        safeEnableModuleSelectorBytes, safeExecTransactionSelectorBytes,
        safeExecTransactionFromModuleSelectorBytes,
        safeExecTransactionFromModuleReturnDataSelectorBytes,
        safeGetModulesPaginatedSelectorBytes, safeGetOwnersSelectorBytes,
        safeGetStorageAtSelectorBytes, safeGetThresholdSelectorBytes,
        safeGetTransactionHashSelectorBytes, safeIsModuleEnabledSelectorBytes,
        safeIsOwnerSelectorBytes, safeNonceSelectorBytes, safeRemoveOwnerSelectorBytes,
        safeSetFallbackHandlerSelectorBytes, safeSetGuardSelectorBytes,
        safeSetModuleGuardSelectorBytes, safeSetupSelectorBytes]
      native_decide
  · rw [selectorOf, safeSignedMessagesSelectorBytes]
    rw [hcd]
    native_decide

/-! ## Runtime selector reachability -/

/-- Safe prologue: install free memory pointer, pass the `size ≥ 4` calldata guard, and load the
    selector, reaching the root split at pc 18 with the selector word on the stack. -/
theorem safeReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeRootSplitPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have h5 := (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    |>.push1 ⟨128⟩ (by native_decide) (by decide)
    |>.push1 ⟨64⟩ (by native_decide) (by decide)
    |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
        mem_cost (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
        (by decide) (by decide)
  have h13 := h5
    |>.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.pushConst (⟨475⟩ : UInt256) (width := 2) (op := .PUSH2) (by native_decide)
        (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (lt_four_eq_zero_of_ge hsz hsize)
        (by simp only [List.length]; omega)
  obtain ⟨k, C, h18⟩ := solcSelectorLoad h13 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by simp only [List.length]; omega)
  exact ⟨k, C, by simpa [safeRootSplitPc, safeSelWord] using h18⟩

theorem safeRootSplitWellFormed :
    selectorSplitWellFormed safeBytecode safeRootSplitPc := by
  dsimp [selectorSplitWellFormed, safeRootSplitPc]
  repeat' first | apply And.intro | native_decide

theorem safeLowSplitWellFormed :
    selectorSplitWellFormed safeBytecode safeLowSplitPc := by
  dsimp [selectorSplitWellFormed, safeLowSplitPc]
  repeat' first | apply And.intro | native_decide

theorem safeLowMidSplitWellFormed :
    selectorSplitWellFormed safeBytecode safeLowMidSplitPc := by
  dsimp [selectorSplitWellFormed, safeLowMidSplitPc]
  repeat' first | apply And.intro | native_decide

theorem safeLowLowerSplitWellFormed :
    selectorSplitWellFormed safeBytecode safeLowLowerSplitPc := by
  dsimp [selectorSplitWellFormed, safeLowLowerSplitPc]
  repeat' first | apply And.intro | native_decide

theorem safeHighSplitWellFormed :
    selectorSplitWellFormed safeBytecode safeHighSplitPc := by
  dsimp [selectorSplitWellFormed, safeHighSplitPc]
  repeat' first | apply And.intro | native_decide

theorem safeHighHighSplitWellFormed :
    selectorSplitWellFormed safeBytecode safeHighHighSplitPc := by
  dsimp [selectorSplitWellFormed, safeHighHighSplitPc]
  repeat' first | apply And.intro | native_decide

theorem safeHighHighLowArmsWellFormed :
    ∀ j, j ≤ 3 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeHighHighLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeHighHighLowFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeHighHighHighArmsWellFormed :
    ∀ j, j ≤ 3 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeHighHighHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeHighHighHighFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeHighLowHighArmsWellFormed :
    ∀ j, j ≤ 3 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeHighLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeHighLowHighFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeHighLowLowArmsWellFormed :
    ∀ j, j ≤ 3 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeHighLowLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeHighLowLowFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeLowHighArmsWellFormed :
    ∀ j, j ≤ 3 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeLowHighFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeLowUpperArmsWellFormed :
    ∀ j, j ≤ 3 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeLowUpperFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeLowUpperFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeLowLowerArmsWellFormed :
    ∀ j, j ≤ 3 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeLowLowerFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeLowLowerFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeLowLowerHighArmsWellFormed :
    ∀ j, j ≤ 2 →
      armWellFormed safeBytecode (nthArmPc safeBytecode safeLowLowerHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed, safeLowLowerHighFirstArmPc]
     repeat' first | apply And.intro | native_decide)

theorem safeReachLowUpperFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt ⟨1445245531⟩ (safeSelWord I) = ⟨0⟩)
    (hmid : UInt256.gt ⟨1786122754⟩ (safeSelWord I) = ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowUpperFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h257 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨257⟩ [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) _ _ :=
    h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hroot (by native_decide) (by simp)
  obtain ⟨_, _, h258⟩ : ∃ k C,
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
        safeLowSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [safeLowSplitPc] using
        h257.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩
  have h269 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨269⟩ [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) _ _ :=
    h258.dup1 (by native_decide) (by simp)
      |>.push4 ⟨1445245531⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨377⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hlow (by simp)
  have h280 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowUpperFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h269.dup1 (by native_decide) (by simp)
      |>.push4 ⟨1786122754⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨328⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hmid (by simp)
  exact ⟨_, _, by simpa [safeLowUpperFirstArmPc] using h280⟩

theorem safeReachLowHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt ⟨1445245531⟩ (safeSelWord I) = ⟨0⟩)
    (hmid : UInt256.gt ⟨1786122754⟩ (safeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowHighFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h257 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨257⟩ [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) _ _ :=
    h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hroot (by native_decide) (by simp)
  obtain ⟨_, _, h258⟩ : ∃ k C,
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
        safeLowSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [safeLowSplitPc] using
        h257.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩
  have h269 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨269⟩ [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) _ _ :=
    h258.dup1 (by native_decide) (by simp)
      |>.push4 ⟨1445245531⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨377⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hlow (by simp)
  have h328 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowHighJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h269.dup1 (by native_decide) (by simp)
      |>.push4 ⟨1786122754⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨328⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hmid (by native_decide) (by simp)
  exact ⟨_, _, by
    simpa [safeLowHighJumpdestPc, safeLowHighFirstArmPc] using
      h328.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩

theorem safeReachLowLowerFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt ⟨1445245531⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hfirst : UInt256.gt ⟨765121853⟩ (safeSelWord I) = ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowLowerFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h257 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨257⟩ [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) _ _ :=
    h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hroot (by native_decide) (by simp)
  obtain ⟨_, _, h258⟩ : ∃ k C,
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
        safeLowSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [safeLowSplitPc] using
        h257.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩
  have h377 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowLowerJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h258.dup1 (by native_decide) (by simp)
      |>.push4 ⟨1445245531⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨377⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hlow (by native_decide) (by simp)
  have h389 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowLowerFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h377.jumpdest (by native_decide) (by simp only [List.length]; omega)
      |>.dup1 (by native_decide) (by simp)
      |>.push4 ⟨765121853⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨437⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hfirst (by simp)
  exact ⟨_, _, by simpa [safeLowLowerFirstArmPc] using h389⟩

theorem safeReachLowLowerHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt ⟨1445245531⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hfirst : UInt256.gt ⟨765121853⟩ (safeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowLowerHighFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h257 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨257⟩ [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) _ _ :=
    h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hroot (by native_decide) (by simp)
  obtain ⟨_, _, h258⟩ : ∃ k C,
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
        safeLowSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [safeLowSplitPc] using
        h257.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩
  have h377 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowLowerJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h258.dup1 (by native_decide) (by simp)
      |>.push4 ⟨1445245531⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨377⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hlow (by native_decide) (by simp)
  have h437 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeLowLowerHighJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h377.jumpdest (by native_decide) (by simp only [List.length]; omega)
      |>.dup1 (by native_decide) (by simp)
      |>.push4 ⟨765121853⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨437⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hfirst (by native_decide) (by simp)
  exact ⟨_, _, by
    simpa [safeLowLowerHighJumpdestPc, safeLowLowerHighFirstArmPc] using
      h437.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩

theorem safeReachHighHighLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt ⟨3785006553⟩ (safeSelWord I) = ⟨0⟩)
    (hthird : UInt256.gt ⟨4137212453⟩ (safeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighHighLowFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h29 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k18 + 5) (C18 + 22) := by
    exact h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hroot (by simp)
  have h40 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighHighSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k18 + 5 + 5) (C18 + 22 + 22) := by
    exact h29.dup1 (by native_decide) (by simp)
      |>.push4 ⟨3785006553⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨148⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hhigh (by simp)
  have h99 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighHighLowJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h40.dup1 (by native_decide) (by simp)
      |>.push4 ⟨4137212453⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨99⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hthird (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [safeHighHighLowJumpdestPc, safeHighHighLowFirstArmPc] using
      h99.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩

theorem safeReachHighHighHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt ⟨3785006553⟩ (safeSelWord I) = ⟨0⟩)
    (hthird : UInt256.gt ⟨4137212453⟩ (safeSelWord I) = ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighHighHighFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h29 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k18 + 5) (C18 + 22) := by
    exact h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hroot (by simp)
  have h40 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighHighSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k18 + 5 + 5) (C18 + 22 + 22) := by
    exact h29.dup1 (by native_decide) (by simp)
      |>.push4 ⟨3785006553⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨148⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hhigh (by simp)
  have h51 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighHighHighFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h40.dup1 (by native_decide) (by simp)
      |>.push4 ⟨4137212453⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨99⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hthird (by simp)
  exact ⟨_, _, by simpa [safeHighHighHighFirstArmPc] using h51⟩

theorem safeReachHighLowHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt ⟨3785006553⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt ⟨3571039693⟩ (safeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighLowHighFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h29 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k18 + 5) (C18 + 22) := by
    exact h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hroot (by simp)
  have h148 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighLowJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h29.dup1 (by native_decide) (by simp)
      |>.push4 ⟨3785006553⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨148⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hhigh (by native_decide) (by simp)
  obtain ⟨_, _, h149⟩ : ∃ k C,
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
        safeHighLowSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [safeHighLowJumpdestPc, safeHighLowSplitPc] using
        h148.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩
  have h208 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighLowHighJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h149.dup1 (by native_decide) (by simp)
      |>.push4 ⟨3571039693⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨208⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hlow (by native_decide) (by simp)
  exact ⟨_, _, by
    simpa [safeHighLowHighJumpdestPc, safeHighLowHighFirstArmPc] using
      h208.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩

/-- Reach the first arm in the high-low/low selector cluster (pc 160). -/
theorem safeReachHighLowLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt ⟨3785006553⟩ (safeSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt ⟨3571039693⟩ (safeSelWord I) = ⟨0⟩) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighLowLowFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k18, C18, h18⟩ :=
    safeReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hsz hsize
  have h29 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k18 + 5) (C18 + 22) := by
    exact h18.dup1 (by native_decide) (by simp)
      |>.push4 ⟨2952712416⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨257⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hroot (by simp)
  have h148 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighLowJumpdestPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h29.dup1 (by native_decide) (by simp)
      |>.push4 ⟨3785006553⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨148⟩ (by native_decide) (by simp)
      |>.jumpiT (by native_decide) hhigh (by native_decide) (by simp)
  obtain ⟨_, _, h149⟩ : ∃ k C,
      RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
        safeHighLowSplitPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [safeHighLowJumpdestPc, safeHighLowSplitPc] using
        h148.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩
  have h160 : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I)
      safeHighLowLowFirstArmPc [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ :=
    h149.dup1 (by native_decide) (by simp)
      |>.push4 ⟨3571039693⟩ (by native_decide) (by simp)
      |>.gt (by native_decide) (by simp)
      |>.push2 ⟨208⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) hlow (by simp)
  exact ⟨_, _, by simpa [safeHighLowLowFirstArmPc] using h160⟩

theorem safeReachFallbackShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode)
    (hshort : I.calldata.size < 4)
    (hcalldata : I.calldata.size ≠ 0) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hnonzero : UInt256.ofNat I.calldata.size ≠ (⟨0⟩ : UInt256) := by
    intro hz
    apply hcalldata
    have hto : (UInt256.ofNat I.calldata.size).toNat = 0 := by rw [hz]; rfl
    rw [UInt256.toNat_ofNat_of_lt (lt_trans hshort (by decide))] at hto
    exact hto
  have h5 := evm_run
      (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode)
      with [
        push1 ⟨128⟩,
        push1 ⟨64⟩,
        raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
          mem_cost (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
          (by decide) (by evm_ov)]
  have h475 := evm_run h5 with [
    push1 ⟨4⟩,
    calldatasize,
    lt,
    push2 ⟨475⟩,
    jumpiT (lt_four_ne_zero_of_lt hshort) (by jump_dest)]
  have h477 := evm_run h475 with [jumpdest, calldatasize]
  have h535 := evm_run h477 with [
    push2 ⟨535⟩,
    jumpiT hnonzero (by jump_dest)]
  exact ⟨_, _, h535⟩

theorem safeSelectorMissOfNoMatch {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false)
    (i : ℕ) (hi : i < 31) (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hbytes : safeSelBytes i = (⟨#[c0, c1, c2, c3]⟩ : ByteArray)) :
    UInt256.eq sel (safeSelWord I) = ⟨0⟩ := by
  dsimp [safeSelWord]
  rw [evmSelectorDecode hsz c0 c1 c2 c3 sel hsel]
  have hno := hnm i hi
  rw [hbytes] at hno
  simp [hno]

theorem safeHighHighHighMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighHighHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 10 (by decide) 0xf6 0x98 0xda 0x25 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 8 (by decide) 0xf8 0x55 0x43 0x8b _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 23 (by decide) 0xf8 0xdc 0x5d 0xd9 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 0 (by decide) 0xff 0xa1 0xad 0x74 _
      (by native_decide) rfl

theorem safeHighHighLowMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighHighLowFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 25 (by decide) 0xe1 0x9a 0x9d 0xd9 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 30 (by decide) 0xe3 0x18 0xb5 0x2b _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 18 (by decide) 0xe7 0x52 0x35 0xb8 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 24 (by decide) 0xf0 0x8a 0x03 0x23 _
      (by native_decide) rfl

theorem safeHighLowLowMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighLowLowFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 2 (by decide) 0xd4 0xd9 0xbd 0xcd _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 19 (by decide) 0xd8 0xd1 0x1f 0x78 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 9 (by decide) 0xe0 0x09 0xcf 0xde _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 26 (by decide) 0xe0 0x68 0xdf 0x37 _
      (by native_decide) rfl

theorem safeHighLowHighMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighLowHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 22 (by decide) 0xaf 0xfe 0xd0 0xe0 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 29 (by decide) 0xb4 0xfa 0xba 0x09 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 27 (by decide) 0xb6 0x3e 0x80 0x0d _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 15 (by decide) 0xcc 0x2f 0x84 0x52 _
      (by native_decide) rfl

theorem safeLowUpperMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowUpperFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 12 (by decide) 0x6a 0x76 0x12 0x02 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 3 (by decide) 0x7d 0x83 0x29 0x74 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 7 (by decide) 0x93 0x4f 0x3a 0x11 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 16 (by decide) 0xa0 0xe6 0x7e 0x2b _
      (by native_decide) rfl

theorem safeLowHighMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 17 (by decide) 0x56 0x24 0xb2 0x5b _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 28 (by decide) 0x5a 0xe6 0xbd 0x37 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 11 (by decide) 0x61 0x0b 0x59 0x25 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 4 (by decide) 0x69 0x4e 0x80 0xc3 _
      (by native_decide) rfl

theorem safeLowLowerMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowLowerFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 20 (by decide) 0x2d 0x9a 0xd5 0x3d _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 21 (by decide) 0x2f 0x54 0xbf 0x6e _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 13 (by decide) 0x46 0x87 0x21 0xa7 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 14 (by decide) 0x52 0x29 0x07 0x3f _
      (by native_decide) rfl

theorem safeLowLowerHighMiss {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∀ j, j ≤ 2 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowLowerHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩ := by
  intro j hj
  interval_cases j
  · exact safeSelectorMissOfNoMatch hsz hnm 1 (by decide) 0x0d 0x58 0x2f 0x13 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 5 (by decide) 0x12 0xfb 0x68 0xe0 _
      (by native_decide) rfl
  · exact safeSelectorMissOfNoMatch hsz hnm 6 (by decide) 0x1f 0xca 0xc7 0xf3 _
      (by native_decide) rfl

theorem safeHighHighHighFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeHighHighHighFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighHighHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h95 := h
    |>.selectorArmNotTakenAuto (safeHighHighHighArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighHighHighArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighHighHighArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighHighHighArmsWellFormed 3 (by omega))
        (hmiss 3 (by omega)) (by simp)
  exact ⟨_, _, evm_run h95 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem safeHighHighLowFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeHighHighLowFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighHighLowFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h144 := h
    |>.selectorArmNotTakenAuto (safeHighHighLowArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighHighLowArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighHighLowArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighHighLowArmsWellFormed 3 (by omega))
        (hmiss 3 (by omega)) (by simp)
  exact ⟨_, _, evm_run h144 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem safeHighLowLowFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeHighLowLowFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighLowLowFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h204 := h
    |>.selectorArmNotTakenAuto (safeHighLowLowArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighLowLowArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighLowLowArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighLowLowArmsWellFormed 3 (by omega))
        (hmiss 3 (by omega)) (by simp)
  exact ⟨_, _, evm_run h204 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem safeHighLowHighFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeHighLowHighFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeHighLowHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h253 := h
    |>.selectorArmNotTakenAuto (safeHighLowHighArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighLowHighArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighLowHighArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeHighLowHighArmsWellFormed 3 (by omega))
        (hmiss 3 (by omega)) (by simp)
  exact ⟨_, _, evm_run h253 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem safeLowUpperFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeLowUpperFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowUpperFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h324 := h
    |>.selectorArmNotTakenAuto (safeLowUpperArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowUpperArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowUpperArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowUpperArmsWellFormed 3 (by omega))
        (hmiss 3 (by omega)) (by simp)
  exact ⟨_, _, evm_run h324 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem safeLowHighFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeLowHighFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h373 := h
    |>.selectorArmNotTakenAuto (safeLowHighArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowHighArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowHighArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowHighArmsWellFormed 3 (by omega))
        (hmiss 3 (by omega)) (by simp)
  exact ⟨_, _, evm_run h373 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem safeLowLowerFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeLowLowerFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 3 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowLowerFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h433 := h
    |>.selectorArmNotTakenAuto (safeLowLowerArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowLowerArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowLowerArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowLowerArmsWellFormed 3 (by omega))
        (hmiss 3 (by omega)) (by simp)
  exact ⟨_, _, evm_run h433 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

theorem safeLowLowerHighFallthrough {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) safeLowLowerHighFirstArmPc
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmiss : ∀ j, j ≤ 2 →
      UInt256.eq (armSelNat safeBytecode (nthArmPc safeBytecode safeLowLowerHighFirstArmPc j))
        (safeSelWord I) = ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h471 := h
    |>.selectorArmNotTakenAuto (safeLowLowerHighArmsWellFormed 0 (by omega))
        (hmiss 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowLowerHighArmsWellFormed 1 (by omega))
        (hmiss 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (safeLowLowerHighArmsWellFormed 2 (by omega))
        (hmiss 2 (by omega)) (by simp)
  exact ⟨_, _, evm_run h471 with [push2 ⟨535⟩, jump (by jump_dest)]⟩

/-- Calldata with no matching selector reaches the shared fallback body at pc 535.  The stack keeps
    the selector word beneath the fallback machinery, matching solc's fallthrough jumps. -/
theorem safeReachFallbackNoMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode)
    (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  classical
  by_cases hroot : UInt256.gt ⟨2952712416⟩ (safeSelWord I) = ⟨0⟩
  · by_cases hhigh : UInt256.gt ⟨3785006553⟩ (safeSelWord I) = ⟨0⟩
    · by_cases hthird : UInt256.gt ⟨4137212453⟩ (safeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h51⟩ := safeReachHighHighHighFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hhigh hthird
        exact safeHighHighHighFallthrough h51 (safeHighHighHighMiss hsz hnm)
      · obtain ⟨_, _, h100⟩ := safeReachHighHighLowFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hhigh hthird
        exact safeHighHighLowFallthrough h100 (safeHighHighLowMiss hsz hnm)
    · by_cases hlow : UInt256.gt ⟨3571039693⟩ (safeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h160⟩ := safeReachHighLowLowFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hhigh hlow
        exact safeHighLowLowFallthrough h160 (safeHighLowLowMiss hsz hnm)
      · obtain ⟨_, _, h209⟩ := safeReachHighLowHighFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hhigh hlow
        exact safeHighLowHighFallthrough h209 (safeHighLowHighMiss hsz hnm)
  · by_cases hlow : UInt256.gt ⟨1445245531⟩ (safeSelWord I) = ⟨0⟩
    · by_cases hmid : UInt256.gt ⟨1786122754⟩ (safeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h280⟩ := safeReachLowUpperFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hlow hmid
        exact safeLowUpperFallthrough h280 (safeLowUpperMiss hsz hnm)
      · obtain ⟨_, _, h329⟩ := safeReachLowHighFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hlow hmid
        exact safeLowHighFallthrough h329 (safeLowHighMiss hsz hnm)
    · by_cases hfirst : UInt256.gt ⟨765121853⟩ (safeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h389⟩ := safeReachLowLowerFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hlow hfirst
        exact safeLowLowerFallthrough h389 (safeLowLowerMiss hsz hnm)
      · obtain ⟨_, _, h438⟩ := safeReachLowLowerHighFirstArm
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcode hsz hsize hroot hlow hfirst
        exact safeLowLowerHighFallthrough h438 (safeLowLowerHighMiss hsz hnm)

/-- Reach `approveHash(bytes32)` body entry (pc 1315). -/
theorem safeReachApproveHashBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 2)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1315⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨3571039693⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0xd4 0xd9 0xbd 0xcd ⟨3571039693⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h160⟩ := safeReachHighLowLowFirstArm (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz
    hsize (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1315⟩ 0 h160
    (fun j hj => safeHighLowLowArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `disableModule(address,address)` body entry (pc 1377). -/
theorem safeReachDisableModuleBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 9)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1377⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨3758739422⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0xe0 0x09 0xcf 0xde ⟨3758739422⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h160⟩ := safeReachHighLowLowFirstArm (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz
    hsize (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1377⟩ 2 h160
    (fun j hj => safeHighLowLowArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `domainSeparator()` body entry (pc 1552). -/
theorem safeReachDomainSeparatorBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 10)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1552⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨4137212453⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0xf6 0x98 0xda 0x25 ⟨4137212453⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h51⟩ := safeReachHighHighHighFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1552⟩ 0 h51
    (fun j hj => safeHighHighHighArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `VERSION()` body entry (pc 1688). -/
theorem safeReachVersionBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 0)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1688⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨4288785780⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0xff 0xa1 0xad 0x74 ⟨4288785780⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h51⟩ := safeReachHighHighHighFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1688⟩ 3 h51
    (fun j hj => safeHighHighHighArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `approvedHashes(address,bytes32)` body entry (pc 1069). -/
theorem safeReachApprovedHashesBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 3)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1069⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨2105747828⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0x7d 0x83 0x29 0x74 ⟨2105747828⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h280⟩ := safeReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1069⟩ 1 h280
    (fun j hj => safeLowUpperArmsWellFormed j (by omega))
    (fun j hj => by
      interval_cases j
      rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `changeThreshold(uint256)` body entry (pc 1019). -/
theorem safeReachChangeThresholdBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 4)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1019⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨1766752451⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0x69 0x4e 0x80 0xc3 ⟨1766752451⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h329⟩ := safeReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1019⟩ 3 h329
    (fun j hj => safeLowHighArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `enableModule(address)` body entry (pc 988). -/
theorem safeReachEnableModuleBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 11)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨988⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨1628133669⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0x61 0x0b 0x59 0x25 ⟨1628133669⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h329⟩ := safeReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨988⟩ 2 h329
    (fun j hj => safeLowHighArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `isModuleEnabled(address)` body entry (pc 728). -/
theorem safeReachIsModuleEnabledBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 20)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨728⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨765121853⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0x2d 0x9a 0xd5 0x3d ⟨765121853⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h389⟩ := safeReachLowLowerFirstArm (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz
    hsize (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨728⟩ 0 h389
    (fun j hj => safeLowLowerArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `isOwner(address)` body entry (pc 780). -/
theorem safeReachIsOwnerBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 21)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨780⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨794083182⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0x2f 0x54 0xbf 0x6e ⟨794083182⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h389⟩ := safeReachLowLowerFirstArm (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz
    hsize (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨780⟩ 1 h389
    (fun j hj => safeLowLowerArmsWellFormed j (by omega))
    (fun j hj => by
      interval_cases j
      rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `getThreshold()` body entry (pc 1501). -/
theorem safeReachGetThresholdBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 18)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1501⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨3880924600⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0xe7 0x52 0x35 0xb8 ⟨3880924600⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h100⟩ := safeReachHighHighLowFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1501⟩ 2 h100
    (fun j hj => safeHighHighLowArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

/-- Reach `setFallbackHandler(address)` body entry (pc 1521). -/
theorem safeReachSetFallbackHandlerBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 24)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1521⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨4035576611⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0xf0 0x8a 0x03 0x23 ⟨4035576611⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h100⟩ := safeReachHighHighLowFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1521⟩ 3 h100
    (fun j hj => safeHighHighLowArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `nonce()` body entry (pc 1187). -/
theorem safeReachNonceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 22)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨2952712416⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0xaf 0xfe 0xd0 0xe0 ⟨2952712416⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h209⟩ := safeReachHighLowHighFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨1187⟩ 0 h209
    (fun j hj => safeHighLowHighArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

/-- Reach `signedMessages(bytes32)` body entry (pc 931). -/
theorem safeReachSignedMessagesBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 28)) :
    ∃ k C, RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨931⟩
      [safeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : safeSelWord I = ⟨1525071159⟩ := by
    simpa [safeSelWord] using
      solcSelectorWord_eq_of_beq I hsz 0x5a 0xe6 0xbd 0x37 ⟨1525071159⟩
        (by native_decide) (by simpa [safeSelBytes] using hsel)
  obtain ⟨_, _, h329⟩ := safeReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨931⟩ 1 h329
    (fun j hj => safeLowHighArmsWellFormed j (by omega))
    (fun j hj => by
      interval_cases j
      rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by native_decide) (by native_decide)
    (by simp)

end Benchmarks.Safe
