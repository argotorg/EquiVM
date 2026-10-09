import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! ## Solm dispatch: which transition a selector reaches -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

theorem metaMorphoV1_1Dispatch_totalAssets {I : ExecutionEnv} 
    (hsel : selIs I (metaMorphoV1_1SelBytes 0)) :
    dispatchMsg contract I.calldata = some totalAssetsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := []) (post := [nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := totalAssetsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp at hu
  · rw [totalAssetsSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_name {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0))
    (hsel : selIs I (metaMorphoV1_1SelBytes 1)) :
    dispatchMsg contract I.calldata = some nameTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition]) (post := [convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := nameTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
  · rw [nameSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_convertToAssets {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1))
    (hsel : selIs I (metaMorphoV1_1SelBytes 2)) :
    dispatchMsg contract I.calldata = some convertToAssetsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition]) (post := [approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := convertToAssetsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
  · rw [convertToAssetsSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_approve {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2))
    (hsel : selIs I (metaMorphoV1_1SelBytes 3)) :
    dispatchMsg contract I.calldata = some approveTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition]) (post := [previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := approveTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
  · rw [approveSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_previewWithdraw {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3))
    (hsel : selIs I (metaMorphoV1_1SelBytes 4)) :
    dispatchMsg contract I.calldata = some previewWithdrawTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition]) (post := [revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := previewWithdrawTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
  · rw [previewWithdrawSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_revokePendingCap {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4))
    (hsel : selIs I (metaMorphoV1_1SelBytes 5)) :
    dispatchMsg contract I.calldata = some revokePendingCapTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition]) (post := [totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := revokePendingCapTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
  · rw [revokePendingCapSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_totalSupply {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5))
    (hsel : selIs I (metaMorphoV1_1SelBytes 6)) :
    dispatchMsg contract I.calldata = some totalSupplyTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition]) (post := [revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := totalSupplyTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
  · rw [totalSupplySelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_revokePendingGuardian {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6))
    (hsel : selIs I (metaMorphoV1_1SelBytes 7)) :
    dispatchMsg contract I.calldata = some revokePendingGuardianTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition]) (post := [lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := revokePendingGuardianTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
  · rw [revokePendingGuardianSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_lostAssets {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7))
    (hsel : selIs I (metaMorphoV1_1SelBytes 8)) :
    dispatchMsg contract I.calldata = some lostAssetsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition]) (post := [transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := lostAssetsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
  · rw [lostAssetsSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_transferFrom {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8))
    (hsel : selIs I (metaMorphoV1_1SelBytes 9)) :
    dispatchMsg contract I.calldata = some transferFromTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition]) (post := [setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := transferFromTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [lostAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
  · rw [transferFromSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setSupplyQueue {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9))
    (hsel : selIs I (metaMorphoV1_1SelBytes 10)) :
    dispatchMsg contract I.calldata = some setSupplyQueueTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition]) (post := [setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setSupplyQueueTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [lostAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
  · rw [setSupplyQueueSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setSkimRecipient {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10))
    (hsel : selIs I (metaMorphoV1_1SelBytes 11)) :
    dispatchMsg contract I.calldata = some setSkimRecipientTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition]) (post := [decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setSkimRecipientTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [lostAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setSupplyQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
  · rw [setSkimRecipientSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_decimals {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11))
    (hsel : selIs I (metaMorphoV1_1SelBytes 12)) :
    dispatchMsg contract I.calldata = some decimalsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition]) (post := [withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := decimalsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [lostAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setSupplyQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [setSkimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
  · rw [decimalsSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_withdrawQueueLength {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12))
    (hsel : selIs I (metaMorphoV1_1SelBytes 13)) :
    dispatchMsg contract I.calldata = some withdrawQueueLengthTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition]) (post := [dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := withdrawQueueLengthTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [lostAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setSupplyQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [setSkimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
  · rw [withdrawQueueLengthSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_dOMAIN_SEPARATOR {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13))
    (hsel : selIs I (metaMorphoV1_1SelBytes 14)) :
    dispatchMsg contract I.calldata = some dOMAIN_SEPARATORTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition]) (post := [skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := dOMAIN_SEPARATORTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [lostAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setSupplyQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [setSkimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [withdrawQueueLengthSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
  · rw [dOMAIN_SEPARATORSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_skimRecipient {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14))
    (hsel : selIs I (metaMorphoV1_1SelBytes 15)) :
    dispatchMsg contract I.calldata = some skimRecipientTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition]) (post := [assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := skimRecipientTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [totalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [nameSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [convertToAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [approveSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [previewWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [revokePendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [totalSupplySelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [revokePendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [lostAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [transferFromSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [setSupplyQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [setSkimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [decimalsSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [withdrawQueueLengthSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [dOMAIN_SEPARATORSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
  · rw [skimRecipientSelectorOf]; exact hsel

end Benchmarks.Morpho.MetaMorphoV1_1
