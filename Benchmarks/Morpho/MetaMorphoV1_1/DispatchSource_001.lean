import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! ## Solm dispatch: which transition a selector reaches -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

theorem metaMorphoV1_1Dispatch_asset {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15))
    (hsel : selIs I (metaMorphoV1_1SelBytes 16)) :
    dispatchMsg contract I.calldata = some assetTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition]) (post := [mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := assetTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
  · rw [assetSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_mORPHO {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16))
    (hsel : selIs I (metaMorphoV1_1SelBytes 17)) :
    dispatchMsg contract I.calldata = some mORPHOTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition]) (post := [submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := mORPHOTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
  · rw [mORPHOSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_submitCap {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17))
    (hsel : selIs I (metaMorphoV1_1SelBytes 18)) :
    dispatchMsg contract I.calldata = some submitCapTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition]) (post := [maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := submitCapTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
  · rw [submitCapSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_maxDeposit {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18))
    (hsel : selIs I (metaMorphoV1_1SelBytes 19)) :
    dispatchMsg contract I.calldata = some maxDepositTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition]) (post := [updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := maxDepositTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
  · rw [maxDepositSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_updateWithdrawQueue {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19))
    (hsel : selIs I (metaMorphoV1_1SelBytes 20)) :
    dispatchMsg contract I.calldata = some updateWithdrawQueueTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition]) (post := [guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := updateWithdrawQueueTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
  · rw [updateWithdrawQueueSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_guardian {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20))
    (hsel : selIs I (metaMorphoV1_1SelBytes 21)) :
    dispatchMsg contract I.calldata = some guardianTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition]) (post := [feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := guardianTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
  · rw [guardianSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_feeRecipient {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21))
    (hsel : selIs I (metaMorphoV1_1SelBytes 22)) :
    dispatchMsg contract I.calldata = some feeRecipientTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition]) (post := [revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := feeRecipientTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
  · rw [feeRecipientSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_revokePendingMarketRemoval {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22))
    (hsel : selIs I (metaMorphoV1_1SelBytes 23)) :
    dispatchMsg contract I.calldata = some revokePendingMarketRemovalTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition]) (post := [previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := revokePendingMarketRemovalTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
  · rw [revokePendingMarketRemovalSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_previewRedeem {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23))
    (hsel : selIs I (metaMorphoV1_1SelBytes 24)) :
    dispatchMsg contract I.calldata = some previewRedeemTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition]) (post := [isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := previewRedeemTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
  · rw [previewRedeemSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_isAllocator {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24))
    (hsel : selIs I (metaMorphoV1_1SelBytes 25)) :
    dispatchMsg contract I.calldata = some isAllocatorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition]) (post := [lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := isAllocatorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
  · rw [isAllocatorSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_lastTotalAssets {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25))
    (hsel : selIs I (metaMorphoV1_1SelBytes 26)) :
    dispatchMsg contract I.calldata = some lastTotalAssetsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition]) (post := [withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := lastTotalAssetsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
  · rw [lastTotalAssetsSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_withdrawQueue {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26))
    (hsel : selIs I (metaMorphoV1_1SelBytes 27)) :
    dispatchMsg contract I.calldata = some withdrawQueueTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition]) (post := [setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := withdrawQueueTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [lastTotalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
  · rw [withdrawQueueSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setFee {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27))
    (hsel : selIs I (metaMorphoV1_1SelBytes 28)) :
    dispatchMsg contract I.calldata = some setFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition]) (post := [depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [lastTotalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [withdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
  · rw [setFeeSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_deposit {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28))
    (hsel : selIs I (metaMorphoV1_1SelBytes 29)) :
    dispatchMsg contract I.calldata = some depositTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition]) (post := [acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := depositTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [lastTotalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [withdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [setFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
  · rw [depositSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_acceptCap {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29))
    (hsel : selIs I (metaMorphoV1_1SelBytes 30)) :
    dispatchMsg contract I.calldata = some acceptCapTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition]) (post := [balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := acceptCapTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [lastTotalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [withdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [setFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [depositSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
  · rw [acceptCapSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_balanceOf {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30))
    (hsel : selIs I (metaMorphoV1_1SelBytes 31)) :
    dispatchMsg contract I.calldata = some balanceOfTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition]) (post := [renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := balanceOfTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [skimRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [assetSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [mORPHOSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [submitCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [maxDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [updateWithdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [guardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [revokePendingMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [previewRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [isAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [lastTotalAssetsSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [withdrawQueueSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [setFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [depositSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [acceptCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
  · rw [balanceOfSelectorOf]; exact hsel

end Benchmarks.Morpho.MetaMorphoV1_1
