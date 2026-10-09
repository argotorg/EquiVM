import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! ## Solm dispatch: which transition a selector reaches -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

theorem metaMorphoV1_1Dispatch_renounceOwnership {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31))
    (hsel : selIs I (metaMorphoV1_1SelBytes 32)) :
    dispatchMsg contract I.calldata = some renounceOwnershipTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition]) (post := [submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := renounceOwnershipTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
  · rw [renounceOwnershipSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_submitTimelock {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32))
    (hsel : selIs I (metaMorphoV1_1SelBytes 33)) :
    dispatchMsg contract I.calldata = some submitTimelockTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition]) (post := [reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := submitTimelockTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
  · rw [submitTimelockSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_reallocate {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33))
    (hsel : selIs I (metaMorphoV1_1SelBytes 34)) :
    dispatchMsg contract I.calldata = some reallocateTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition]) (post := [pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := reallocateTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
  · rw [reallocateSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_pendingGuardian {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34))
    (hsel : selIs I (metaMorphoV1_1SelBytes 35)) :
    dispatchMsg contract I.calldata = some pendingGuardianTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition]) (post := [acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := pendingGuardianTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
  · rw [pendingGuardianSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_acceptOwnership {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35))
    (hsel : selIs I (metaMorphoV1_1SelBytes 36)) :
    dispatchMsg contract I.calldata = some acceptOwnershipTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition]) (post := [pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := acceptOwnershipTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
  · rw [acceptOwnershipSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_pendingTimelock {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36))
    (hsel : selIs I (metaMorphoV1_1SelBytes 37)) :
    dispatchMsg contract I.calldata = some pendingTimelockTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition]) (post := [noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := pendingTimelockTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
  · rw [pendingTimelockSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_nonces {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37))
    (hsel : selIs I (metaMorphoV1_1SelBytes 38)) :
    dispatchMsg contract I.calldata = some noncesTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition]) (post := [submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := noncesTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
  · rw [noncesSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_submitMarketRemoval {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38))
    (hsel : selIs I (metaMorphoV1_1SelBytes 39)) :
    dispatchMsg contract I.calldata = some submitMarketRemovalTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition]) (post := [eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := submitMarketRemovalTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
  · rw [submitMarketRemovalSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_eip712Domain {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39))
    (hsel : selIs I (metaMorphoV1_1SelBytes 40)) :
    dispatchMsg contract I.calldata = some eip712DomainTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition]) (post := [acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := eip712DomainTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
  · rw [eip712DomainSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_acceptTimelock {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40))
    (hsel : selIs I (metaMorphoV1_1SelBytes 41)) :
    dispatchMsg contract I.calldata = some acceptTimelockTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition]) (post := [ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := acceptTimelockTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [eip712DomainSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
  · rw [acceptTimelockSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_owner {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41))
    (hsel : selIs I (metaMorphoV1_1SelBytes 42)) :
    dispatchMsg contract I.calldata = some ownerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition]) (post := [mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := ownerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [eip712DomainSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [acceptTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
  · rw [ownerSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_mint {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42))
    (hsel : selIs I (metaMorphoV1_1SelBytes 43)) :
    dispatchMsg contract I.calldata = some mintTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition]) (post := [symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := mintTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [eip712DomainSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [acceptTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
  · rw [mintSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_symbol {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43))
    (hsel : selIs I (metaMorphoV1_1SelBytes 44)) :
    dispatchMsg contract I.calldata = some symbolTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition]) (post := [submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := symbolTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [eip712DomainSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [acceptTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
  · rw [symbolSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_submitGuardian {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44))
    (hsel : selIs I (metaMorphoV1_1SelBytes 45)) :
    dispatchMsg contract I.calldata = some submitGuardianTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition]) (post := [supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := submitGuardianTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [eip712DomainSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [acceptTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
  · rw [submitGuardianSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_supplyQueueLength {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45))
    (hsel : selIs I (metaMorphoV1_1SelBytes 46)) :
    dispatchMsg contract I.calldata = some supplyQueueLengthTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition]) (post := [pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := supplyQueueLengthTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [eip712DomainSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [acceptTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [submitGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
  · rw [supplyQueueLengthSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_pendingCap {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46))
    (hsel : selIs I (metaMorphoV1_1SelBytes 47)) :
    dispatchMsg contract I.calldata = some pendingCapTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition]) (post := [acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := pendingCapTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [balanceOfSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [renounceOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [submitTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [reallocateSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [pendingGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [acceptOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [pendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [noncesSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [submitMarketRemovalSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [eip712DomainSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [acceptTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [ownerSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [mintSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [symbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [submitGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [supplyQueueLengthSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
  · rw [pendingCapSelectorOf]; exact hsel

end Benchmarks.Morpho.MetaMorphoV1_1
