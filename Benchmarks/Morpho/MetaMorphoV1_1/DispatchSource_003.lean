import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! ## Solm dispatch: which transition a selector reaches -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

theorem metaMorphoV1_1Dispatch_acceptGuardian {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47))
    (hsel : selIs I (metaMorphoV1_1SelBytes 48)) :
    dispatchMsg contract I.calldata = some acceptGuardianTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition]) (post := [transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := acceptGuardianTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
  · rw [acceptGuardianSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_transfer {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48))
    (hsel : selIs I (metaMorphoV1_1SelBytes 49)) :
    dispatchMsg contract I.calldata = some transferTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition]) (post := [multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := transferTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
  · rw [transferSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_multicall {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49))
    (hsel : selIs I (metaMorphoV1_1SelBytes 50)) :
    dispatchMsg contract I.calldata = some multicallTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition]) (post := [dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := multicallTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
  · rw [multicallSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_dECIMALS_OFFSET {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50))
    (hsel : selIs I (metaMorphoV1_1SelBytes 51)) :
    dispatchMsg contract I.calldata = some dECIMALS_OFFSETTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition]) (post := [setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := dECIMALS_OFFSETTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
  · rw [dECIMALS_OFFSETSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setIsAllocator {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51))
    (hsel : selIs I (metaMorphoV1_1SelBytes 52)) :
    dispatchMsg contract I.calldata = some setIsAllocatorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition]) (post := [previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setIsAllocatorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
  · rw [setIsAllocatorSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_previewMint {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52))
    (hsel : selIs I (metaMorphoV1_1SelBytes 53)) :
    dispatchMsg contract I.calldata = some previewMintTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition]) (post := [withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := previewMintTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
  · rw [previewMintSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_withdraw {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53))
    (hsel : selIs I (metaMorphoV1_1SelBytes 54)) :
    dispatchMsg contract I.calldata = some withdrawTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition]) (post := [setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := withdrawTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
  · rw [withdrawSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setSymbol {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54))
    (hsel : selIs I (metaMorphoV1_1SelBytes 55)) :
    dispatchMsg contract I.calldata = some setSymbolTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition]) (post := [redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setSymbolTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
  · rw [setSymbolSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_redeem {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55))
    (hsel : selIs I (metaMorphoV1_1SelBytes 56)) :
    dispatchMsg contract I.calldata = some redeemTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition]) (post := [skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := redeemTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
  · rw [redeemSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_skim {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56))
    (hsel : selIs I (metaMorphoV1_1SelBytes 57)) :
    dispatchMsg contract I.calldata = some skimTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition]) (post := [setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := skimTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
    · rw [redeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h56
  · rw [skimSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setName {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57))
    (hsel : selIs I (metaMorphoV1_1SelBytes 58)) :
    dispatchMsg contract I.calldata = some setNameTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition]) (post := [maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setNameTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
    · rw [redeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h56
    · rw [skimSelectorOf]; exact Bool.eq_false_of_not_eq_true h57
  · rw [setNameSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_maxMint {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58))
    (hsel : selIs I (metaMorphoV1_1SelBytes 59)) :
    dispatchMsg contract I.calldata = some maxMintTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition]) (post := [convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := maxMintTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
    · rw [redeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h56
    · rw [skimSelectorOf]; exact Bool.eq_false_of_not_eq_true h57
    · rw [setNameSelectorOf]; exact Bool.eq_false_of_not_eq_true h58
  · rw [maxMintSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_convertToShares {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59))
    (hsel : selIs I (metaMorphoV1_1SelBytes 60)) :
    dispatchMsg contract I.calldata = some convertToSharesTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition]) (post := [revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := convertToSharesTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
    · rw [redeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h56
    · rw [skimSelectorOf]; exact Bool.eq_false_of_not_eq_true h57
    · rw [setNameSelectorOf]; exact Bool.eq_false_of_not_eq_true h58
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h59
  · rw [convertToSharesSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_revokePendingTimelock {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60))
    (hsel : selIs I (metaMorphoV1_1SelBytes 61)) :
    dispatchMsg contract I.calldata = some revokePendingTimelockTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition]) (post := [configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := revokePendingTimelockTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
    · rw [redeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h56
    · rw [skimSelectorOf]; exact Bool.eq_false_of_not_eq_true h57
    · rw [setNameSelectorOf]; exact Bool.eq_false_of_not_eq_true h58
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h59
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h60
  · rw [revokePendingTimelockSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_config {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61))
    (hsel : selIs I (metaMorphoV1_1SelBytes 62)) :
    dispatchMsg contract I.calldata = some configTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition]) (post := [maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := configTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
    · rw [redeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h56
    · rw [skimSelectorOf]; exact Bool.eq_false_of_not_eq_true h57
    · rw [setNameSelectorOf]; exact Bool.eq_false_of_not_eq_true h58
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h59
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h60
    · rw [revokePendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h61
  · rw [configSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_maxWithdraw {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62))
    (hsel : selIs I (metaMorphoV1_1SelBytes 63)) :
    dispatchMsg contract I.calldata = some maxWithdrawTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition]) (post := [timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := maxWithdrawTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [pendingCapSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [acceptGuardianSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [transferSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [dECIMALS_OFFSETSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setIsAllocatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [previewMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [setSymbolSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
    · rw [redeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h56
    · rw [skimSelectorOf]; exact Bool.eq_false_of_not_eq_true h57
    · rw [setNameSelectorOf]; exact Bool.eq_false_of_not_eq_true h58
    · rw [maxMintSelectorOf]; exact Bool.eq_false_of_not_eq_true h59
    · rw [convertToSharesSelectorOf]; exact Bool.eq_false_of_not_eq_true h60
    · rw [revokePendingTimelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h61
    · rw [configSelectorOf]; exact Bool.eq_false_of_not_eq_true h62
  · rw [maxWithdrawSelectorOf]; exact hsel

end Benchmarks.Morpho.MetaMorphoV1_1
