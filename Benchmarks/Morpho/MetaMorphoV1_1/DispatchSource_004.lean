import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! ## Solm dispatch: which transition a selector reaches -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

theorem metaMorphoV1_1Dispatch_timelock {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63))
    (hsel : selIs I (metaMorphoV1_1SelBytes 64)) :
    dispatchMsg contract I.calldata = some timelockTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition]) (post := [permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := timelockTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
  · rw [timelockSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_permit {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64))
    (hsel : selIs I (metaMorphoV1_1SelBytes 65)) :
    dispatchMsg contract I.calldata = some permitTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition]) (post := [maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := permitTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
  · rw [permitSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_maxRedeem {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65))
    (hsel : selIs I (metaMorphoV1_1SelBytes 66)) :
    dispatchMsg contract I.calldata = some maxRedeemTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition]) (post := [allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := maxRedeemTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
  · rw [maxRedeemSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_allowance {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66))
    (hsel : selIs I (metaMorphoV1_1SelBytes 67)) :
    dispatchMsg contract I.calldata = some allowanceTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition]) (post := [feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := allowanceTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
  · rw [allowanceSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_fee {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67))
    (hsel : selIs I (metaMorphoV1_1SelBytes 68)) :
    dispatchMsg contract I.calldata = some feeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition]) (post := [pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := feeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
  · rw [feeSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_pendingOwner {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67)) (h68 : ¬ selIs I (metaMorphoV1_1SelBytes 68))
    (hsel : selIs I (metaMorphoV1_1SelBytes 69)) :
    dispatchMsg contract I.calldata = some pendingOwnerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition]) (post := [curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := pendingOwnerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
    · rw [feeSelectorOf]; exact Bool.eq_false_of_not_eq_true h68
  · rw [pendingOwnerSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_curator {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67)) (h68 : ¬ selIs I (metaMorphoV1_1SelBytes 68)) (h69 : ¬ selIs I (metaMorphoV1_1SelBytes 69))
    (hsel : selIs I (metaMorphoV1_1SelBytes 70)) :
    dispatchMsg contract I.calldata = some curatorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition]) (post := [setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := curatorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
    · rw [feeSelectorOf]; exact Bool.eq_false_of_not_eq_true h68
    · rw [pendingOwnerSelectorOf]; exact Bool.eq_false_of_not_eq_true h69
  · rw [curatorSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setFeeRecipient {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67)) (h68 : ¬ selIs I (metaMorphoV1_1SelBytes 68)) (h69 : ¬ selIs I (metaMorphoV1_1SelBytes 69)) (h70 : ¬ selIs I (metaMorphoV1_1SelBytes 70))
    (hsel : selIs I (metaMorphoV1_1SelBytes 71)) :
    dispatchMsg contract I.calldata = some setFeeRecipientTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition]) (post := [setCuratorTransition, previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setFeeRecipientTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
    · rw [feeSelectorOf]; exact Bool.eq_false_of_not_eq_true h68
    · rw [pendingOwnerSelectorOf]; exact Bool.eq_false_of_not_eq_true h69
    · rw [curatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h70
  · rw [setFeeRecipientSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_setCurator {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67)) (h68 : ¬ selIs I (metaMorphoV1_1SelBytes 68)) (h69 : ¬ selIs I (metaMorphoV1_1SelBytes 69)) (h70 : ¬ selIs I (metaMorphoV1_1SelBytes 70)) (h71 : ¬ selIs I (metaMorphoV1_1SelBytes 71))
    (hsel : selIs I (metaMorphoV1_1SelBytes 72)) :
    dispatchMsg contract I.calldata = some setCuratorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition]) (post := [previewDepositTransition, transferOwnershipTransition, supplyQueueTransition])
    (ti := setCuratorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
    · rw [feeSelectorOf]; exact Bool.eq_false_of_not_eq_true h68
    · rw [pendingOwnerSelectorOf]; exact Bool.eq_false_of_not_eq_true h69
    · rw [curatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h70
    · rw [setFeeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h71
  · rw [setCuratorSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_previewDeposit {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67)) (h68 : ¬ selIs I (metaMorphoV1_1SelBytes 68)) (h69 : ¬ selIs I (metaMorphoV1_1SelBytes 69)) (h70 : ¬ selIs I (metaMorphoV1_1SelBytes 70)) (h71 : ¬ selIs I (metaMorphoV1_1SelBytes 71)) (h72 : ¬ selIs I (metaMorphoV1_1SelBytes 72))
    (hsel : selIs I (metaMorphoV1_1SelBytes 73)) :
    dispatchMsg contract I.calldata = some previewDepositTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition]) (post := [transferOwnershipTransition, supplyQueueTransition])
    (ti := previewDepositTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
    · rw [feeSelectorOf]; exact Bool.eq_false_of_not_eq_true h68
    · rw [pendingOwnerSelectorOf]; exact Bool.eq_false_of_not_eq_true h69
    · rw [curatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h70
    · rw [setFeeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h71
    · rw [setCuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h72
  · rw [previewDepositSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_transferOwnership {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67)) (h68 : ¬ selIs I (metaMorphoV1_1SelBytes 68)) (h69 : ¬ selIs I (metaMorphoV1_1SelBytes 69)) (h70 : ¬ selIs I (metaMorphoV1_1SelBytes 70)) (h71 : ¬ selIs I (metaMorphoV1_1SelBytes 71)) (h72 : ¬ selIs I (metaMorphoV1_1SelBytes 72)) (h73 : ¬ selIs I (metaMorphoV1_1SelBytes 73))
    (hsel : selIs I (metaMorphoV1_1SelBytes 74)) :
    dispatchMsg contract I.calldata = some transferOwnershipTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition]) (post := [supplyQueueTransition])
    (ti := transferOwnershipTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
    · rw [feeSelectorOf]; exact Bool.eq_false_of_not_eq_true h68
    · rw [pendingOwnerSelectorOf]; exact Bool.eq_false_of_not_eq_true h69
    · rw [curatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h70
    · rw [setFeeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h71
    · rw [setCuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h72
    · rw [previewDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h73
  · rw [transferOwnershipSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_supplyQueue {I : ExecutionEnv} (h0 : ¬ selIs I (metaMorphoV1_1SelBytes 0)) (h1 : ¬ selIs I (metaMorphoV1_1SelBytes 1)) (h2 : ¬ selIs I (metaMorphoV1_1SelBytes 2)) (h3 : ¬ selIs I (metaMorphoV1_1SelBytes 3)) (h4 : ¬ selIs I (metaMorphoV1_1SelBytes 4)) (h5 : ¬ selIs I (metaMorphoV1_1SelBytes 5)) (h6 : ¬ selIs I (metaMorphoV1_1SelBytes 6)) (h7 : ¬ selIs I (metaMorphoV1_1SelBytes 7)) (h8 : ¬ selIs I (metaMorphoV1_1SelBytes 8)) (h9 : ¬ selIs I (metaMorphoV1_1SelBytes 9)) (h10 : ¬ selIs I (metaMorphoV1_1SelBytes 10)) (h11 : ¬ selIs I (metaMorphoV1_1SelBytes 11)) (h12 : ¬ selIs I (metaMorphoV1_1SelBytes 12)) (h13 : ¬ selIs I (metaMorphoV1_1SelBytes 13)) (h14 : ¬ selIs I (metaMorphoV1_1SelBytes 14)) (h15 : ¬ selIs I (metaMorphoV1_1SelBytes 15)) (h16 : ¬ selIs I (metaMorphoV1_1SelBytes 16)) (h17 : ¬ selIs I (metaMorphoV1_1SelBytes 17)) (h18 : ¬ selIs I (metaMorphoV1_1SelBytes 18)) (h19 : ¬ selIs I (metaMorphoV1_1SelBytes 19)) (h20 : ¬ selIs I (metaMorphoV1_1SelBytes 20)) (h21 : ¬ selIs I (metaMorphoV1_1SelBytes 21)) (h22 : ¬ selIs I (metaMorphoV1_1SelBytes 22)) (h23 : ¬ selIs I (metaMorphoV1_1SelBytes 23)) (h24 : ¬ selIs I (metaMorphoV1_1SelBytes 24)) (h25 : ¬ selIs I (metaMorphoV1_1SelBytes 25)) (h26 : ¬ selIs I (metaMorphoV1_1SelBytes 26)) (h27 : ¬ selIs I (metaMorphoV1_1SelBytes 27)) (h28 : ¬ selIs I (metaMorphoV1_1SelBytes 28)) (h29 : ¬ selIs I (metaMorphoV1_1SelBytes 29)) (h30 : ¬ selIs I (metaMorphoV1_1SelBytes 30)) (h31 : ¬ selIs I (metaMorphoV1_1SelBytes 31)) (h32 : ¬ selIs I (metaMorphoV1_1SelBytes 32)) (h33 : ¬ selIs I (metaMorphoV1_1SelBytes 33)) (h34 : ¬ selIs I (metaMorphoV1_1SelBytes 34)) (h35 : ¬ selIs I (metaMorphoV1_1SelBytes 35)) (h36 : ¬ selIs I (metaMorphoV1_1SelBytes 36)) (h37 : ¬ selIs I (metaMorphoV1_1SelBytes 37)) (h38 : ¬ selIs I (metaMorphoV1_1SelBytes 38)) (h39 : ¬ selIs I (metaMorphoV1_1SelBytes 39)) (h40 : ¬ selIs I (metaMorphoV1_1SelBytes 40)) (h41 : ¬ selIs I (metaMorphoV1_1SelBytes 41)) (h42 : ¬ selIs I (metaMorphoV1_1SelBytes 42)) (h43 : ¬ selIs I (metaMorphoV1_1SelBytes 43)) (h44 : ¬ selIs I (metaMorphoV1_1SelBytes 44)) (h45 : ¬ selIs I (metaMorphoV1_1SelBytes 45)) (h46 : ¬ selIs I (metaMorphoV1_1SelBytes 46)) (h47 : ¬ selIs I (metaMorphoV1_1SelBytes 47)) (h48 : ¬ selIs I (metaMorphoV1_1SelBytes 48)) (h49 : ¬ selIs I (metaMorphoV1_1SelBytes 49)) (h50 : ¬ selIs I (metaMorphoV1_1SelBytes 50)) (h51 : ¬ selIs I (metaMorphoV1_1SelBytes 51)) (h52 : ¬ selIs I (metaMorphoV1_1SelBytes 52)) (h53 : ¬ selIs I (metaMorphoV1_1SelBytes 53)) (h54 : ¬ selIs I (metaMorphoV1_1SelBytes 54)) (h55 : ¬ selIs I (metaMorphoV1_1SelBytes 55)) (h56 : ¬ selIs I (metaMorphoV1_1SelBytes 56)) (h57 : ¬ selIs I (metaMorphoV1_1SelBytes 57)) (h58 : ¬ selIs I (metaMorphoV1_1SelBytes 58)) (h59 : ¬ selIs I (metaMorphoV1_1SelBytes 59)) (h60 : ¬ selIs I (metaMorphoV1_1SelBytes 60)) (h61 : ¬ selIs I (metaMorphoV1_1SelBytes 61)) (h62 : ¬ selIs I (metaMorphoV1_1SelBytes 62)) (h63 : ¬ selIs I (metaMorphoV1_1SelBytes 63)) (h64 : ¬ selIs I (metaMorphoV1_1SelBytes 64)) (h65 : ¬ selIs I (metaMorphoV1_1SelBytes 65)) (h66 : ¬ selIs I (metaMorphoV1_1SelBytes 66)) (h67 : ¬ selIs I (metaMorphoV1_1SelBytes 67)) (h68 : ¬ selIs I (metaMorphoV1_1SelBytes 68)) (h69 : ¬ selIs I (metaMorphoV1_1SelBytes 69)) (h70 : ¬ selIs I (metaMorphoV1_1SelBytes 70)) (h71 : ¬ selIs I (metaMorphoV1_1SelBytes 71)) (h72 : ¬ selIs I (metaMorphoV1_1SelBytes 72)) (h73 : ¬ selIs I (metaMorphoV1_1SelBytes 73)) (h74 : ¬ selIs I (metaMorphoV1_1SelBytes 74))
    (hsel : selIs I (metaMorphoV1_1SelBytes 75)) :
    dispatchMsg contract I.calldata = some supplyQueueTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [totalAssetsTransition, nameTransition, convertToAssetsTransition, approveTransition, previewWithdrawTransition, revokePendingCapTransition, totalSupplyTransition, revokePendingGuardianTransition, lostAssetsTransition, transferFromTransition, setSupplyQueueTransition, setSkimRecipientTransition, decimalsTransition, withdrawQueueLengthTransition, dOMAIN_SEPARATORTransition, skimRecipientTransition, assetTransition, mORPHOTransition, submitCapTransition, maxDepositTransition, updateWithdrawQueueTransition, guardianTransition, feeRecipientTransition, revokePendingMarketRemovalTransition, previewRedeemTransition, isAllocatorTransition, lastTotalAssetsTransition, withdrawQueueTransition, setFeeTransition, depositTransition, acceptCapTransition, balanceOfTransition, renounceOwnershipTransition, submitTimelockTransition, reallocateTransition, pendingGuardianTransition, acceptOwnershipTransition, pendingTimelockTransition, noncesTransition, submitMarketRemovalTransition, eip712DomainTransition, acceptTimelockTransition, ownerTransition, mintTransition, symbolTransition, submitGuardianTransition, supplyQueueLengthTransition, pendingCapTransition, acceptGuardianTransition, transferTransition, multicallTransition, dECIMALS_OFFSETTransition, setIsAllocatorTransition, previewMintTransition, withdrawTransition, setSymbolTransition, redeemTransition, skimTransition, setNameTransition, maxMintTransition, convertToSharesTransition, revokePendingTimelockTransition, configTransition, maxWithdrawTransition, timelockTransition, permitTransition, maxRedeemTransition, allowanceTransition, feeTransition, pendingOwnerTransition, curatorTransition, setFeeRecipientTransition, setCuratorTransition, previewDepositTransition, transferOwnershipTransition]) (post := [])
    (ti := supplyQueueTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [maxWithdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h63
    · rw [timelockSelectorOf]; exact Bool.eq_false_of_not_eq_true h64
    · rw [permitSelectorOf]; exact Bool.eq_false_of_not_eq_true h65
    · rw [maxRedeemSelectorOf]; exact Bool.eq_false_of_not_eq_true h66
    · rw [allowanceSelectorOf]; exact Bool.eq_false_of_not_eq_true h67
    · rw [feeSelectorOf]; exact Bool.eq_false_of_not_eq_true h68
    · rw [pendingOwnerSelectorOf]; exact Bool.eq_false_of_not_eq_true h69
    · rw [curatorSelectorOf]; exact Bool.eq_false_of_not_eq_true h70
    · rw [setFeeRecipientSelectorOf]; exact Bool.eq_false_of_not_eq_true h71
    · rw [setCuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h72
    · rw [previewDepositSelectorOf]; exact Bool.eq_false_of_not_eq_true h73
    · rw [transferOwnershipSelectorOf]; exact Bool.eq_false_of_not_eq_true h74
  · rw [supplyQueueSelectorOf]; exact hsel

theorem metaMorphoV1_1Dispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd, transitions_eq]
  refine dispatchList_none_short _ ?_ h
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [totalAssetsSelectorOf]; rfl
  · rw [nameSelectorOf]; rfl
  · rw [convertToAssetsSelectorOf]; rfl
  · rw [approveSelectorOf]; rfl
  · rw [previewWithdrawSelectorOf]; rfl
  · rw [revokePendingCapSelectorOf]; rfl
  · rw [totalSupplySelectorOf]; rfl
  · rw [revokePendingGuardianSelectorOf]; rfl
  · rw [lostAssetsSelectorOf]; rfl
  · rw [transferFromSelectorOf]; rfl
  · rw [setSupplyQueueSelectorOf]; rfl
  · rw [setSkimRecipientSelectorOf]; rfl
  · rw [decimalsSelectorOf]; rfl
  · rw [withdrawQueueLengthSelectorOf]; rfl
  · rw [dOMAIN_SEPARATORSelectorOf]; rfl
  · rw [skimRecipientSelectorOf]; rfl
  · rw [assetSelectorOf]; rfl
  · rw [mORPHOSelectorOf]; rfl
  · rw [submitCapSelectorOf]; rfl
  · rw [maxDepositSelectorOf]; rfl
  · rw [updateWithdrawQueueSelectorOf]; rfl
  · rw [guardianSelectorOf]; rfl
  · rw [feeRecipientSelectorOf]; rfl
  · rw [revokePendingMarketRemovalSelectorOf]; rfl
  · rw [previewRedeemSelectorOf]; rfl
  · rw [isAllocatorSelectorOf]; rfl
  · rw [lastTotalAssetsSelectorOf]; rfl
  · rw [withdrawQueueSelectorOf]; rfl
  · rw [setFeeSelectorOf]; rfl
  · rw [depositSelectorOf]; rfl
  · rw [acceptCapSelectorOf]; rfl
  · rw [balanceOfSelectorOf]; rfl
  · rw [renounceOwnershipSelectorOf]; rfl
  · rw [submitTimelockSelectorOf]; rfl
  · rw [reallocateSelectorOf]; rfl
  · rw [pendingGuardianSelectorOf]; rfl
  · rw [acceptOwnershipSelectorOf]; rfl
  · rw [pendingTimelockSelectorOf]; rfl
  · rw [noncesSelectorOf]; rfl
  · rw [submitMarketRemovalSelectorOf]; rfl
  · rw [eip712DomainSelectorOf]; rfl
  · rw [acceptTimelockSelectorOf]; rfl
  · rw [ownerSelectorOf]; rfl
  · rw [mintSelectorOf]; rfl
  · rw [symbolSelectorOf]; rfl
  · rw [submitGuardianSelectorOf]; rfl
  · rw [supplyQueueLengthSelectorOf]; rfl
  · rw [pendingCapSelectorOf]; rfl
  · rw [acceptGuardianSelectorOf]; rfl
  · rw [transferSelectorOf]; rfl
  · rw [multicallSelectorOf]; rfl
  · rw [dECIMALS_OFFSETSelectorOf]; rfl
  · rw [setIsAllocatorSelectorOf]; rfl
  · rw [previewMintSelectorOf]; rfl
  · rw [withdrawSelectorOf]; rfl
  · rw [setSymbolSelectorOf]; rfl
  · rw [redeemSelectorOf]; rfl
  · rw [skimSelectorOf]; rfl
  · rw [setNameSelectorOf]; rfl
  · rw [maxMintSelectorOf]; rfl
  · rw [convertToSharesSelectorOf]; rfl
  · rw [revokePendingTimelockSelectorOf]; rfl
  · rw [configSelectorOf]; rfl
  · rw [maxWithdrawSelectorOf]; rfl
  · rw [timelockSelectorOf]; rfl
  · rw [permitSelectorOf]; rfl
  · rw [maxRedeemSelectorOf]; rfl
  · rw [allowanceSelectorOf]; rfl
  · rw [feeSelectorOf]; rfl
  · rw [pendingOwnerSelectorOf]; rfl
  · rw [curatorSelectorOf]; rfl
  · rw [setFeeRecipientSelectorOf]; rfl
  · rw [setCuratorSelectorOf]; rfl
  · rw [previewDepositSelectorOf]; rfl
  · rw [transferOwnershipSelectorOf]; rfl
  · rw [supplyQueueSelectorOf]; rfl

theorem metaMorphoV1_1Dispatch_none_nomatch {I : ExecutionEnv}
    (hnm : ∀ i, i < 76 → (metaMorphoV1_1SelBytes i == I.calldata.extract 0 4) = false) :
    dispatchMsg contract I.calldata = none := by
  refine dispatchMsg_none_of_all_ne (contract := contract) (cd := I.calldata) (by rfl) (by rfl) ?_
  intro t ht
  rw [transitions_eq] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [totalAssetsSelectorOf]; exact hnm 0 (by omega)
  · rw [nameSelectorOf]; exact hnm 1 (by omega)
  · rw [convertToAssetsSelectorOf]; exact hnm 2 (by omega)
  · rw [approveSelectorOf]; exact hnm 3 (by omega)
  · rw [previewWithdrawSelectorOf]; exact hnm 4 (by omega)
  · rw [revokePendingCapSelectorOf]; exact hnm 5 (by omega)
  · rw [totalSupplySelectorOf]; exact hnm 6 (by omega)
  · rw [revokePendingGuardianSelectorOf]; exact hnm 7 (by omega)
  · rw [lostAssetsSelectorOf]; exact hnm 8 (by omega)
  · rw [transferFromSelectorOf]; exact hnm 9 (by omega)
  · rw [setSupplyQueueSelectorOf]; exact hnm 10 (by omega)
  · rw [setSkimRecipientSelectorOf]; exact hnm 11 (by omega)
  · rw [decimalsSelectorOf]; exact hnm 12 (by omega)
  · rw [withdrawQueueLengthSelectorOf]; exact hnm 13 (by omega)
  · rw [dOMAIN_SEPARATORSelectorOf]; exact hnm 14 (by omega)
  · rw [skimRecipientSelectorOf]; exact hnm 15 (by omega)
  · rw [assetSelectorOf]; exact hnm 16 (by omega)
  · rw [mORPHOSelectorOf]; exact hnm 17 (by omega)
  · rw [submitCapSelectorOf]; exact hnm 18 (by omega)
  · rw [maxDepositSelectorOf]; exact hnm 19 (by omega)
  · rw [updateWithdrawQueueSelectorOf]; exact hnm 20 (by omega)
  · rw [guardianSelectorOf]; exact hnm 21 (by omega)
  · rw [feeRecipientSelectorOf]; exact hnm 22 (by omega)
  · rw [revokePendingMarketRemovalSelectorOf]; exact hnm 23 (by omega)
  · rw [previewRedeemSelectorOf]; exact hnm 24 (by omega)
  · rw [isAllocatorSelectorOf]; exact hnm 25 (by omega)
  · rw [lastTotalAssetsSelectorOf]; exact hnm 26 (by omega)
  · rw [withdrawQueueSelectorOf]; exact hnm 27 (by omega)
  · rw [setFeeSelectorOf]; exact hnm 28 (by omega)
  · rw [depositSelectorOf]; exact hnm 29 (by omega)
  · rw [acceptCapSelectorOf]; exact hnm 30 (by omega)
  · rw [balanceOfSelectorOf]; exact hnm 31 (by omega)
  · rw [renounceOwnershipSelectorOf]; exact hnm 32 (by omega)
  · rw [submitTimelockSelectorOf]; exact hnm 33 (by omega)
  · rw [reallocateSelectorOf]; exact hnm 34 (by omega)
  · rw [pendingGuardianSelectorOf]; exact hnm 35 (by omega)
  · rw [acceptOwnershipSelectorOf]; exact hnm 36 (by omega)
  · rw [pendingTimelockSelectorOf]; exact hnm 37 (by omega)
  · rw [noncesSelectorOf]; exact hnm 38 (by omega)
  · rw [submitMarketRemovalSelectorOf]; exact hnm 39 (by omega)
  · rw [eip712DomainSelectorOf]; exact hnm 40 (by omega)
  · rw [acceptTimelockSelectorOf]; exact hnm 41 (by omega)
  · rw [ownerSelectorOf]; exact hnm 42 (by omega)
  · rw [mintSelectorOf]; exact hnm 43 (by omega)
  · rw [symbolSelectorOf]; exact hnm 44 (by omega)
  · rw [submitGuardianSelectorOf]; exact hnm 45 (by omega)
  · rw [supplyQueueLengthSelectorOf]; exact hnm 46 (by omega)
  · rw [pendingCapSelectorOf]; exact hnm 47 (by omega)
  · rw [acceptGuardianSelectorOf]; exact hnm 48 (by omega)
  · rw [transferSelectorOf]; exact hnm 49 (by omega)
  · rw [multicallSelectorOf]; exact hnm 50 (by omega)
  · rw [dECIMALS_OFFSETSelectorOf]; exact hnm 51 (by omega)
  · rw [setIsAllocatorSelectorOf]; exact hnm 52 (by omega)
  · rw [previewMintSelectorOf]; exact hnm 53 (by omega)
  · rw [withdrawSelectorOf]; exact hnm 54 (by omega)
  · rw [setSymbolSelectorOf]; exact hnm 55 (by omega)
  · rw [redeemSelectorOf]; exact hnm 56 (by omega)
  · rw [skimSelectorOf]; exact hnm 57 (by omega)
  · rw [setNameSelectorOf]; exact hnm 58 (by omega)
  · rw [maxMintSelectorOf]; exact hnm 59 (by omega)
  · rw [convertToSharesSelectorOf]; exact hnm 60 (by omega)
  · rw [revokePendingTimelockSelectorOf]; exact hnm 61 (by omega)
  · rw [configSelectorOf]; exact hnm 62 (by omega)
  · rw [maxWithdrawSelectorOf]; exact hnm 63 (by omega)
  · rw [timelockSelectorOf]; exact hnm 64 (by omega)
  · rw [permitSelectorOf]; exact hnm 65 (by omega)
  · rw [maxRedeemSelectorOf]; exact hnm 66 (by omega)
  · rw [allowanceSelectorOf]; exact hnm 67 (by omega)
  · rw [feeSelectorOf]; exact hnm 68 (by omega)
  · rw [pendingOwnerSelectorOf]; exact hnm 69 (by omega)
  · rw [curatorSelectorOf]; exact hnm 70 (by omega)
  · rw [setFeeRecipientSelectorOf]; exact hnm 71 (by omega)
  · rw [setCuratorSelectorOf]; exact hnm 72 (by omega)
  · rw [previewDepositSelectorOf]; exact hnm 73 (by omega)
  · rw [transferOwnershipSelectorOf]; exact hnm 74 (by omega)
  · rw [supplyQueueSelectorOf]; exact hnm 75 (by omega)

end Benchmarks.Morpho.MetaMorphoV1_1
