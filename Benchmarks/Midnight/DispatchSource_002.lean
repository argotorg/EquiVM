import Benchmarks.Midnight.DispatchSource_001

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightDispatch_pendingFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43))
    (hsel : selIs I (midnightSelBytes 44)) :
    dispatchMsg contract I.calldata = some pendingFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition]) (post := [creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := pendingFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
  · rw [pendingFeeSelectorOf]; exact hsel

theorem midnightDispatch_credit {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44))
    (hsel : selIs I (midnightSelBytes 45)) :
    dispatchMsg contract I.calldata = some creditTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition]) (post := [updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := creditTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
  · rw [creditSelectorOf]; exact hsel

theorem midnightDispatch_updatePositionView {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45))
    (hsel : selIs I (midnightSelBytes 46)) :
    dispatchMsg contract I.calldata = some updatePositionViewTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition]) (post := [tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := updatePositionViewTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
  · rw [updatePositionViewSelectorOf]; exact hsel

theorem midnightDispatch_tickSpacing {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46))
    (hsel : selIs I (midnightSelBytes 47)) :
    dispatchMsg contract I.calldata = some tickSpacingTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition]) (post := [lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := tickSpacingTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
  · rw [tickSpacingSelectorOf]; exact hsel

theorem midnightDispatch_lastAccrual {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47))
    (hsel : selIs I (midnightSelBytes 48)) :
    dispatchMsg contract I.calldata = some lastAccrualTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition]) (post := [consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := lastAccrualTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
  · rw [lastAccrualSelectorOf]; exact hsel

theorem midnightDispatch_consumed {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48))
    (hsel : selIs I (midnightSelBytes 49)) :
    dispatchMsg contract I.calldata = some consumedTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition]) (post := [marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := consumedTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
  · rw [consumedSelectorOf]; exact hsel

theorem midnightDispatch_marketState {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48)) (h49 : ¬ selIs I (midnightSelBytes 49))
    (hsel : selIs I (midnightSelBytes 50)) :
    dispatchMsg contract I.calldata = some marketStateTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition]) (post := [collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := marketStateTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [consumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
  · rw [marketStateSelectorOf]; exact hsel

theorem midnightDispatch_collateral {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48)) (h49 : ¬ selIs I (midnightSelBytes 49)) (h50 : ¬ selIs I (midnightSelBytes 50))
    (hsel : selIs I (midnightSelBytes 51)) :
    dispatchMsg contract I.calldata = some collateralTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition]) (post := [setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := collateralTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [consumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [marketStateSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
  · rw [collateralSelectorOf]; exact hsel

theorem midnightDispatch_setConsumed {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48)) (h49 : ¬ selIs I (midnightSelBytes 49)) (h50 : ¬ selIs I (midnightSelBytes 50)) (h51 : ¬ selIs I (midnightSelBytes 51))
    (hsel : selIs I (midnightSelBytes 52)) :
    dispatchMsg contract I.calldata = some setConsumedTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition]) (post := [setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setConsumedTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [consumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [marketStateSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [collateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
  · rw [setConsumedSelectorOf]; exact hsel

theorem midnightDispatch_setMarketTickSpacing {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48)) (h49 : ¬ selIs I (midnightSelBytes 49)) (h50 : ¬ selIs I (midnightSelBytes 50)) (h51 : ¬ selIs I (midnightSelBytes 51)) (h52 : ¬ selIs I (midnightSelBytes 52))
    (hsel : selIs I (midnightSelBytes 53)) :
    dispatchMsg contract I.calldata = some setMarketTickSpacingTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition]) (post := [setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setMarketTickSpacingTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [consumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [marketStateSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [collateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setConsumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
  · rw [setMarketTickSpacingSelectorOf]; exact hsel

theorem midnightDispatch_setTickSpacingSetter {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48)) (h49 : ¬ selIs I (midnightSelBytes 49)) (h50 : ¬ selIs I (midnightSelBytes 50)) (h51 : ¬ selIs I (midnightSelBytes 51)) (h52 : ¬ selIs I (midnightSelBytes 52)) (h53 : ¬ selIs I (midnightSelBytes 53))
    (hsel : selIs I (midnightSelBytes 54)) :
    dispatchMsg contract I.calldata = some setTickSpacingSetterTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition]) (post := [toMarketTransition, continuousFeeCreditTransition])
    (ti := setTickSpacingSetterTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [consumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [marketStateSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [collateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setConsumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [setMarketTickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
  · rw [setTickSpacingSetterSelectorOf]; exact hsel

theorem midnightDispatch_toMarket {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48)) (h49 : ¬ selIs I (midnightSelBytes 49)) (h50 : ¬ selIs I (midnightSelBytes 50)) (h51 : ¬ selIs I (midnightSelBytes 51)) (h52 : ¬ selIs I (midnightSelBytes 52)) (h53 : ¬ selIs I (midnightSelBytes 53)) (h54 : ¬ selIs I (midnightSelBytes 54))
    (hsel : selIs I (midnightSelBytes 55)) :
    dispatchMsg contract I.calldata = some toMarketTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition]) (post := [continuousFeeCreditTransition])
    (ti := toMarketTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [consumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [marketStateSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [collateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setConsumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [setMarketTickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [setTickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
  · rw [toMarketSelectorOf]; exact hsel

theorem midnightDispatch_continuousFeeCredit {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42)) (h43 : ¬ selIs I (midnightSelBytes 43)) (h44 : ¬ selIs I (midnightSelBytes 44)) (h45 : ¬ selIs I (midnightSelBytes 45)) (h46 : ¬ selIs I (midnightSelBytes 46)) (h47 : ¬ selIs I (midnightSelBytes 47)) (h48 : ¬ selIs I (midnightSelBytes 48)) (h49 : ¬ selIs I (midnightSelBytes 49)) (h50 : ¬ selIs I (midnightSelBytes 50)) (h51 : ¬ selIs I (midnightSelBytes 51)) (h52 : ¬ selIs I (midnightSelBytes 52)) (h53 : ¬ selIs I (midnightSelBytes 53)) (h54 : ¬ selIs I (midnightSelBytes 54)) (h55 : ¬ selIs I (midnightSelBytes 55))
    (hsel : selIs I (midnightSelBytes 56)) :
    dispatchMsg contract I.calldata = some continuousFeeCreditTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition]) (post := [])
    (ti := continuousFeeCreditTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
    · rw [flashLoanSelectorOf]; exact Bool.eq_false_of_not_eq_true h9
    · rw [claimableSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h10
    · rw [totalUnitsSelectorOf]; exact Bool.eq_false_of_not_eq_true h11
    · rw [updatePositionSelectorOf]; exact Bool.eq_false_of_not_eq_true h12
    · rw [lossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h13
    · rw [claimContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h14
    · rw [isHealthySelectorOf]; exact Bool.eq_false_of_not_eq_true h15
    · rw [setDefaultSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h16
    · rw [isAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h17
    · rw [takeSelectorOf]; exact Bool.eq_false_of_not_eq_true h18
    · rw [repaySelectorOf]; exact Bool.eq_false_of_not_eq_true h19
    · rw [withdrawableSelectorOf]; exact Bool.eq_false_of_not_eq_true h20
    · rw [feeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h21
    · rw [feeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h22
    · rw [lastLossFactorSelectorOf]; exact Bool.eq_false_of_not_eq_true h23
    · rw [isLiquidationCursorEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h24
    · rw [enableLiquidationCursorSelectorOf]; exact Bool.eq_false_of_not_eq_true h25
    · rw [debtSelectorOf]; exact Bool.eq_false_of_not_eq_true h26
    · rw [positionSelectorOf]; exact Bool.eq_false_of_not_eq_true h27
    · rw [tickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h28
    · rw [setMarketSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h29
    · rw [liquidateSelectorOf]; exact Bool.eq_false_of_not_eq_true h30
    · rw [setConfiguratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h31
    · rw [withdrawCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h32
    · rw [touchMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h33
    · rw [withdrawSelectorOf]; exact Bool.eq_false_of_not_eq_true h34
    · rw [settlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h35
    · rw [multicallSelectorOf]; exact Bool.eq_false_of_not_eq_true h36
    · rw [setFeeSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h37
    · rw [isLltvEnabledSelectorOf]; exact Bool.eq_false_of_not_eq_true h38
    · rw [collateralBitmapSelectorOf]; exact Bool.eq_false_of_not_eq_true h39
    · rw [setIsAuthorizedSelectorOf]; exact Bool.eq_false_of_not_eq_true h40
    · rw [continuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h41
    · rw [defaultSettlementFeeCbpSelectorOf]; exact Bool.eq_false_of_not_eq_true h42
    · rw [setFeeClaimerSelectorOf]; exact Bool.eq_false_of_not_eq_true h43
    · rw [pendingFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h44
    · rw [creditSelectorOf]; exact Bool.eq_false_of_not_eq_true h45
    · rw [updatePositionViewSelectorOf]; exact Bool.eq_false_of_not_eq_true h46
    · rw [tickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h47
    · rw [lastAccrualSelectorOf]; exact Bool.eq_false_of_not_eq_true h48
    · rw [consumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h49
    · rw [marketStateSelectorOf]; exact Bool.eq_false_of_not_eq_true h50
    · rw [collateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h51
    · rw [setConsumedSelectorOf]; exact Bool.eq_false_of_not_eq_true h52
    · rw [setMarketTickSpacingSelectorOf]; exact Bool.eq_false_of_not_eq_true h53
    · rw [setTickSpacingSetterSelectorOf]; exact Bool.eq_false_of_not_eq_true h54
    · rw [toMarketSelectorOf]; exact Bool.eq_false_of_not_eq_true h55
  · rw [continuousFeeCreditSelectorOf]; exact hsel

theorem midnightDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd, transitions_eq]
  refine dispatchList_none_short _ ?_ h
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [liquidationLockedSelectorOf]; rfl
  · rw [setDefaultContinuousFeeSelectorOf]; rfl
  · rw [defaultContinuousFeeSelectorOf]; rfl
  · rw [settlementFeeCbpsSelectorOf]; rfl
  · rw [claimSettlementFeeSelectorOf]; rfl
  · rw [configuratorSelectorOf]; rfl
  · rw [supplyCollateralSelectorOf]; rfl
  · rw [setMarketContinuousFeeSelectorOf]; rfl
  · rw [enableLltvSelectorOf]; rfl
  · rw [flashLoanSelectorOf]; rfl
  · rw [claimableSettlementFeeSelectorOf]; rfl
  · rw [totalUnitsSelectorOf]; rfl
  · rw [updatePositionSelectorOf]; rfl
  · rw [lossFactorSelectorOf]; rfl
  · rw [claimContinuousFeeSelectorOf]; rfl
  · rw [isHealthySelectorOf]; rfl
  · rw [setDefaultSettlementFeeSelectorOf]; rfl
  · rw [isAuthorizedSelectorOf]; rfl
  · rw [takeSelectorOf]; rfl
  · rw [repaySelectorOf]; rfl
  · rw [withdrawableSelectorOf]; rfl
  · rw [feeClaimerSelectorOf]; rfl
  · rw [feeSetterSelectorOf]; rfl
  · rw [lastLossFactorSelectorOf]; rfl
  · rw [isLiquidationCursorEnabledSelectorOf]; rfl
  · rw [enableLiquidationCursorSelectorOf]; rfl
  · rw [debtSelectorOf]; rfl
  · rw [positionSelectorOf]; rfl
  · rw [tickSpacingSetterSelectorOf]; rfl
  · rw [setMarketSettlementFeeSelectorOf]; rfl
  · rw [liquidateSelectorOf]; rfl
  · rw [setConfiguratorSelectorOf]; rfl
  · rw [withdrawCollateralSelectorOf]; rfl
  · rw [touchMarketSelectorOf]; rfl
  · rw [withdrawSelectorOf]; rfl
  · rw [settlementFeeSelectorOf]; rfl
  · rw [multicallSelectorOf]; rfl
  · rw [setFeeSetterSelectorOf]; rfl
  · rw [isLltvEnabledSelectorOf]; rfl
  · rw [collateralBitmapSelectorOf]; rfl
  · rw [setIsAuthorizedSelectorOf]; rfl
  · rw [continuousFeeSelectorOf]; rfl
  · rw [defaultSettlementFeeCbpSelectorOf]; rfl
  · rw [setFeeClaimerSelectorOf]; rfl
  · rw [pendingFeeSelectorOf]; rfl
  · rw [creditSelectorOf]; rfl
  · rw [updatePositionViewSelectorOf]; rfl
  · rw [tickSpacingSelectorOf]; rfl
  · rw [lastAccrualSelectorOf]; rfl
  · rw [consumedSelectorOf]; rfl
  · rw [marketStateSelectorOf]; rfl
  · rw [collateralSelectorOf]; rfl
  · rw [setConsumedSelectorOf]; rfl
  · rw [setMarketTickSpacingSelectorOf]; rfl
  · rw [setTickSpacingSetterSelectorOf]; rfl
  · rw [toMarketSelectorOf]; rfl
  · rw [continuousFeeCreditSelectorOf]; rfl

theorem midnightDispatch_none_nomatch {I : ExecutionEnv}
    (hnm : ∀ i, i < 57 → (midnightSelBytes i == I.calldata.extract 0 4) = false) :
    dispatchMsg contract I.calldata = none := by
  refine dispatchMsg_none_of_all_ne (contract := contract) (cd := I.calldata) (by rfl) (by rfl) ?_
  intro t ht
  rw [transitions_eq] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [liquidationLockedSelectorOf]; exact hnm 0 (by omega)
  · rw [setDefaultContinuousFeeSelectorOf]; exact hnm 1 (by omega)
  · rw [defaultContinuousFeeSelectorOf]; exact hnm 2 (by omega)
  · rw [settlementFeeCbpsSelectorOf]; exact hnm 3 (by omega)
  · rw [claimSettlementFeeSelectorOf]; exact hnm 4 (by omega)
  · rw [configuratorSelectorOf]; exact hnm 5 (by omega)
  · rw [supplyCollateralSelectorOf]; exact hnm 6 (by omega)
  · rw [setMarketContinuousFeeSelectorOf]; exact hnm 7 (by omega)
  · rw [enableLltvSelectorOf]; exact hnm 8 (by omega)
  · rw [flashLoanSelectorOf]; exact hnm 9 (by omega)
  · rw [claimableSettlementFeeSelectorOf]; exact hnm 10 (by omega)
  · rw [totalUnitsSelectorOf]; exact hnm 11 (by omega)
  · rw [updatePositionSelectorOf]; exact hnm 12 (by omega)
  · rw [lossFactorSelectorOf]; exact hnm 13 (by omega)
  · rw [claimContinuousFeeSelectorOf]; exact hnm 14 (by omega)
  · rw [isHealthySelectorOf]; exact hnm 15 (by omega)
  · rw [setDefaultSettlementFeeSelectorOf]; exact hnm 16 (by omega)
  · rw [isAuthorizedSelectorOf]; exact hnm 17 (by omega)
  · rw [takeSelectorOf]; exact hnm 18 (by omega)
  · rw [repaySelectorOf]; exact hnm 19 (by omega)
  · rw [withdrawableSelectorOf]; exact hnm 20 (by omega)
  · rw [feeClaimerSelectorOf]; exact hnm 21 (by omega)
  · rw [feeSetterSelectorOf]; exact hnm 22 (by omega)
  · rw [lastLossFactorSelectorOf]; exact hnm 23 (by omega)
  · rw [isLiquidationCursorEnabledSelectorOf]; exact hnm 24 (by omega)
  · rw [enableLiquidationCursorSelectorOf]; exact hnm 25 (by omega)
  · rw [debtSelectorOf]; exact hnm 26 (by omega)
  · rw [positionSelectorOf]; exact hnm 27 (by omega)
  · rw [tickSpacingSetterSelectorOf]; exact hnm 28 (by omega)
  · rw [setMarketSettlementFeeSelectorOf]; exact hnm 29 (by omega)
  · rw [liquidateSelectorOf]; exact hnm 30 (by omega)
  · rw [setConfiguratorSelectorOf]; exact hnm 31 (by omega)
  · rw [withdrawCollateralSelectorOf]; exact hnm 32 (by omega)
  · rw [touchMarketSelectorOf]; exact hnm 33 (by omega)
  · rw [withdrawSelectorOf]; exact hnm 34 (by omega)
  · rw [settlementFeeSelectorOf]; exact hnm 35 (by omega)
  · rw [multicallSelectorOf]; exact hnm 36 (by omega)
  · rw [setFeeSetterSelectorOf]; exact hnm 37 (by omega)
  · rw [isLltvEnabledSelectorOf]; exact hnm 38 (by omega)
  · rw [collateralBitmapSelectorOf]; exact hnm 39 (by omega)
  · rw [setIsAuthorizedSelectorOf]; exact hnm 40 (by omega)
  · rw [continuousFeeSelectorOf]; exact hnm 41 (by omega)
  · rw [defaultSettlementFeeCbpSelectorOf]; exact hnm 42 (by omega)
  · rw [setFeeClaimerSelectorOf]; exact hnm 43 (by omega)
  · rw [pendingFeeSelectorOf]; exact hnm 44 (by omega)
  · rw [creditSelectorOf]; exact hnm 45 (by omega)
  · rw [updatePositionViewSelectorOf]; exact hnm 46 (by omega)
  · rw [tickSpacingSelectorOf]; exact hnm 47 (by omega)
  · rw [lastAccrualSelectorOf]; exact hnm 48 (by omega)
  · rw [consumedSelectorOf]; exact hnm 49 (by omega)
  · rw [marketStateSelectorOf]; exact hnm 50 (by omega)
  · rw [collateralSelectorOf]; exact hnm 51 (by omega)
  · rw [setConsumedSelectorOf]; exact hnm 52 (by omega)
  · rw [setMarketTickSpacingSelectorOf]; exact hnm 53 (by omega)
  · rw [setTickSpacingSetterSelectorOf]; exact hnm 54 (by omega)
  · rw [toMarketSelectorOf]; exact hnm 55 (by omega)
  · rw [continuousFeeCreditSelectorOf]; exact hnm 56 (by omega)

end Benchmarks.Midnight
