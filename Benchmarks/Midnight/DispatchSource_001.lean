import Benchmarks.Midnight.Common

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-! ## Stele dispatch: which transition a selector reaches -/

theorem midnightDispatch_liquidationLocked {I : ExecutionEnv} 
    (hsel : selIs I (midnightSelBytes 0)) :
    dispatchMsg contract I.calldata = some liquidationLockedTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := []) (post := [setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := liquidationLockedTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp at hu
  · rw [liquidationLockedSelectorOf]; exact hsel

theorem midnightDispatch_setDefaultContinuousFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0))
    (hsel : selIs I (midnightSelBytes 1)) :
    dispatchMsg contract I.calldata = some setDefaultContinuousFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition]) (post := [defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setDefaultContinuousFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
  · rw [setDefaultContinuousFeeSelectorOf]; exact hsel

theorem midnightDispatch_defaultContinuousFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1))
    (hsel : selIs I (midnightSelBytes 2)) :
    dispatchMsg contract I.calldata = some defaultContinuousFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition]) (post := [settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := defaultContinuousFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
  · rw [defaultContinuousFeeSelectorOf]; exact hsel

theorem midnightDispatch_settlementFeeCbps {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2))
    (hsel : selIs I (midnightSelBytes 3)) :
    dispatchMsg contract I.calldata = some settlementFeeCbpsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition]) (post := [claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := settlementFeeCbpsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
  · rw [settlementFeeCbpsSelectorOf]; exact hsel

theorem midnightDispatch_claimSettlementFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3))
    (hsel : selIs I (midnightSelBytes 4)) :
    dispatchMsg contract I.calldata = some claimSettlementFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition]) (post := [configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := claimSettlementFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
  · rw [claimSettlementFeeSelectorOf]; exact hsel

theorem midnightDispatch_configurator {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4))
    (hsel : selIs I (midnightSelBytes 5)) :
    dispatchMsg contract I.calldata = some configuratorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition]) (post := [supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := configuratorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
  · rw [configuratorSelectorOf]; exact hsel

theorem midnightDispatch_supplyCollateral {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5))
    (hsel : selIs I (midnightSelBytes 6)) :
    dispatchMsg contract I.calldata = some supplyCollateralTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition]) (post := [setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := supplyCollateralTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
  · rw [supplyCollateralSelectorOf]; exact hsel

theorem midnightDispatch_setMarketContinuousFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6))
    (hsel : selIs I (midnightSelBytes 7)) :
    dispatchMsg contract I.calldata = some setMarketContinuousFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition]) (post := [enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setMarketContinuousFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
  · rw [setMarketContinuousFeeSelectorOf]; exact hsel

theorem midnightDispatch_enableLltv {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7))
    (hsel : selIs I (midnightSelBytes 8)) :
    dispatchMsg contract I.calldata = some enableLltvTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition]) (post := [flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := enableLltvTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
  · rw [enableLltvSelectorOf]; exact hsel

theorem midnightDispatch_flashLoan {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8))
    (hsel : selIs I (midnightSelBytes 9)) :
    dispatchMsg contract I.calldata = some flashLoanTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition]) (post := [claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := flashLoanTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [liquidationLockedSelectorOf]; exact Bool.eq_false_of_not_eq_true h0
    · rw [setDefaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h1
    · rw [defaultContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h2
    · rw [settlementFeeCbpsSelectorOf]; exact Bool.eq_false_of_not_eq_true h3
    · rw [claimSettlementFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h4
    · rw [configuratorSelectorOf]; exact Bool.eq_false_of_not_eq_true h5
    · rw [supplyCollateralSelectorOf]; exact Bool.eq_false_of_not_eq_true h6
    · rw [setMarketContinuousFeeSelectorOf]; exact Bool.eq_false_of_not_eq_true h7
    · rw [enableLltvSelectorOf]; exact Bool.eq_false_of_not_eq_true h8
  · rw [flashLoanSelectorOf]; exact hsel

theorem midnightDispatch_claimableSettlementFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9))
    (hsel : selIs I (midnightSelBytes 10)) :
    dispatchMsg contract I.calldata = some claimableSettlementFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition]) (post := [totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := claimableSettlementFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [claimableSettlementFeeSelectorOf]; exact hsel

theorem midnightDispatch_totalUnits {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10))
    (hsel : selIs I (midnightSelBytes 11)) :
    dispatchMsg contract I.calldata = some totalUnitsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition]) (post := [updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := totalUnitsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [totalUnitsSelectorOf]; exact hsel

theorem midnightDispatch_updatePosition {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11))
    (hsel : selIs I (midnightSelBytes 12)) :
    dispatchMsg contract I.calldata = some updatePositionTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition]) (post := [lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := updatePositionTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [updatePositionSelectorOf]; exact hsel

theorem midnightDispatch_lossFactor {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12))
    (hsel : selIs I (midnightSelBytes 13)) :
    dispatchMsg contract I.calldata = some lossFactorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition]) (post := [claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := lossFactorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [lossFactorSelectorOf]; exact hsel

theorem midnightDispatch_claimContinuousFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13))
    (hsel : selIs I (midnightSelBytes 14)) :
    dispatchMsg contract I.calldata = some claimContinuousFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition]) (post := [isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := claimContinuousFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [claimContinuousFeeSelectorOf]; exact hsel

theorem midnightDispatch_isHealthy {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14))
    (hsel : selIs I (midnightSelBytes 15)) :
    dispatchMsg contract I.calldata = some isHealthyTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition]) (post := [setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := isHealthyTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [isHealthySelectorOf]; exact hsel

theorem midnightDispatch_setDefaultSettlementFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15))
    (hsel : selIs I (midnightSelBytes 16)) :
    dispatchMsg contract I.calldata = some setDefaultSettlementFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition]) (post := [isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setDefaultSettlementFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [setDefaultSettlementFeeSelectorOf]; exact hsel

theorem midnightDispatch_isAuthorized {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16))
    (hsel : selIs I (midnightSelBytes 17)) :
    dispatchMsg contract I.calldata = some isAuthorizedTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition]) (post := [takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := isAuthorizedTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [isAuthorizedSelectorOf]; exact hsel

theorem midnightDispatch_take {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17))
    (hsel : selIs I (midnightSelBytes 18)) :
    dispatchMsg contract I.calldata = some takeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition]) (post := [repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := takeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [takeSelectorOf]; exact hsel

theorem midnightDispatch_repay {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18))
    (hsel : selIs I (midnightSelBytes 19)) :
    dispatchMsg contract I.calldata = some repayTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition]) (post := [withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := repayTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [repaySelectorOf]; exact hsel

theorem midnightDispatch_withdrawable {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19))
    (hsel : selIs I (midnightSelBytes 20)) :
    dispatchMsg contract I.calldata = some withdrawableTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition]) (post := [feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := withdrawableTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [withdrawableSelectorOf]; exact hsel

theorem midnightDispatch_feeClaimer {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20))
    (hsel : selIs I (midnightSelBytes 21)) :
    dispatchMsg contract I.calldata = some feeClaimerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition]) (post := [feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := feeClaimerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [feeClaimerSelectorOf]; exact hsel

theorem midnightDispatch_feeSetter {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21))
    (hsel : selIs I (midnightSelBytes 22)) :
    dispatchMsg contract I.calldata = some feeSetterTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition]) (post := [lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := feeSetterTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [feeSetterSelectorOf]; exact hsel

theorem midnightDispatch_lastLossFactor {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22))
    (hsel : selIs I (midnightSelBytes 23)) :
    dispatchMsg contract I.calldata = some lastLossFactorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition]) (post := [isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := lastLossFactorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [lastLossFactorSelectorOf]; exact hsel

theorem midnightDispatch_isLiquidationCursorEnabled {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23))
    (hsel : selIs I (midnightSelBytes 24)) :
    dispatchMsg contract I.calldata = some isLiquidationCursorEnabledTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition]) (post := [enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := isLiquidationCursorEnabledTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [isLiquidationCursorEnabledSelectorOf]; exact hsel

theorem midnightDispatch_enableLiquidationCursor {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24))
    (hsel : selIs I (midnightSelBytes 25)) :
    dispatchMsg contract I.calldata = some enableLiquidationCursorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition]) (post := [debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := enableLiquidationCursorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [enableLiquidationCursorSelectorOf]; exact hsel

theorem midnightDispatch_debt {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25))
    (hsel : selIs I (midnightSelBytes 26)) :
    dispatchMsg contract I.calldata = some debtTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition]) (post := [positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := debtTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [debtSelectorOf]; exact hsel

theorem midnightDispatch_position {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26))
    (hsel : selIs I (midnightSelBytes 27)) :
    dispatchMsg contract I.calldata = some positionTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition]) (post := [tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := positionTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [positionSelectorOf]; exact hsel

theorem midnightDispatch_tickSpacingSetter {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27))
    (hsel : selIs I (midnightSelBytes 28)) :
    dispatchMsg contract I.calldata = some tickSpacingSetterTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition]) (post := [setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := tickSpacingSetterTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [tickSpacingSetterSelectorOf]; exact hsel

theorem midnightDispatch_setMarketSettlementFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28))
    (hsel : selIs I (midnightSelBytes 29)) :
    dispatchMsg contract I.calldata = some setMarketSettlementFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition]) (post := [liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setMarketSettlementFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [setMarketSettlementFeeSelectorOf]; exact hsel

theorem midnightDispatch_liquidate {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29))
    (hsel : selIs I (midnightSelBytes 30)) :
    dispatchMsg contract I.calldata = some liquidateTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition]) (post := [setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := liquidateTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [liquidateSelectorOf]; exact hsel

theorem midnightDispatch_setConfigurator {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30))
    (hsel : selIs I (midnightSelBytes 31)) :
    dispatchMsg contract I.calldata = some setConfiguratorTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition]) (post := [withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setConfiguratorTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [setConfiguratorSelectorOf]; exact hsel

theorem midnightDispatch_withdrawCollateral {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31))
    (hsel : selIs I (midnightSelBytes 32)) :
    dispatchMsg contract I.calldata = some withdrawCollateralTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition]) (post := [touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := withdrawCollateralTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [withdrawCollateralSelectorOf]; exact hsel

theorem midnightDispatch_touchMarket {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32))
    (hsel : selIs I (midnightSelBytes 33)) :
    dispatchMsg contract I.calldata = some touchMarketTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition]) (post := [withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := touchMarketTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [touchMarketSelectorOf]; exact hsel

theorem midnightDispatch_withdraw {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33))
    (hsel : selIs I (midnightSelBytes 34)) :
    dispatchMsg contract I.calldata = some withdrawTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition]) (post := [settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := withdrawTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [withdrawSelectorOf]; exact hsel

theorem midnightDispatch_settlementFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34))
    (hsel : selIs I (midnightSelBytes 35)) :
    dispatchMsg contract I.calldata = some settlementFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition]) (post := [multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := settlementFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [settlementFeeSelectorOf]; exact hsel

theorem midnightDispatch_multicall {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35))
    (hsel : selIs I (midnightSelBytes 36)) :
    dispatchMsg contract I.calldata = some multicallTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition]) (post := [setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := multicallTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [multicallSelectorOf]; exact hsel

theorem midnightDispatch_setFeeSetter {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36))
    (hsel : selIs I (midnightSelBytes 37)) :
    dispatchMsg contract I.calldata = some setFeeSetterTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition]) (post := [isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setFeeSetterTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [setFeeSetterSelectorOf]; exact hsel

theorem midnightDispatch_isLltvEnabled {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37))
    (hsel : selIs I (midnightSelBytes 38)) :
    dispatchMsg contract I.calldata = some isLltvEnabledTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition]) (post := [collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := isLltvEnabledTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [isLltvEnabledSelectorOf]; exact hsel

theorem midnightDispatch_collateralBitmap {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38))
    (hsel : selIs I (midnightSelBytes 39)) :
    dispatchMsg contract I.calldata = some collateralBitmapTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition]) (post := [setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := collateralBitmapTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [collateralBitmapSelectorOf]; exact hsel

theorem midnightDispatch_setIsAuthorized {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39))
    (hsel : selIs I (midnightSelBytes 40)) :
    dispatchMsg contract I.calldata = some setIsAuthorizedTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition]) (post := [continuousFeeTransition, defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setIsAuthorizedTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [setIsAuthorizedSelectorOf]; exact hsel

theorem midnightDispatch_continuousFee {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40))
    (hsel : selIs I (midnightSelBytes 41)) :
    dispatchMsg contract I.calldata = some continuousFeeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition]) (post := [defaultSettlementFeeCbpTransition, setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := continuousFeeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [continuousFeeSelectorOf]; exact hsel

theorem midnightDispatch_defaultSettlementFeeCbp {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41))
    (hsel : selIs I (midnightSelBytes 42)) :
    dispatchMsg contract I.calldata = some defaultSettlementFeeCbpTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition]) (post := [setFeeClaimerTransition, pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := defaultSettlementFeeCbpTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [defaultSettlementFeeCbpSelectorOf]; exact hsel

theorem midnightDispatch_setFeeClaimer {I : ExecutionEnv} (h0 : ¬ selIs I (midnightSelBytes 0)) (h1 : ¬ selIs I (midnightSelBytes 1)) (h2 : ¬ selIs I (midnightSelBytes 2)) (h3 : ¬ selIs I (midnightSelBytes 3)) (h4 : ¬ selIs I (midnightSelBytes 4)) (h5 : ¬ selIs I (midnightSelBytes 5)) (h6 : ¬ selIs I (midnightSelBytes 6)) (h7 : ¬ selIs I (midnightSelBytes 7)) (h8 : ¬ selIs I (midnightSelBytes 8)) (h9 : ¬ selIs I (midnightSelBytes 9)) (h10 : ¬ selIs I (midnightSelBytes 10)) (h11 : ¬ selIs I (midnightSelBytes 11)) (h12 : ¬ selIs I (midnightSelBytes 12)) (h13 : ¬ selIs I (midnightSelBytes 13)) (h14 : ¬ selIs I (midnightSelBytes 14)) (h15 : ¬ selIs I (midnightSelBytes 15)) (h16 : ¬ selIs I (midnightSelBytes 16)) (h17 : ¬ selIs I (midnightSelBytes 17)) (h18 : ¬ selIs I (midnightSelBytes 18)) (h19 : ¬ selIs I (midnightSelBytes 19)) (h20 : ¬ selIs I (midnightSelBytes 20)) (h21 : ¬ selIs I (midnightSelBytes 21)) (h22 : ¬ selIs I (midnightSelBytes 22)) (h23 : ¬ selIs I (midnightSelBytes 23)) (h24 : ¬ selIs I (midnightSelBytes 24)) (h25 : ¬ selIs I (midnightSelBytes 25)) (h26 : ¬ selIs I (midnightSelBytes 26)) (h27 : ¬ selIs I (midnightSelBytes 27)) (h28 : ¬ selIs I (midnightSelBytes 28)) (h29 : ¬ selIs I (midnightSelBytes 29)) (h30 : ¬ selIs I (midnightSelBytes 30)) (h31 : ¬ selIs I (midnightSelBytes 31)) (h32 : ¬ selIs I (midnightSelBytes 32)) (h33 : ¬ selIs I (midnightSelBytes 33)) (h34 : ¬ selIs I (midnightSelBytes 34)) (h35 : ¬ selIs I (midnightSelBytes 35)) (h36 : ¬ selIs I (midnightSelBytes 36)) (h37 : ¬ selIs I (midnightSelBytes 37)) (h38 : ¬ selIs I (midnightSelBytes 38)) (h39 : ¬ selIs I (midnightSelBytes 39)) (h40 : ¬ selIs I (midnightSelBytes 40)) (h41 : ¬ selIs I (midnightSelBytes 41)) (h42 : ¬ selIs I (midnightSelBytes 42))
    (hsel : selIs I (midnightSelBytes 43)) :
    dispatchMsg contract I.calldata = some setFeeClaimerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [liquidationLockedTransition, setDefaultContinuousFeeTransition, defaultContinuousFeeTransition, settlementFeeCbpsTransition, claimSettlementFeeTransition, configuratorTransition, supplyCollateralTransition, setMarketContinuousFeeTransition, enableLltvTransition, flashLoanTransition, claimableSettlementFeeTransition, totalUnitsTransition, updatePositionTransition, lossFactorTransition, claimContinuousFeeTransition, isHealthyTransition, setDefaultSettlementFeeTransition, isAuthorizedTransition, takeTransition, repayTransition, withdrawableTransition, feeClaimerTransition, feeSetterTransition, lastLossFactorTransition, isLiquidationCursorEnabledTransition, enableLiquidationCursorTransition, debtTransition, positionTransition, tickSpacingSetterTransition, setMarketSettlementFeeTransition, liquidateTransition, setConfiguratorTransition, withdrawCollateralTransition, touchMarketTransition, withdrawTransition, settlementFeeTransition, multicallTransition, setFeeSetterTransition, isLltvEnabledTransition, collateralBitmapTransition, setIsAuthorizedTransition, continuousFeeTransition, defaultSettlementFeeCbpTransition]) (post := [pendingFeeTransition, creditTransition, updatePositionViewTransition, tickSpacingTransition, lastAccrualTransition, consumedTransition, marketStateTransition, collateralTransition, setConsumedTransition, setMarketTickSpacingTransition, setTickSpacingSetterTransition, toMarketTransition, continuousFeeCreditTransition])
    (ti := setFeeClaimerTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · exact transitions_eq
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [setFeeClaimerSelectorOf]; exact hsel

end Benchmarks.Midnight
