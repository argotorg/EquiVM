import Benchmarks.Morpho.MorphoBlue.Common

/-! Solm selector dispatch and the raw signature fallback. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MorphoBlue

theorem morphoSelectorDispatch_of_selIs {I : ExecutionEnv} {i : Nat} (hi : i < 27)
    (hsel : selIs I (morphoSelBytes i)) :
    selectorDispatchMsg contract I.calldata = some contract.transitions[i]! := by
  rw [selectorDispatchMsg_eq_dispatchList, transitions_eq]
  simp only [dispatchList_cons, dispatchList_nil,
    setOwnerSelectorOf, accrueInterestSelectorOf, repaySelectorOf,
    supplyCollateralSelectorOf, setFeeSelectorOf, dOMAIN_SEPARATORSelectorOf,
    feeRecipientSelectorOf, enableLltvSelectorOf, borrowSelectorOf,
    enableIrmSelectorOf, withdrawSelectorOf, isAuthorizedSelectorOf,
    positionSelectorOf, nonceSelectorOf, extSloadsSelectorOf,
    withdrawCollateralSelectorOf, createMarketSelectorOf, ownerSelectorOf,
    idToMarketParamsSelectorOf, supplySelectorOf, isLltvEnabledSelectorOf,
    liquidateSelectorOf, flashLoanSelectorOf, marketSelectorOf,
    setFeeRecipientSelectorOf, setAuthorizationSelectorOf, isIrmEnabledSelectorOf]
  rw [← byteArray_eq_of_beq hsel]
  interval_cases i <;> rfl

theorem morphoSelectorDispatch_none_of_misses {I : ExecutionEnv}
    (hnm : ∀ i, i < 27 → (morphoSelBytes i == I.calldata.extract 0 4) = false) :
    selectorDispatchMsg contract I.calldata = none := by
  rw [selectorDispatchMsg_eq_dispatchList, transitions_eq]
  simp only [dispatchList_cons, dispatchList_nil,
    setOwnerSelectorOf, accrueInterestSelectorOf, repaySelectorOf,
    supplyCollateralSelectorOf, setFeeSelectorOf, dOMAIN_SEPARATORSelectorOf,
    feeRecipientSelectorOf, enableLltvSelectorOf, borrowSelectorOf,
    enableIrmSelectorOf, withdrawSelectorOf, isAuthorizedSelectorOf,
    positionSelectorOf, nonceSelectorOf, extSloadsSelectorOf,
    withdrawCollateralSelectorOf, createMarketSelectorOf, ownerSelectorOf,
    idToMarketParamsSelectorOf, supplySelectorOf, isLltvEnabledSelectorOf,
    liquidateSelectorOf, flashLoanSelectorOf, marketSelectorOf,
    setFeeRecipientSelectorOf, setAuthorizationSelectorOf, isIrmEnabledSelectorOf]
  simp (disch := omega) only [hnm, Bool.false_eq_true, ↓reduceIte]

/-! ## Solm dispatch: which transition a selector reaches -/

theorem morphoDispatch_setOwner {I : ExecutionEnv} 
    (hsel : selIs I (morphoSelBytes 0)) :
    dispatchMsg contract I.calldata = some setOwnerTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_accrueInterest {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0))
    (hsel : selIs I (morphoSelBytes 1)) :
    dispatchMsg contract I.calldata = some accrueInterestTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_repay {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1))
    (hsel : selIs I (morphoSelBytes 2)) :
    dispatchMsg contract I.calldata = some repayTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_supplyCollateral {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2))
    (hsel : selIs I (morphoSelBytes 3)) :
    dispatchMsg contract I.calldata = some supplyCollateralTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_setFee {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3))
    (hsel : selIs I (morphoSelBytes 4)) :
    dispatchMsg contract I.calldata = some setFeeTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_dOMAIN_SEPARATOR {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4))
    (hsel : selIs I (morphoSelBytes 5)) :
    dispatchMsg contract I.calldata = some dOMAIN_SEPARATORTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_feeRecipient {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5))
    (hsel : selIs I (morphoSelBytes 6)) :
    dispatchMsg contract I.calldata = some feeRecipientTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_enableLltv {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6))
    (hsel : selIs I (morphoSelBytes 7)) :
    dispatchMsg contract I.calldata = some enableLltvTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_borrow {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7))
    (hsel : selIs I (morphoSelBytes 8)) :
    dispatchMsg contract I.calldata = some borrowTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_enableIrm {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8))
    (hsel : selIs I (morphoSelBytes 9)) :
    dispatchMsg contract I.calldata = some enableIrmTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_withdraw {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9))
    (hsel : selIs I (morphoSelBytes 10)) :
    dispatchMsg contract I.calldata = some withdrawTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_isAuthorized {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10))
    (hsel : selIs I (morphoSelBytes 11)) :
    dispatchMsg contract I.calldata = some isAuthorizedTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_position {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11))
    (hsel : selIs I (morphoSelBytes 12)) :
    dispatchMsg contract I.calldata = some positionTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_nonce {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12))
    (hsel : selIs I (morphoSelBytes 13)) :
    dispatchMsg contract I.calldata = some nonceTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_extSloads {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13))
    (hsel : selIs I (morphoSelBytes 14)) :
    dispatchMsg contract I.calldata = some extSloadsTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_withdrawCollateral {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14))
    (hsel : selIs I (morphoSelBytes 15)) :
    dispatchMsg contract I.calldata = some withdrawCollateralTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_createMarket {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15))
    (hsel : selIs I (morphoSelBytes 16)) :
    dispatchMsg contract I.calldata = some createMarketTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_owner {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16))
    (hsel : selIs I (morphoSelBytes 17)) :
    dispatchMsg contract I.calldata = some ownerTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_idToMarketParams {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17))
    (hsel : selIs I (morphoSelBytes 18)) :
    dispatchMsg contract I.calldata = some idToMarketParamsTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_supply {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18))
    (hsel : selIs I (morphoSelBytes 19)) :
    dispatchMsg contract I.calldata = some supplyTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_isLltvEnabled {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19))
    (hsel : selIs I (morphoSelBytes 20)) :
    dispatchMsg contract I.calldata = some isLltvEnabledTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_liquidate {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19)) (h20 : ¬ selIs I (morphoSelBytes 20))
    (hsel : selIs I (morphoSelBytes 21)) :
    dispatchMsg contract I.calldata = some liquidateTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_flashLoan {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19)) (h20 : ¬ selIs I (morphoSelBytes 20)) (h21 : ¬ selIs I (morphoSelBytes 21))
    (hsel : selIs I (morphoSelBytes 22)) :
    dispatchMsg contract I.calldata = some flashLoanTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_market {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19)) (h20 : ¬ selIs I (morphoSelBytes 20)) (h21 : ¬ selIs I (morphoSelBytes 21)) (h22 : ¬ selIs I (morphoSelBytes 22))
    (hsel : selIs I (morphoSelBytes 23)) :
    dispatchMsg contract I.calldata = some marketTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_setFeeRecipient {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19)) (h20 : ¬ selIs I (morphoSelBytes 20)) (h21 : ¬ selIs I (morphoSelBytes 21)) (h22 : ¬ selIs I (morphoSelBytes 22)) (h23 : ¬ selIs I (morphoSelBytes 23))
    (hsel : selIs I (morphoSelBytes 24)) :
    dispatchMsg contract I.calldata = some setFeeRecipientTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_setAuthorization {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19)) (h20 : ¬ selIs I (morphoSelBytes 20)) (h21 : ¬ selIs I (morphoSelBytes 21)) (h22 : ¬ selIs I (morphoSelBytes 22)) (h23 : ¬ selIs I (morphoSelBytes 23)) (h24 : ¬ selIs I (morphoSelBytes 24))
    (hsel : selIs I (morphoSelBytes 25)) :
    dispatchMsg contract I.calldata = some setAuthorizationTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_isIrmEnabled {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19)) (h20 : ¬ selIs I (morphoSelBytes 20)) (h21 : ¬ selIs I (morphoSelBytes 21)) (h22 : ¬ selIs I (morphoSelBytes 22)) (h23 : ¬ selIs I (morphoSelBytes 23)) (h24 : ¬ selIs I (morphoSelBytes 24)) (h25 : ¬ selIs I (morphoSelBytes 25))
    (hsel : selIs I (morphoSelBytes 26)) :
    dispatchMsg contract I.calldata = some isIrmEnabledTransition := by
  simp only [dispatchMsg, morphoSelectorDispatch_of_selIs (by decide) hsel]

theorem morphoDispatch_setAuthorizationWithSig {I : ExecutionEnv} (h0 : ¬ selIs I (morphoSelBytes 0)) (h1 : ¬ selIs I (morphoSelBytes 1)) (h2 : ¬ selIs I (morphoSelBytes 2)) (h3 : ¬ selIs I (morphoSelBytes 3)) (h4 : ¬ selIs I (morphoSelBytes 4)) (h5 : ¬ selIs I (morphoSelBytes 5)) (h6 : ¬ selIs I (morphoSelBytes 6)) (h7 : ¬ selIs I (morphoSelBytes 7)) (h8 : ¬ selIs I (morphoSelBytes 8)) (h9 : ¬ selIs I (morphoSelBytes 9)) (h10 : ¬ selIs I (morphoSelBytes 10)) (h11 : ¬ selIs I (morphoSelBytes 11)) (h12 : ¬ selIs I (morphoSelBytes 12)) (h13 : ¬ selIs I (morphoSelBytes 13)) (h14 : ¬ selIs I (morphoSelBytes 14)) (h15 : ¬ selIs I (morphoSelBytes 15)) (h16 : ¬ selIs I (morphoSelBytes 16)) (h17 : ¬ selIs I (morphoSelBytes 17)) (h18 : ¬ selIs I (morphoSelBytes 18)) (h19 : ¬ selIs I (morphoSelBytes 19)) (h20 : ¬ selIs I (morphoSelBytes 20)) (h21 : ¬ selIs I (morphoSelBytes 21)) (h22 : ¬ selIs I (morphoSelBytes 22)) (h23 : ¬ selIs I (morphoSelBytes 23)) (h24 : ¬ selIs I (morphoSelBytes 24)) (h25 : ¬ selIs I (morphoSelBytes 25)) (h26 : ¬ selIs I (morphoSelBytes 26))
    (hsel : selIs I (morphoSelBytes 27)) :
    dispatchMsg contract I.calldata = some setAuthorizationWithSigTransition := by
  have hmiss : selectorDispatchMsg contract I.calldata = none := by
    apply morphoSelectorDispatch_none_of_misses
    intro i hi
    interval_cases i <;> simp_all only [selIs, Bool.not_eq_true]
  rw [dispatchMsg, hmiss]
  simp only [receiveDispatchMsg, show contract.receive = none from rfl, ite_self]
  rfl

theorem morphoDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    selectorDispatchMsg contract cd = none := by
  rw [selectorDispatchMsg_eq_dispatchList]
  apply dispatchList_none_short _ (fun t ht ↦ ?_) h
  rw [transitions_eq] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [setOwnerSelectorOf, accrueInterestSelectorOf, repaySelectorOf,
      supplyCollateralSelectorOf, setFeeSelectorOf, dOMAIN_SEPARATORSelectorOf,
      feeRecipientSelectorOf, enableLltvSelectorOf, borrowSelectorOf,
      enableIrmSelectorOf, withdrawSelectorOf, isAuthorizedSelectorOf,
      positionSelectorOf, nonceSelectorOf, extSloadsSelectorOf,
      withdrawCollateralSelectorOf, createMarketSelectorOf, ownerSelectorOf,
      idToMarketParamsSelectorOf, supplySelectorOf, isLltvEnabledSelectorOf,
      liquidateSelectorOf, flashLoanSelectorOf, marketSelectorOf,
      setFeeRecipientSelectorOf, setAuthorizationSelectorOf, isIrmEnabledSelectorOf]
    rfl

theorem morphoDispatch_none_nomatch {I : ExecutionEnv}
    (hnm : ∀ i, i < 28 → (morphoSelBytes i == I.calldata.extract 0 4) = false) :
    selectorDispatchMsg contract I.calldata = none := by
  exact morphoSelectorDispatch_none_of_misses (fun i hi ↦ hnm i (by omega))

end Benchmarks.Morpho.MorphoBlue
