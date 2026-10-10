import Benchmarks.CompoundIII.Comet.Common
import Benchmarks.CompoundIII.Comet.DispatchRules

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transitionAt (i : Fin 68) : TransitionDecl :=
  contract.transitions[i.val]'(by exact i.isLt)

theorem transitionAt_mem (i : Fin 68) : transitionAt i ∈ contract.transitions := by
  exact List.getElem_mem _

theorem selectorOf_transitionAt (i : Fin 68) :
    selectorOf (transitionAt i) = cometWithExtendedAssetListSelBytes i.val := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact isLiquidatableSelectorOf
  · exact getReservesSelectorOf
  · exact isSupplyPausedSelectorOf
  · exact governorSelectorOf
  · exact totalSupplySelectorOf
  · exact baseTrackingSupplySpeedSelectorOf
  · exact initializeStorageSelectorOf
  · exact storeFrontPriceFactorSelectorOf
  · exact transferFromSelectorOf
  · exact pauseGuardianSelectorOf
  · exact withdrawFromSelectorOf
  · exact borrowPerSecondInterestRateSlopeHighSelectorOf
  · exact userCollateralSelectorOf
  · exact borrowPerSecondInterestRateSlopeLowSelectorOf
  · exact userNonceSelectorOf
  · exact baseBorrowMinSelectorOf
  · exact decimalsSelectorOf
  · exact targetReservesSelectorOf
  · exact borrowBalanceOfSelectorOf
  · exact isBorrowCollateralizedSelectorOf
  · exact getAssetInfoByAddressSelectorOf
  · exact getPriceSelectorOf
  · exact supplyToSelectorOf
  · exact transferAssetSelectorOf
  · exact baseScaleSelectorOf
  · exact pauseSelectorOf
  · exact extensionDelegateSelectorOf
  · exact totalsCollateralSelectorOf
  · exact supplyPerSecondInterestRateSlopeLowSelectorOf
  · exact isWithdrawPausedSelectorOf
  · exact balanceOfSelectorOf
  · exact borrowPerSecondInterestRateBaseSelectorOf
  · exact quoteCollateralSelectorOf
  · exact getUtilizationSelectorOf
  · exact supplyPerSecondInterestRateSlopeHighSelectorOf
  · exact totalBorrowSelectorOf
  · exact isAbsorbPausedSelectorOf
  · exact supplyFromSelectorOf
  · exact absorbSelectorOf
  · exact borrowKinkSelectorOf
  · exact baseMinForRewardsSelectorOf
  · exact supplyPerSecondInterestRateBaseSelectorOf
  · exact baseTrackingBorrowSpeedSelectorOf
  · exact getBorrowRateSelectorOf
  · exact getCollateralReservesSelectorOf
  · exact isAllowedSelectorOf
  · exact isTransferPausedSelectorOf
  · exact numAssetsSelectorOf
  · exact supplyKinkSelectorOf
  · exact transferSelectorOf
  · exact trackingIndexScaleSelectorOf
  · exact approveThisSelectorOf
  · exact accrueAccountSelectorOf
  · exact transferAssetFromSelectorOf
  · exact withdrawToSelectorOf
  · exact baseTokenSelectorOf
  · exact liquidatorPointsSelectorOf
  · exact getAssetInfoSelectorOf
  · exact hasPermissionSelectorOf
  · exact isBuyPausedSelectorOf
  · exact getSupplyRateSelectorOf
  · exact userBasicSelectorOf
  · exact assetListSelectorOf
  · exact withdrawReservesSelectorOf
  · exact buyCollateralSelectorOf
  · exact baseTokenPriceFeedSelectorOf
  · exact supplySelectorOf
  · exact withdrawSelectorOf

set_option maxRecDepth 10000 in
theorem cometSelectors_injective :
    Function.Injective (fun i : Fin 68 ↦ cometWithExtendedAssetListSelBytes i.val) := by
  decide +kernel

theorem cometSelectorDispatch {I : ExecutionEnv} (i : Fin 68)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes i.val)) :
    selectorDispatchMsg contract I.calldata = some (transitionAt i) := by
  rw [selectorDispatchMsg_eq_dispatchList]
  apply dispatchList_eq_some_of_unique (transitionAt_mem i)
  · rw [selectorOf_transitionAt]
    exact hsel
  · intro t ht hhit
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ht
    let j' : Fin 68 := ⟨j.val, j.isLt⟩
    have htransition : transitionAt j' = t := hj
    have heq : cometWithExtendedAssetListSelBytes j'.val =
        cometWithExtendedAssetListSelBytes i.val := by
      rw [← selectorOf_transitionAt, htransition]
      exact (byteArray_eq_of_beq hhit).trans (byteArray_eq_of_beq hsel).symm
    have hindex := cometSelectors_injective heq
    rw [← htransition, hindex]

end Benchmarks.CompoundIII.Comet
