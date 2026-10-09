import Benchmarks.CompoundIII.Comet.DiffTarget
import Benchmarks.CompoundIII.Comet.Common
import Benchmarks.CompoundIII.Comet.GasBound

/-!
Reproducer for the original modern mode's eager decoding versus lazy element validation.
The input is a static absorb call with one dirty address, timestamp 1 and empty storage.
This file does not import the unfinished correctness theorem.
-/

open Solm ABI Solm.DiffTest Ethereum Ethereum.EVM
open Benchmarks.CompoundIII.Comet Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet.AbsorbStaticDecodeWitness

def baselineConfig : Config := { config with abiDecodeMode := .modern }

def zeroImms : CometWithExtendedAssetListImmutables :=
  { governor := EVM.address 0, pauseGuardian := EVM.address 0,
    baseToken := EVM.address 0, baseTokenPriceFeed := EVM.address 0,
    extensionDelegate := EVM.address 0, supplyKink := ⟨0⟩,
    supplyPerSecondInterestRateSlopeLow := ⟨0⟩, supplyPerSecondInterestRateSlopeHigh := ⟨0⟩,
    supplyPerSecondInterestRateBase := ⟨0⟩, borrowKink := ⟨0⟩,
    borrowPerSecondInterestRateSlopeLow := ⟨0⟩, borrowPerSecondInterestRateSlopeHigh := ⟨0⟩,
    borrowPerSecondInterestRateBase := ⟨0⟩, storeFrontPriceFactor := ⟨0⟩, baseScale := ⟨0⟩,
    trackingIndexScale := ⟨0⟩, baseTrackingSupplySpeed := ⟨0⟩, baseTrackingBorrowSpeed := ⟨0⟩,
    baseMinForRewards := ⟨0⟩, baseBorrowMin := ⟨0⟩, targetReserves := ⟨0⟩,
    decimals := ⟨0⟩, numAssets := ⟨0⟩, accrualDescaleFactor := ⟨0⟩, assetList := EVM.address 0,
    decimals_lt := by decide, numAssets_lt := by decide }
def zeroTarget : Target :=
  { name := "absorb-static-decode", contract := contract, config := baselineConfig,
    runtime := deployedRuntime zeroImms, immutables := immStore zeroImms }
def dirtyData := cometWithExtendedAssetListSelBytes 38 ++ wordBytes 0 ++ wordBytes 64 ++
  wordBytes 1 ++ wordBytes (2^160)
def zeroEnv := zeroTarget.env zeroTarget.runtime (EVM.address 0x2000) 0 dirtyData false 1

def evmIsStaticError : Bool :=
  match Ξ zeroTarget.world zeroTarget.world (.ofNat 3000000) default zeroEnv with
  | .error .StaticModeViolation => true
  | _ => false

theorem evm_static_check : evmIsStaticError = true := by native_decide

theorem evm_static :
    Ξ zeroTarget.world zeroTarget.world (.ofNat 3000000) default zeroEnv =
      .error .StaticModeViolation := by
  have h := evm_static_check
  unfold evmIsStaticError at h
  split at h
  · assumption
  · contradiction

theorem calldata_selects :
    selectorDispatchMsg contract dirtyData = some absorbTransition := by native_decide

theorem calldata_does_not_decode :
    decodeCalldataWithMode baselineConfig.abiDecodeMode (absorbTransition.params.map Param.name)
      (transitionSignature absorbTransition).paramTypes dirtyData = none := by native_decide

theorem gas_within_bound : cometGasBound (UInt256.ofNat 3000000) := by
  rw [cometGasBound_iff]
  decide

-- LIBRARY CANDIDATE (Reasoning/Reach): rejected calldata cannot refine a static-mode exception.
theorem no_refinement_of_static_decode_failure
    {cfg : Config} {contract : ContractDecl} {σ σ₀ : AccountMap} {gas : UInt256}
    {A : Substate} {I : ExecutionEnv} {imms : Store} {t : TransitionDecl}
    (hdispatch : selectorDispatchMsg contract I.calldata = some t)
    (hdecode : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none)
    (hreceive : receiveDispatchMsg contract I.calldata = none)
    (hevm : Ξ σ σ₀ gas A I = .error .StaticModeViolation) :
    ¬ runtimeRefinementFor cfg contract σ σ₀ gas A I imms := by
  intro h
  cases h with
  | execution _ hsolm _ =>
      cases hsolm with
      | intro hd hsig hargs _ _ =>
          cases Option.some.inj (hdispatch.symm.trans hd)
          subst_vars
          rw [hdecode] at hargs
          cases hargs
      | fallback hd _ _ _ _ _ _ => rw [hdispatch] at hd; cases hd
      | receive hd _ _ _ _ => rw [hreceive] at hd; cases hd
  | noDispatch _ hrev => rw [hevm] at hrev; cases hrev
  | decodingFailed _ _ _ hrev => rw [hevm] at hrev; cases hrev
  | outOfGas hoog => rw [hevm] at hoog; cases hoog

theorem refinement_fails :
    ¬ runtimeRefinementFor baselineConfig contract zeroTarget.world zeroTarget.world
      (UInt256.ofNat 3000000) default zeroEnv (immStore zeroImms) :=
  no_refinement_of_static_decode_failure calldata_selects calldata_does_not_decode rfl evm_static

theorem runtime_refinement_fails :
    ¬ runtimeRefinementWithWF trivialStorageWF cometGasBound baselineConfig
      (deployedRuntime zeroImms) contract (immStore zeroImms) := by
  intro h
  cases h with
  | intro h =>
      exact refinement_fails (h zeroTarget.world zeroTarget.world (.ofNat 3000000)
        default zeroEnv rfl (by native_decide) trivial gas_within_bound)

#eval (runCase zeroTarget
  { label := "dirty address, static accrual", σ := zeroTarget.world, I := zeroEnv }).verdict.describe

end Benchmarks.CompoundIII.Comet.AbsorbStaticDecodeWitness

