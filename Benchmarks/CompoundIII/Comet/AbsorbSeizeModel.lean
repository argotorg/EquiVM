import Benchmarks.CompoundIII.Comet.WithdrawCollateralModel
import Benchmarks.CompoundIII.Comet.InternalFrameResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def absorbSeizeUserState (evm : State) (account asset : AccountAddress) : State :=
  storePackedWord evm (userCollateralSlot account asset) ⟨0⟩ 0 16

def absorbSeizeState (evm : State) (account asset : AccountAddress) : State :=
  let cleared := absorbSeizeUserState evm account asset
  storePackedWord cleared (totalsCollateralSlot asset)
    (UInt256.sub (withdrawCollateralTotal cleared asset)
      (withdrawCollateralBalance evm account asset)) 0 16

def absorbSeizeTotalOutcome (evm : State) (asset : AccountAddress) (seized : UInt256) :
    InternalOutcome :=
  if seized.toNat ≤ (withdrawCollateralTotal evm asset).toNat then
    .ok (storePackedWord evm (totalsCollateralSlot asset)
      (UInt256.sub (withdrawCollateralTotal evm asset) seized) 0 16)
  else .reverted

def absorbSeizeOutcome (evm : State) (account asset : AccountAddress) : InternalOutcome :=
  if evm.executionEnv.perm then
    absorbSeizeTotalOutcome (absorbSeizeUserState evm account asset) asset
      (withdrawCollateralBalance evm account asset)
  else .staticViolation

theorem absorbSeizeOutcome_ok_perm {evm updated : State} {account asset : AccountAddress}
    (h : absorbSeizeOutcome evm account asset = .ok updated) : evm.executionEnv.perm = true := by
  unfold absorbSeizeOutcome at h
  split_ifs at h with hp
  exact hp

def absorbSeizeBlock : List Stmt :=
  [.letDecl "seizeAmount" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      (.storage ⟨"userCollateral", [.mindex (.var "account"), .mindex (.var "asset"), .field "balance"]⟩),
    .assign .storage ⟨"userCollateral", [.mindex (.var "account"), .mindex (.var "asset"), .field "balance"]⟩
      (.intLit 0),
    .assign .storage ⟨"totalsCollateral", [.mindex (.var "asset"), .field "totalSupplyAsset"]⟩
      (.inRange (.uint ⟨128, by decide⟩) (.binary .sub
        (.storage ⟨"totalsCollateral", [.mindex (.var "asset"), .field "totalSupplyAsset"]⟩)
        (.var "seizeAmount")))]

def absorbSeizeFrame (frame : Frame) (evm : State) (account asset : AccountAddress) : Frame :=
  { frame with
    locals := frame.locals.insert "seizeAmount" (.int (withdrawCollateralBalance evm account asset).toNat) }

end Benchmarks.CompoundIII.Comet
