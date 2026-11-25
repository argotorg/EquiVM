import Benchmarks.Midnight.PositionUpdateWritesSource
import Benchmarks.Midnight.PositionUpdateFeeSource

variable {fork : Ethereum.Fork}

/-! Source execution of the state-changing position update after its checked calculations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def positionUpdatedBalances (evm : EVM.State) (m : MarketData) (id user : UInt256) : EVM.State :=
  positionUpdateState evm id user (positionNewCredit evm m id user) (positionNewPending evm m id user)

def positionUpdateFinalState (evm : EVM.State) (m : MarketData) (id user : UInt256) : EVM.State :=
  positionUpdateFeeState (positionUpdatedBalances evm m id user) id (positionViewFee evm m id user)

def positionUpdateFinalFrame (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  wordLocal (positionUpdateWritesFrame evm imms m id user) "__c1" (positionViewFee evm m id user)

theorem positionUpdateSourceReturns (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user)
    (hc : (positionNewCredit evm m id user).toNat ≤ (positionFieldWord evm id user 0).toNat)
    (hp : (positionNewPending evm m id user).toNat ≤ (positionFieldWord evm id user 1).toNat)
    (hsum : (marketFeeCreditWord (positionUpdatedBalances evm m id user) id).toNat +
      (positionViewFee evm m id user).toNat < 2^128)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body
      (.returned (positionUpdateFinalFrame evm imms m id user) (positionUpdateFinalState evm m id user)
        (some (positionViewReturnValues (positionPostCredit evm id user) (positionPostPending evm id user)
          (positionViewFee evm m id user)))) := by
  apply ExecFuncBody.execBlockRet
  apply (positionUpdateWritesPrefix evm imms m id user hcanon hsafe hc hp).run
  rcases positionUpdateWrites_get evm imms m id user with
    ⟨hfc, hbase, hid, hpos, hcredit, hpending, hfee, hcd, hpd, huser⟩
  apply positionUpdateAssignmentsSource hfc hbase hid hpos hcredit hpending hcanon hperm
  exact positionUpdateFeeSource hfc hbase hid huser hcredit hpending hfee hcd hpd
    (positionAccruedFee_lt ..) hsum (by simpa only [positionUpdateState_env] using hperm)

theorem positionUpdateSourceFeeReverts (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user)
    (hc : (positionNewCredit evm m id user).toNat ≤ (positionFieldWord evm id user 0).toNat)
    (hp : (positionNewPending evm m id user).toNat ≤ (positionFieldWord evm id user 1).toNat)
    (hsum : 2^128 ≤ (marketFeeCreditWord (positionUpdatedBalances evm m id user) id).toNat +
      (positionViewFee evm m id user).toNat)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (positionUpdateWritesPrefix evm imms m id user hcanon hsafe hc hp).run
  rcases positionUpdateWrites_get evm imms m id user with
    ⟨hfc, hbase, hid, hpos, hcredit, hpending, hfee, hcd, hpd, huser⟩
  apply positionUpdateAssignmentsSource hfc hbase hid hpos hcredit hpending hcanon hperm
  exact positionUpdateFeeSourceRevert hfc hbase hid hfee (positionAccruedFee_lt ..) hsum

theorem positionNewCredit_lt {evm : EVM.State} {m : MarketData} {id user : UInt256}
    (hsafe : PositionViewSourceSafe evm m id user) : (positionNewCredit evm m id user).toNat < 2^128 := by
  unfold positionNewCredit
  rw [usub_toNat (show (positionViewFee evm m id user).toNat ≤
    (low128 (positionPostCredit evm id user)).toNat from hsafe.2.2.1)]
  have h := low128_lt (positionPostCredit evm id user)
  omega

theorem positionNewPending_lt {evm : EVM.State} {m : MarketData} {id user : UInt256}
    (hsafe : PositionViewSourceSafe evm m id user) : (positionNewPending evm m id user).toNat < 2^128 := by
  unfold positionNewPending
  rw [usub_toNat (show (positionViewFee evm m id user).toNat ≤
    (low128 (positionPostPending evm id user)).toNat from hsafe.2.2.2)]
  have h := low128_lt (positionPostPending evm id user)
  omega

@[simp] theorem positionUpdateFinalState_env (evm : EVM.State) (m : MarketData) (id user : UInt256) :
    (positionUpdateFinalState evm m id user).executionEnv = evm.executionEnv := by
  simp [positionUpdateFinalState, positionUpdateFeeState, positionUpdatedBalances]

theorem positionUpdateFinalState_accounts (evm : EVM.State) (m : MarketData) (id user : UInt256) :
    (positionUpdateFinalState evm m id user).accountMap =
      let σ' := positionUpdateAccounts evm.accountMap evm.executionEnv id user
        (positionNewCredit evm m id user) (positionNewPending evm m id user)
      storeHigh128Accounts σ' evm.executionEnv (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
        (UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨1⟩) σ' evm.executionEnv)
          (UInt256.ofNat 128) + positionViewFee evm m id user) := by
  have hl := storageLoad_codeOwner_eq_solcSlotWordAt (positionUpdatedBalances evm m id user)
    evm.executionEnv (solcMappingSlot ⟨1⟩ id + ⟨1⟩) (by simp [positionUpdatedBalances])
  simp only [positionUpdatedBalances, positionUpdateState_env, positionUpdateState_accounts] at hl
  simp only [positionUpdateFinalState, positionUpdateFeeState, storeHigh128_accounts, marketFeeCreditWord,
    positionUpdatedBalances, positionUpdateState_env, positionUpdateState_accounts, hl]

end Benchmarks.Midnight
