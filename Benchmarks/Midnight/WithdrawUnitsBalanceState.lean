import Benchmarks.Midnight.WithdrawUnitsBalanceSource

/-! The states reached by the three ordered withdrawal balance writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def withdrawUnitsCreditState (evm : EVM.State) (id user units : UInt256) : EVM.State :=
  storeLow128 evm (positionSlot id user) (UInt256.sub (positionFieldWord evm id user 0) units)

def withdrawUnitsWithdrawableState (evm : EVM.State) (id user units : UInt256) : EVM.State :=
  let credited := withdrawUnitsCreditState evm id user units
  storeLow128 credited (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
    (UInt256.sub (marketBalanceWord credited id 1) units)

def withdrawUnitsFinalState (evm : EVM.State) (id user units : UInt256) : EVM.State :=
  let withdrawn := withdrawUnitsWithdrawableState evm id user units
  storeLow128 withdrawn (solcMappingSlot ⟨1⟩ id)
    (UInt256.sub (marketBalanceWord withdrawn id 0) units)

def WithdrawUnitsBalancesSafe (evm : EVM.State) (id user units : UInt256) : Prop :=
  units.toNat < 2^128 ∧ units.toNat ≤ (positionFieldWord evm id user 0).toNat ∧
    units.toNat ≤ (marketBalanceWord (withdrawUnitsCreditState evm id user units) id 1).toNat ∧
    units.toNat ≤ (marketBalanceWord (withdrawUnitsWithdrawableState evm id user units) id 0).toNat

@[simp] theorem withdrawUnitsCreditState_env (evm : EVM.State) (id user units : UInt256) :
    (withdrawUnitsCreditState evm id user units).executionEnv = evm.executionEnv :=
  storeLow128_env ..

@[simp] theorem withdrawUnitsWithdrawableState_env (evm : EVM.State) (id user units : UInt256) :
    (withdrawUnitsWithdrawableState evm id user units).executionEnv = evm.executionEnv := by
  simp [withdrawUnitsWithdrawableState]

@[simp] theorem withdrawUnitsFinalState_env (evm : EVM.State) (id user units : UInt256) :
    (withdrawUnitsFinalState evm id user units).executionEnv = evm.executionEnv := by
  simp [withdrawUnitsFinalState]

def withdrawUnitsCreditFrame (frame : Frame) (units : UInt256) : Frame :=
  wordLocal frame "__c4" units

def withdrawUnitsWithdrawableFrame (frame : Frame) (units : UInt256) : Frame :=
  wordLocal (withdrawUnitsCreditFrame frame units) "__c5" units

def withdrawUnitsFinalFrame (frame : Frame) (units : UInt256) : Frame :=
  wordLocal (withdrawUnitsWithdrawableFrame frame units) "__c6" units

theorem withdrawUnitsBalancesSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {receiver : AccountAddress} {result : ExecResult}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus)
    (hsafe : WithdrawUnitsBalancesSafe evm id user units)
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config (withdrawUnitsFinalFrame frame units)
      (withdrawUnitsFinalState evm id user units) (withdrawTransition.body.drop 16) result) :
    ExecBlock config frame evm (withdrawTransition.body.drop 10) result := by
  have hf1 := hf.insert "__c4" (.int units.toNat) (by decide)
  have hf2 := hf1.insert "__c5" (.int units.toNat) (by decide)
  have hf3 := hf2.insert "__c6" (.int units.toNat) (by decide)
  apply withdrawUnitsSubtractSource hf.contract hf.units
    (evalPositionAliasField 0 hcanon hf1.position)
    (assignPositionAliasField 0 _ hcanon hf1.position)
    (positionFieldWord_lt evm id user 0) hsafe.1 hsafe.2.1 hperm
  apply withdrawUnitsSubtractSource hf1.contract hf1.units
    (evalMarketBalance 1 hf2.marketState) (assignMarketBalance 1 _ hf2.marketState)
    (marketBalanceWord_lt (withdrawUnitsCreditState evm id user units) id 1)
    hsafe.1 hsafe.2.2.1 (by simpa only [withdrawUnitsCreditState_env] using hperm)
  exact withdrawUnitsSubtractSource hf2.contract hf2.units
    (evalMarketBalance 0 hf3.marketState) (assignMarketBalance 0 _ hf3.marketState)
    (marketBalanceWord_lt (withdrawUnitsWithdrawableState evm id user units) id 0)
    hsafe.1 hsafe.2.2.2 (by simpa only [withdrawUnitsWithdrawableState_env] using hperm) htail

end Benchmarks.Midnight
