import Benchmarks.Midnight.RepaySourceEntry
import Benchmarks.Midnight.RepayBalanceStorage
import Benchmarks.Midnight.WithdrawUnitsBalanceSource

/-! Ordered checked debt reduction and withdrawable increase in repayment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def repayDebtState (evm : EVM.State) (id user units : UInt256) : EVM.State :=
  storeLow128 evm (positionSlot id user + ⟨2⟩)
    (UInt256.sub (low128 (healthPositionWord evm id user)) units)

def repayBalanceState (evm : EVM.State) (id user units : UInt256) : EVM.State :=
  let paid := repayDebtState evm id user units
  marketBalanceStore paid id 1 (marketBalanceWord paid id 1 + units)

@[simp] theorem repayDebtState_env (evm : EVM.State) (id user units : UInt256) :
    (repayDebtState evm id user units).executionEnv = evm.executionEnv := storeLow128_env ..

@[simp] theorem repayBalanceState_env (evm : EVM.State) (id user units : UInt256) :
    (repayBalanceState evm id user units).executionEnv = evm.executionEnv := by
  simp [repayBalanceState, marketBalanceStore]

def repayDebtFrame (frame : Frame) (units : UInt256) : Frame := wordLocal frame "__c1" units

def repayBalanceFrame (frame : Frame) (units : UInt256) : Frame :=
  wordLocal (repayDebtFrame frame units) "__c2" units

def RepayBalancesSafe (evm : EVM.State) (id user units : UInt256) : Prop :=
  units.toNat < 2^128 ∧ units.toNat ≤ (low128 (healthPositionWord evm id user)).toNat ∧
    (marketBalanceWord (repayDebtState evm id user units) id 1).toNat + units.toNat < 2^128

theorem repayDebtSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {callback : AccountAddress} {data : ByteArray} {result : ExecResult}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hcanon : user.toNat < EVM.addressModulus) (h128 : units.toNat < 2^128)
    (hle : units.toNat ≤ (low128 (healthPositionWord evm id user)).toNat)
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config (repayDebtFrame frame units) (repayDebtState evm id user units)
      (repayTransition.body.drop 7) result) :
    ExecBlock config frame evm (repayTransition.body.drop 5) result := by
  have hf1 := hf.insert "__c1" (.int units.toNat) (by decide)
  exact withdrawUnitsSubtractSource hf.contract hf.units
    (evalRepayDebt hf1.contract hf1.position hf1.idValue hf1.userValue hcanon)
    (assignRepayDebt _ hf1.contract hf1.position hf1.idValue hf1.userValue hcanon)
    (low128_lt _) h128 hle hperm htail

theorem repayWithdrawableSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {callback : AccountAddress} {data : ByteArray} {result : ExecResult}
    (hf : RepaySourceFrame frame m id user units callback data)
    (h128 : units.toNat < 2^128)
    (hsum : (marketBalanceWord evm id 1).toNat + units.toNat < 2^128)
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config (wordLocal frame "__c2" units)
      (marketBalanceStore evm id 1 (marketBalanceWord evm id 1 + units))
      (repayTransition.body.drop 9) result) :
    ExecBlock config frame evm (repayTransition.body.drop 7) result := by
  have hf2 := hf.insert "__c2" (.int units.toNat) (by decide)
  have he : evalExprs? config frame evm [.var "units"] = .ok [.int units.toNat] := by
    simp only [evalExprs?, evalWordLocal hf.units, EvalResult.bind, bind, pure]
  apply ExecBlock.consNormal (callToUint128 hf.contract he h128 (name := "__c2"))
  exact ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalCheckedAdd128
      (evalDirectMarketBalance 1 hf2.contract hf2.marketState hf2.idValue)
      (evalWordLocal (wordLocal_get ..)) hsum)
    (assignDirectMarketBalance 1 _ hf2.contract hf2.marketState hf2.idValue)) htail

theorem repayWithdrawableOverflow {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {callback : AccountAddress} {data : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data)
    (h128 : units.toNat < 2^128)
    (hsum : 2^128 ≤ (marketBalanceWord evm id 1).toNat + units.toNat) :
    ExecBlock config frame evm (repayTransition.body.drop 7) .reverted := by
  have hf2 := hf.insert "__c2" (.int units.toNat) (by decide)
  have he : evalExprs? config frame evm [.var "units"] = .ok [.int units.toNat] := by
    simp only [evalExprs?, evalWordLocal hf.units, EvalResult.bind, bind, pure]
  apply ExecBlock.consNormal (callToUint128 hf.contract he h128 (name := "__c2"))
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert (evalCheckedAdd128Overflow
    (evalDirectMarketBalance 1 hf2.contract hf2.marketState hf2.idValue)
    (evalWordLocal (wordLocal_get ..)) hsum))

theorem repayBalancesSource {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {callback : AccountAddress} {data : ByteArray} {result : ExecResult}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : RepayBalancesSafe evm id user units)
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config (repayBalanceFrame frame units) (repayBalanceState evm id user units)
      (repayTransition.body.drop 9) result) :
    ExecBlock config frame evm (repayTransition.body.drop 5) result := by
  apply repayDebtSource hf hcanon hsafe.1 hsafe.2.1 hperm
  exact repayWithdrawableSource (hf.insert "__c1" (.int units.toNat) (by decide))
    hsafe.1 hsafe.2.2 (by simpa only [repayDebtState_env] using hperm) htail

theorem repayDebtStatic {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {callback : AccountAddress} {data : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hcanon : user.toNat < EVM.addressModulus) (h128 : units.toNat < 2^128)
    (hle : units.toNat ≤ (low128 (healthPositionWord evm id user)).toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm (repayTransition.body.drop 5) .staticViolation := by
  have hf1 := hf.insert "__c1" (.int units.toNat) (by decide)
  have he : evalExprs? config frame evm [.var "units"] = .ok [.int units.toNat] := by
    simp only [evalExprs?, evalWordLocal hf.units, EvalResult.bind, bind, pure]
  apply ExecBlock.consNormal (callToUint128 hf.contract he h128 (name := "__c1"))
  exact ExecBlock.consStatic (ExecStmt.assignStatic
    (evalCheckedSub128
      (evalRepayDebt hf1.contract hf1.position hf1.idValue hf1.userValue hcanon)
      (evalWordLocal (wordLocal_get ..)) (low128_lt _) hle)
    (assignRepayDebt _ hf1.contract hf1.position hf1.idValue hf1.userValue hcanon) hperm)

end Benchmarks.Midnight
