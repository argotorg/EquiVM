import Benchmarks.Midnight.MarketBalanceFields

/-! The three ordered balance changes made by a continuous-fee claim. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def claimFeeCredit (evm : EVM.State) (id amount : UInt256) : UInt256 :=
  UInt256.sub (marketBalanceWord evm id 2) amount

def claimFeeCreditState (evm : EVM.State) (id amount : UInt256) : EVM.State :=
  marketBalanceStore evm id 2 (claimFeeCredit evm id amount)

def claimFeeUnits (evm : EVM.State) (id amount : UInt256) : UInt256 :=
  UInt256.sub (marketBalanceWord (claimFeeCreditState evm id amount) id 0) amount

def claimFeeUnitsState (evm : EVM.State) (id amount : UInt256) : EVM.State :=
  marketBalanceStore (claimFeeCreditState evm id amount) id 0 (claimFeeUnits evm id amount)

def claimFeeWithdrawable (evm : EVM.State) (id amount : UInt256) : UInt256 :=
  UInt256.sub (marketBalanceWord (claimFeeUnitsState evm id amount) id 1) amount

def claimFeeFinalState (evm : EVM.State) (id amount : UInt256) : EVM.State :=
  marketBalanceStore (claimFeeUnitsState evm id amount) id 1 (claimFeeWithdrawable evm id amount)

def ClaimFeeArithmeticSafe (evm : EVM.State) (id amount : UInt256) : Prop :=
  amount.toNat < 2^128 ∧ amount.toNat ≤ (marketBalanceWord evm id 2).toNat ∧
    amount.toNat ≤ (marketBalanceWord (claimFeeCreditState evm id amount) id 0).toNat ∧
    amount.toNat ≤ (marketBalanceWord (claimFeeUnitsState evm id amount) id 1).toNat

@[simp] theorem marketBalanceStore_env (evm : EVM.State) (id : UInt256) (i : Fin 3)
    (value : UInt256) : (marketBalanceStore evm id i value).executionEnv = evm.executionEnv := by
  unfold marketBalanceStore
  split <;> simp

@[simp] theorem claimFeeCreditState_env (evm : EVM.State) (id amount : UInt256) :
    (claimFeeCreditState evm id amount).executionEnv = evm.executionEnv := by
  simp [claimFeeCreditState]

@[simp] theorem claimFeeUnitsState_env (evm : EVM.State) (id amount : UInt256) :
    (claimFeeUnitsState evm id amount).executionEnv = evm.executionEnv := by
  simp [claimFeeUnitsState]

@[simp] theorem claimFeeFinalState_env (evm : EVM.State) (id amount : UInt256) :
    (claimFeeFinalState evm id amount).executionEnv = evm.executionEnv := by
  simp [claimFeeFinalState]

end Benchmarks.Midnight
