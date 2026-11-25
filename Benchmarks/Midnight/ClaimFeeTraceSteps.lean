import Benchmarks.Midnight.ClaimFeeState
import Benchmarks.Midnight.ClaimFeeBlocksFunding
import Benchmarks.Midnight.CheckedUint128Gas

variable {fork : Ethereum.Fork}

/-! Ordered claim-fee reads and writes, retaining the transfer's memory budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightClaimFeeReadCredit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {evm : EVM.State} {mem rdata : ByteArray} {aw root id amount : UInt256}
    {credit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 7 ≤ 1024)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨15604⟩
      (amount :: solcMappingSlot ⟨1⟩ id :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', TransferBudget root credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨19743⟩
        (marketBalanceWord evm id 2 :: amount :: ⟨15626⟩ :: ⟨15658⟩ ::
          solcMappingSlot ⟨1⟩ id :: (solcMappingSlot ⟨1⟩ id + ⟨1⟩) :: R)
        mem aw rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hb', rd'⟩ := claim_block_15604_funded hstack (by jump_dest) hb rd
  have hw := storageLoad_codeOwner_eq_solcSlotWordAt evm I
    (solcMappingSlot ⟨1⟩ id + ⟨1⟩) (congrArg ExecutionEnv.codeOwner henv)
  simp only [midnightBlocks.midnight_block_15604_stack] at rd'
  refine ⟨k', C', hb', ?_⟩
  simpa only [marketBalanceWord, marketBalanceSlot, show (2 : Fin 3).val = 2 from rfl,
    show ¬ (2 : Nat) = 0 from by decide, if_false, if_true, hw,
    u256_add_comm (UInt256.ofNat 1)] using rd'

theorem midnightClaimFeeWriteCredit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {evm : EVM.State} {mem rdata : ByteArray} {aw root id amount : UInt256}
    {credit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨15626⟩
      (claimFeeCredit evm id amount :: ⟨15658⟩ :: solcMappingSlot ⟨1⟩ id ::
        (solcMappingSlot ⟨1⟩ id + ⟨1⟩) :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', TransferBudget root credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨15658⟩
        (solcMappingSlot ⟨1⟩ id :: (solcMappingSlot ⟨1⟩ id + ⟨1⟩) :: R)
        mem aw rdata (claimFeeCreditState evm id amount).accountMap k' C' := by
  obtain ⟨k', C', hb', rd'⟩ := claim_block_15626_funded hstack hperm (by jump_dest) hb rd
  simp only [midnightBlocks.midnight_block_15626_stack, uint128Mask_computed,
    u256_land_comm (UInt256.lnot uint128Mask), shiftLeft128_highMask,
    u256_land_comm uint128Mask,
    u256_lor_comm (UInt256.shiftLeft (claimFeeCredit evm id amount) (UInt256.ofNat 128))] at rd'
  refine ⟨k', C', hb', ?_⟩
  simpa only [claimFeeCreditState, marketBalanceStore, marketBalanceSlot,
    show (2 : Fin 3).val = 2 from rfl, show ¬ (2 : Nat) = 0 from by decide,
    if_false, if_true, storeHigh128_accounts, henv, storeHigh128Accounts,
    setUint128HighWord] using rd'

theorem midnightClaimFeeWriteUnits {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {evm : EVM.State} {mem rdata : ByteArray} {aw root id amount market receiver : UInt256}
    {credit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 13 ≤ 1024) (hperm : I.perm = true)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨15678⟩
      ([claimFeeUnits evm id amount, uint128Mask, solcMappingSlot ⟨1⟩ id,
        solcMappingSlot ⟨1⟩ id + ⟨1⟩, id, market, ⟨64⟩, solcAddrMask, receiver,
        amount, ⟨15786⟩] ++ R) mem aw rdata (claimFeeCreditState evm id amount).accountMap k C) :
    ∃ k' C', TransferBudget root credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨23403⟩
        ([amount, ⟨3993⟩, ⟨15714⟩, uint128Mask, solcMappingSlot ⟨1⟩ id + ⟨1⟩,
          id, market, ⟨64⟩, solcAddrMask, receiver, amount, ⟨15786⟩] ++ R)
        mem aw rdata (claimFeeUnitsState evm id amount).accountMap k' C' := by
  change RD fork _ _ _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: R)
    _ _ _ _ _ _ at rd
  obtain ⟨k', C', hb', rd'⟩ := claim_block_15678_funded
    (by simp only [List.length_cons]; omega) hperm (by jump_dest) hb rd
  simp only [midnightBlocks.midnight_block_15678_stack, uint128Mask_computed] at rd'
  refine ⟨k', C', hb', ?_⟩
  simpa only [claimFeeUnitsState, marketBalanceStore, marketBalanceSlot,
    show (0 : Fin 3).val = 0 from rfl, show ¬ (0 : Nat) = 2 from by decide,
    if_false, if_true, storeLow128_accounts, claimFeeCreditState_env, henv,
    storeLow128Accounts, setUint128LowWord] using rd'

theorem midnightClaimFeeReadLow {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {evm : EVM.State} {mem rdata : ByteArray} {aw amount ret id : UInt256}
    {k C : Nat} {R : List UInt256} (i : Fin 3) (hi : i.val ≠ 2)
    (henv : evm.executionEnv = I) (hstack : R.length + 6 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨3993⟩
      (amount :: ret :: uint128Mask :: marketBalanceSlot id i :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨19743⟩
      (marketBalanceWord evm id i :: amount :: ret :: uint128Mask ::
        marketBalanceSlot id i :: R) mem aw rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hC, rd'⟩ := midnightReadLow128Sub hstack rd
  refine ⟨k', C', hC, ?_⟩
  simpa only [marketBalanceWord, hi, if_false, low128,
    storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (congrArg ExecutionEnv.codeOwner henv)]
    using rd'

theorem midnightClaimFeeWriteWithdrawable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {evm : EVM.State} {mem rdata : ByteArray} {aw root id amount market receiver : UInt256}
    {credit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 12 ≤ 1024) (hperm : I.perm = true)
    (hfree : memLoad ⟨64⟩ mem = root) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨15714⟩
      ([claimFeeWithdrawable evm id amount, uint128Mask, solcMappingSlot ⟨1⟩ id + ⟨1⟩,
        id, market, ⟨64⟩, solcAddrMask, receiver, amount, ⟨15786⟩] ++ R)
      mem aw rdata (claimFeeUnitsState evm id amount).accountMap k C) :
    ∃ aw' k' C', TransferBudget root credit (writeWord mem root.toNat amount) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨23236⟩
        ([UInt256.land (memLoad (market + ⟨64⟩) (writeWord mem root.toNat amount)) solcAddrMask,
          receiver, amount, ⟨15786⟩] ++ R)
        (writeWord mem root.toNat amount) aw' rdata (claimFeeFinalState evm id amount).accountMap
        k' C' := by
  change RD fork _ _ _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: R)
    _ _ _ _ _ _ at rd
  obtain ⟨k', C', hb', rd'⟩ := claim_block_15714_funded
    (by simp only [List.length_cons]; omega) hperm (by jump_dest) hb rd
  simp only [midnightBlocks.midnight_block_15714_stack,
    midnightBlocks.midnight_block_15714_memory, uint128Mask_computed, hfree] at hb' rd'
  refine ⟨_, k', C', hb', ?_⟩
  simpa only [claimFeeFinalState, marketBalanceStore, marketBalanceSlot,
    show (1 : Fin 3).val = 1 from rfl, show ¬ (1 : Nat) = 2 from by decide,
    show ¬ (1 : Nat) = 0 from by decide, if_false, storeLow128_accounts,
    claimFeeUnitsState_env, henv, storeLow128Accounts, setUint128LowWord] using rd'

end Benchmarks.Midnight
