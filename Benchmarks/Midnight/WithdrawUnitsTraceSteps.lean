import Benchmarks.Midnight.WithdrawUnitsBalanceState
import Benchmarks.Midnight.WithdrawUnitsWriteBlocksGas
import Benchmarks.Midnight.CheckedUint128Gas

/-! Withdrawal's ordered balance reads and writes retain cumulative gas. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightWithdrawUnitsReadCredit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw units ret id user : UInt256} {k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 6 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨3993⟩
      (units :: ret :: uint128Mask :: positionSlot id user :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨19743⟩
      (positionFieldWord evm id user 0 :: units :: ret :: uint128Mask :: positionSlot id user :: R)
      mem aw rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hc, rd'⟩ := midnightReadLow128Sub hstack rd
  have hw := storageLoad_codeOwner_eq_solcSlotWordAt evm I (positionSlot id user)
    (congrArg ExecutionEnv.codeOwner henv)
  refine ⟨k', C', hc, ?_⟩
  simpa only [positionFieldWord, positionFieldSlot, show (0 : Fin 4).val < 2 by decide,
    show (0 : Fin 4).val % 2 = 0 from rfl, if_true, hw] using rd'

theorem midnightWithdrawUnitsWriteCredit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw units id user decrease market receiver : UInt256}
    {k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 14 ≤ 1024) (hperm : I.perm = true)
    (rd : RD midnightBytecode I g s0 ⟨4002⟩
      ([UInt256.sub (positionFieldWord evm id user 0) units, uint128Mask,
        positionSlot id user, solcMappingSlot ⟨1⟩ id, id, user, decrease, market,
        UInt256.ofNat 64, solcAddrMask, receiver, units] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨23403⟩
      ([units, UInt256.ofNat 4027, solcMappingSlot ⟨1⟩ id, id, user, decrease,
        market, UInt256.ofNat 64, solcAddrMask, receiver, units] ++ R)
      mem aw rdata (withdrawUnitsCreditState evm id user units).accountMap k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  obtain ⟨k', C', hc, rd'⟩ := withdraw_units_block_4002_mono hstack hperm (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_4002_stack, uint128Mask_computed] at rd'
  refine ⟨k', C', hc, ?_⟩
  simpa only [withdrawUnitsCreditState, storeLow128_accounts, henv,
    storeLow128Accounts, setUint128LowWord] using rd'

theorem midnightWithdrawUnitsReadWithdrawable {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw units id : UInt256} {k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 7 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨4027⟩ (units :: solcMappingSlot ⟨1⟩ id :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨19743⟩
      (marketBalanceWord evm id 1 :: units :: UInt256.ofNat 4052 :: uint128Mask ::
        (solcMappingSlot ⟨1⟩ id + ⟨1⟩) :: solcMappingSlot ⟨1⟩ id :: R)
      mem aw rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hc, rd'⟩ := withdraw_units_block_4027_mono hstack (by jump_dest) rd
  have hw := storageLoad_codeOwner_eq_solcSlotWordAt evm I (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
    (congrArg ExecutionEnv.codeOwner henv)
  simp only [midnightBlocks.midnight_block_4027_stack, uint128Mask_computed] at rd'
  refine ⟨k', C', hc, ?_⟩
  simpa only [marketBalanceWord, marketBalanceSlot, show (1 : Fin 3).val ≠ 0 by decide,
    show (1 : Fin 3).val ≠ 2 by decide, if_false, hw, low128] using rd'

theorem midnightWithdrawUnitsWriteWithdrawable {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw units id user decrease market receiver : UInt256}
    {k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 14 ≤ 1024) (hperm : I.perm = true)
    (rd : RD midnightBytecode I g s0 ⟨4052⟩
      ([UInt256.sub (marketBalanceWord (withdrawUnitsCreditState evm id user units) id 1) units,
        uint128Mask, solcMappingSlot ⟨1⟩ id + ⟨1⟩, solcMappingSlot ⟨1⟩ id, id, user, decrease,
        market, UInt256.ofNat 64, solcAddrMask, receiver, units] ++ R)
      mem aw rdata (withdrawUnitsCreditState evm id user units).accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨23403⟩
      ([units, UInt256.ofNat 3993, UInt256.ofNat 4088, uint128Mask,
        solcMappingSlot ⟨1⟩ id, id, user, decrease, market, UInt256.ofNat 64,
        solcAddrMask, receiver, units] ++ R)
      mem aw rdata (withdrawUnitsWithdrawableState evm id user units).accountMap k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  obtain ⟨k', C', hc, rd'⟩ := withdraw_units_block_4052_mono hstack hperm (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_4052_stack, uint128Mask_computed] at rd'
  refine ⟨k', C', hc, ?_⟩
  simpa only [withdrawUnitsWithdrawableState, storeLow128_accounts,
    withdrawUnitsCreditState_env, henv, storeLow128Accounts, setUint128LowWord] using rd'

end Benchmarks.Midnight
