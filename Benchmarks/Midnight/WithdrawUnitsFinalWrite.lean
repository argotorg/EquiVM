import Benchmarks.Midnight.WithdrawUnitsBalanceState
import Benchmarks.Midnight.WithdrawUnitsTransferBlockBudget
import Benchmarks.Midnight.MemoryWords

variable {fork : Ethereum.Fork}

/-! The final total-unit write and withdrawal event preserve transfer funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def withdrawUnitsLogMemory (mem : ByteArray) (root : UInt256) (I : ExecutionEnv)
    (units decrease : UInt256) : ByteArray :=
  writeWordArray mem root.toNat [UInt256.ofNat I.source.val, units, decrease]

theorem midnightWithdrawUnitsFinalWrite {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw root units id user decrease market receiver : UInt256}
    {gasCredit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 13 ≤ 1024) (hperm : I.perm = true)
    (hroot : root.toNat < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hdecrease : decrease.toNat < 2^128) (hb : TransferBudget root gasCredit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨4088⟩
      ([UInt256.sub (marketBalanceWord (withdrawUnitsWithdrawableState evm id user units) id 0)
          units, uint128Mask, solcMappingSlot ⟨1⟩ id, id, user, decrease,
        market, UInt256.ofNat 64, solcAddrMask, receiver, units] ++ R)
      mem aw rdata (withdrawUnitsWithdrawableState evm id user units).accountMap k C) :
    let mm := withdrawUnitsLogMemory mem root I units decrease
    ∃ aw' k' C', TransferBudget root gasCredit mm aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨23236⟩
        ([UInt256.land (memLoad (market + UInt256.ofNat 64) mm) solcAddrMask,
          receiver, units] ++ R) mm aw' rdata (withdrawUnitsFinalState evm id user units).accountMap
        k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  obtain ⟨k1, C1, hb1, rd1⟩ := withdraw_units_block_4088_budget hstack hperm
    (by jump_dest) hb rd
  have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega)
  have h64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat root 64 (by change _ < 2^256; omega)
  have hm : midnightBlocks.midnight_block_4088_memory (ee := I) (mem := mem)
      (x5 := decrease) (x7 := UInt256.ofNat 64) (x10 := units) =
      withdrawUnitsLogMemory mem root I units decrease := by
    simp only [midnightBlocks.midnight_block_4088_memory, hfree, h32, h64,
      uint128Mask_computed, uint128Mask_clean hdecrease]
    simp only [withdrawUnitsLogMemory, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]
  rw [hm] at rd1 hb1
  simp only [midnightBlocks.midnight_block_4088_stack, hfree, uint128Mask_computed,
    uint128Mask_clean hdecrease, h32, h64] at rd1 hb1
  refine ⟨_, k1, C1, hb1, ?_⟩
  simpa only [withdrawUnitsFinalState, storeLow128_accounts,
    withdrawUnitsWithdrawableState_env, henv, storeLow128Accounts, setUint128LowWord,
    withdrawUnitsLogMemory, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc] using rd1

end Benchmarks.Midnight
