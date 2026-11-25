import Benchmarks.Midnight.PositionUpdateWrites
import Benchmarks.Midnight.PositionWriteBlocksBudget
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.CheckedExtraGas

variable {fork : Ethereum.Fork}

/-! Position-update bookkeeping with retained transfer funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionUpdateWrites_budget {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id user credit pending fee creditDecrease pendingDecrease ret : UInt256}
    {budgetRoot : UInt256} {gasCredit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hmem : 64 ≤ mem.size) (hperm : I.perm = true)
    (hb : TransferBudget budgetRoot gasCredit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨23723⟩
      ([pendingDecrease, ⟨23855⟩, positionSlot id user, user, solcAddrMask, ⟨96⟩,
        updatePositionTopic, id, creditDecrease, credit, ret, fee, pending] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      TransferBudget budgetRoot gasCredit (twoWordHashMem id (UInt256.ofNat 1) mem) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨23855⟩
      ([pendingDecrease, user, solcAddrMask, ⟨96⟩, updatePositionTopic, id, creditDecrease,
        credit, ret, fee, pending] ++ R)
      (twoWordHashMem id (UInt256.ofNat 1) mem) aw' rdata
      (positionUpdateAccounts σ I id user credit pending) k' C' := by
  change RD fork midnightBytecode I g s0 ⟨23723⟩
    (pendingDecrease :: ⟨23855⟩ :: positionSlot id user :: user :: solcAddrMask :: ⟨96⟩ ::
      updatePositionTopic :: id :: creditDecrease :: credit :: ret :: fee :: pending :: R)
    mem aw rdata σ k C at rd
  obtain ⟨k1, C1, hb1, rd1⟩ := position_block_23723_budget hstack hperm hb rd
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 id (UInt256.ofNat 1) hmem
  simp only [midnightBlocks.midnight_block_23723_stack, midnightBlocks.midnight_block_23723_memory,
    uint128Mask_computed, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh] at rd1 hb1
  obtain ⟨k2, C2, hb2, rd2⟩ := position_block_23809_budget
    (by simp only [List.length_cons]; omega) hperm (by jump_dest) hb1 rd1
  simp only [midnightBlocks.midnight_block_23809_stack, shiftLeft128_highMask] at rd2
  obtain ⟨k3, C3, hb3, rd3⟩ := position_block_23825_budget
    (by simp only [List.length_cons]; omega) hperm (by jump_dest) hb2 rd2
  simp only [midnightBlocks.midnight_block_23825_stack, uint128Mask_computed,
    u256_land_comm (UInt256.lnot uint128Mask), shiftLeft128_highMask,
    u256_land_comm uint128Mask, u256_lor_comm (UInt256.shiftLeft (UInt256.ofNat I.header.timestamp)
      (UInt256.ofNat 128))] at rd3
  exact ⟨_, _, _, hb3, rd3⟩

end Benchmarks.Midnight
