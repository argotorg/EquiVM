import Benchmarks.Midnight.WithdrawUnitsReadBlocksBudget
import Benchmarks.Midnight.PositionUpdateMemory

/-! Withdrawal reads the updated position and branches on its credit balance. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightWithdrawUnitsRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root fee pending credit id user slot market receiver units : UInt256}
    {σ : AccountMap} {k C gasCredit : Nat} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root gasCredit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨3909⟩
      ([fee, pending, credit, id, user, slot, market, UInt256.ofNat 64, solcAddrMask, receiver, units] ++ R)
      mem aw rdata σ k C) :
    let w := solcSlotWordAt (positionSlot id user) σ I
    ∃ aw' k' C',
      TransferBudget root gasCredit (positionReadMemory mem id user) aw' C' ∧
      ((low128 w = ⟨0⟩ ∧ RD midnightBytecode I g s0 ⟨3971⟩
          ([w, low128 w, units, positionSlot id user, slot, id, user, ⟨0⟩, market, UInt256.ofNat 64,
            solcAddrMask, receiver, units] ++ R)
          (positionReadMemory mem id user) aw' rdata σ k' C') ∨
        (low128 w ≠ ⟨0⟩ ∧ RD midnightBytecode I g s0 ⟨4177⟩
          ([w, low128 w, units, positionSlot id user, slot, id, user, ⟨0⟩, market, UInt256.ofNat 64,
            solcAddrMask, receiver, units] ++ R)
          (positionReadMemory mem id user) aw' rdata σ k' C')) := by
  simp only [List.cons_append, List.nil_append] at rd
  have hz1 : memLoad (UInt256.ofNat 800) (wordAt0Mem id mem) = ⟨0⟩ := by
    change memLoad (UInt256.ofNat 800) (writeWord mem 0 id) = ⟨0⟩
    rw [memLoad_writeWord_preserved mem 0 (UInt256.ofNat 800) id
      hmem (Or.inr (by decide)), hzero]
  have hz2 : memLoad (UInt256.ofNat 800) (twoWordHashMem id ⟨0⟩ mem) = ⟨0⟩ := by
    rw [memLoad_twoWordHashMem id ⟨0⟩ (UInt256.ofNat 800) (by decide) hmem, hzero]
  have hz3 : memLoad (UInt256.ofNat 800) (positionReadMemory mem id user) = ⟨0⟩ := by
    rw [positionReadMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 800) (by decide)
      (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hmem), hz2]
  have hh0 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
      solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 id ⟨0⟩ (by omega)
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem user (solcMappingSlot ⟨0⟩ id) (twoWordHashMem id ⟨0⟩ mem)) =
      positionSlot id user := twoWordHashMem_mapSlot_of_ge64 _ _ (by
        rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega)
  unfold positionReadMemory at hz3
  by_cases hc : low128 (solcSlotWordAt (positionSlot id user) σ I) = ⟨0⟩
  · obtain ⟨k1, C1, hb1, rd1⟩ := withdraw_units_block_3909_fallthrough_budget hstack (by
      simp only [hzero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, hz1,
        twoWordHash_fold, hz2, hh0, hh1, uint128Mask_computed]
      exact hc) hb rd
    simp only [midnightBlocks.midnight_block_3909_fallthrough_stack,
      midnightBlocks.midnight_block_3909_fallthrough_memory, hzero,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, hz1,
      twoWordHash_fold, hz2, hh0, hh1, hz3, uint128Mask_computed] at rd1 hb1
    exact ⟨_, _, _, hb1, Or.inl ⟨hc, rd1⟩⟩
  · obtain ⟨k1, C1, hb1, rd1⟩ := withdraw_units_block_3909_taken_budget hstack (by
      simp only [hzero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, hz1,
        twoWordHash_fold, hz2, hh0, hh1, uint128Mask_computed]
      exact hc) (by jump_dest) hb rd
    simp only [midnightBlocks.midnight_block_3909_taken_stack,
      midnightBlocks.midnight_block_3909_taken_memory, hzero,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, hz1,
      twoWordHash_fold, hz2, hh0, hh1, hz3, uint128Mask_computed] at rd1 hb1
    exact ⟨_, _, _, hb1, Or.inr ⟨hc, rd1⟩⟩

end Benchmarks.Midnight
