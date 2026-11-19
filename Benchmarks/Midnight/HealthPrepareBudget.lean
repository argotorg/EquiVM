import Benchmarks.Midnight.HealthPrepareBlocksBudget
import Benchmarks.Midnight.PositionUpdateMemory
import Benchmarks.Midnight.RuntimeBlocks_075
import Benchmarks.Midnight.RuntimeBlocks_076

/-! The health-check position lookup and debt guard, with memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

set_option maxHeartbeats 400000 in
theorem midnightHealthPrepare_budget {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw market id user ret budgetRoot : UInt256} {credit : Nat} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hmem : 64 ≤ mem.size) (hcanon : user.toNat < EVM.addressModulus)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19775⟩ (market :: id :: user :: ret :: R)
      mem aw rdata σ k C) :
    let w := solcSlotWordAt (positionSlot id user + ⟨2⟩) σ I
    (low128 w = ⟨0⟩ ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit (positionReadMemory mem id user) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19831⟩
      ([w, market, positionSlot id user, ⟨0⟩, ⟨0⟩, ret] ++ R)
      (positionReadMemory mem id user) aw' rdata σ k' C') ∨
    (low128 w ≠ ⟨0⟩ ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit (positionReadMemory mem id user) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19847⟩
      ([positionSlot id user + ⟨3⟩, market, UInt256.shiftRight w (UInt256.ofNat 128),
        ⟨0⟩, low128 w, ret] ++ R)
      (positionReadMemory mem id user) aw' rdata σ k' C') := by
  dsimp only
  let w := solcSlotWordAt (positionSlot id user + ⟨2⟩) σ I
  have hh0 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
      solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 id ⟨0⟩ hmem
  have hs0 : 64 ≤ (twoWordHashMem id ⟨0⟩ mem).size := by
    rw [twoWordHashMem_size_of_ge_64 _ _ hmem]; exact hmem
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem user (solcMappingSlot ⟨0⟩ id) (twoWordHashMem id ⟨0⟩ mem)) =
      positionSlot id user := twoWordHashMem_mapSlot_of_ge64 user (solcMappingSlot ⟨0⟩ id) hs0
  by_cases hz : low128 w = ⟨0⟩
  · obtain ⟨k1, C1, hb1, rd1⟩ := health_block_19775_fallthrough_budget
      (by simp only [List.length_cons]; omega) (by
        simp only [addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl,
          wordAt0_fold, twoWordHash_fold, hh0, hh1]
        exact hz) hb rd
    simp only [midnightBlocks.midnight_block_19775_fallthrough_stack,
      midnightBlocks.midnight_block_19775_fallthrough_memory,
      addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl,
      wordAt0_fold, twoWordHash_fold, hh0, hh1] at rd1 hb1
    change RD midnightBytecode I g s0 ⟨19831⟩
      (w :: market :: positionSlot id user :: ⟨0⟩ :: low128 w :: ret :: R)
      (positionReadMemory mem id user) _ rdata σ k1 C1 at rd1
    rw [hz] at rd1
    exact Or.inl ⟨hz, _, _, _, hb1, rd1⟩
  · obtain ⟨k1, C1, hb1, rd1⟩ := health_block_19775_taken_budget
      (by simp only [List.length_cons]; omega) (by
        simp only [addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl,
          wordAt0_fold, twoWordHash_fold, hh0, hh1]
        exact hz) (by jump_dest) hb rd
    simp only [midnightBlocks.midnight_block_19775_taken_stack,
      midnightBlocks.midnight_block_19775_taken_memory,
      addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl,
      wordAt0_fold, twoWordHash_fold, hh0, hh1] at rd1 hb1
    have rd2 := midnightBlocks.midnight_block_19839
      (by simp only [List.length_cons]; omega) rd1
    simp only [midnightBlocks.midnight_block_19839_stack] at rd2
    rw [u256_add_comm (UInt256.ofNat 3)] at rd2
    exact Or.inr ⟨hz, _, _, _, hb1.mono (by omega), rd2⟩

end Benchmarks.Midnight
