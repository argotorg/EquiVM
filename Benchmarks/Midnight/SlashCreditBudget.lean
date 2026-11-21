import Benchmarks.Midnight.SlashCreditTrace
import Benchmarks.Midnight.SlashCreditArithmeticGas
import Benchmarks.Midnight.PositionReadBlocksBudget

/-! Credit slashing retains the memory funding needed after a position update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightSlashCredit_budget {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr id user ret : UInt256} {budgetRoot : UInt256} {credit : Nat} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 16 ≤ 1024)
    (hsize : 64 ≤ mem.size) (hcanon : user.toNat < EVM.addressModulus)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨22775⟩ (ptr :: id :: user :: ret :: R)
      mem aw rdata σ k C) :
    let w0 := solcSlotWordAt (positionSlot id user) σ I
    let w1 := solcSlotWordAt (positionSlot id user + ⟨1⟩) σ I
    let loss := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) ⟨128⟩
    ∃ aw' k' C',
      TransferBudget budgetRoot credit (positionSlashMemory mem id user (low128 w1)) aw' C' ∧
      RD midnightBytecode I g s0 ⟨22948⟩
      ([w0, low128 w0, w1, slashCredit (low128 w0) (low128 w1) loss,
        ⟨23076⟩, ret, uint128Mask, ptr] ++ R)
      (positionSlashMemory mem id user (low128 w1)) aw' rdata σ k' C' := by
  let w0 := solcSlotWordAt (positionSlot id user) σ I
  let w1 := solcSlotWordAt (positionSlot id user + ⟨1⟩) σ I
  let loss := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) ⟨128⟩
  have hh0 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) = solcMappingSlot ⟨0⟩ id :=
    twoWordHashMem_mapSlot_of_ge64 id ⟨0⟩ hsize
  have hs0 : 64 ≤ (twoWordHashMem id ⟨0⟩ mem).size := by
    rw [twoWordHashMem_size_of_ge_64 _ _ hsize]; exact hsize
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem user (solcMappingSlot ⟨0⟩ id) (twoWordHashMem id ⟨0⟩ mem)) =
      positionSlot id user := twoWordHashMem_mapSlot_of_ge64 user (solcMappingSlot ⟨0⟩ id) hs0
  by_cases hlast : (low128 w1).toNat < 2 ^ 128 - 1
  · have hc : UInt256.eq ⟨0⟩ (UInt256.lt (low128 w1) uint128Mask) = ⟨0⟩ := by
      rw [ult_one hlast]; decide
    obtain ⟨k1, C1, hb1, rd1⟩ := position_block_22775_fallthrough_budget (by omega)
      (by
        simp only [addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl,
          wordAt0_fold, twoWordHash_fold, hh0, hh1]
        exact hc) hb rd
    simp only [midnightBlocks.midnight_block_22775_fallthrough_stack,
      midnightBlocks.midnight_block_22775_fallthrough_memory,
      addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl,
      wordAt0_fold, twoWordHash_fold, hh0, hh1] at rd1 hb1
    have hsr : 64 ≤ (positionReadMemory mem id user).size := by
      rw [positionReadMemory_size _ _ _ hsize]; exact hsize
    have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) (positionReadMemory mem id user)) =
        solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 id ⟨1⟩ hsr
    obtain ⟨k2, C2, hb2, rd2⟩ := position_block_22854_fallthrough_budget
      (by simp only [List.length_cons]; omega) (by
        simp only [uint128Mask_computed,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold]
        change UInt256.gt (complement128
          (UInt256.shiftRight (solcSlotWordAt
            (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) (positionReadMemory mem id user))) σ I)
            ⟨128⟩)) uint128Mask = ⟨0⟩
        rw [hh2]
        exact complement128_guard (shiftRight128_lt _)) hb1 rd1
    simp only [midnightBlocks.midnight_block_22854_fallthrough_stack,
      midnightBlocks.midnight_block_22854_fallthrough_memory, uint128Mask_computed,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl,
      wordAt0_fold, twoWordHash_fold] at rd2 hb2
    unfold positionReadMemory at hh2
    rw [hh2] at rd2
    change RD midnightBytecode I g s0 ⟨22893⟩
      (low128 w1 :: w1 :: w0 :: complement128 loss :: ret :: low128 w0 :: ptr :: R)
      (twoWordHashMem id (UInt256.ofNat 1) (positionReadMemory mem id user)) _ rdata σ k2 C2 at rd2
    obtain ⟨k3, C3, hc3, rd3⟩ := midnightSlashCreditArithmetic_mono hstack (low128_lt _)
      (complement128_lt (shiftRight128_lt _)) hlast rd2
    dsimp only [w1] at hlast
    simp only [slashCredit, positionSlashMemory, hlast, if_true]
    exact ⟨_, _, _, hb2.mono hc3, rd3⟩
  · have hc : UInt256.eq ⟨0⟩ (UInt256.lt (low128 w1) uint128Mask) ≠ ⟨0⟩ := by
      rw [ult_zero (by change 2 ^ 128 - 1 ≤ (low128 w1).toNat; omega)]
      decide
    obtain ⟨k1, C1, hb1, rd1⟩ := position_block_22775_taken_budget (by omega)
      (by
        simp only [addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl,
          wordAt0_fold, twoWordHash_fold, hh0, hh1]
        exact hc) (by jump_dest) hb rd
    simp only [midnightBlocks.midnight_block_22775_taken_stack,
      midnightBlocks.midnight_block_22775_taken_memory,
      addressMask_computed, solcAddrMask_clean hcanon, uint128Mask_computed,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl,
      wordAt0_fold, twoWordHash_fold, hh0, hh1] at rd1 hb1
    have rd2 := midnightBlocks.midnight_block_23108 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_23108_stack, uint128Mask_computed] at rd2
    dsimp only [w1] at hlast
    simp only [slashCredit, positionSlashMemory, hlast, if_false]
    refine ⟨_, _, _, ?_, rd2⟩
    exact hb1.mono (by omega)

end Benchmarks.Midnight
