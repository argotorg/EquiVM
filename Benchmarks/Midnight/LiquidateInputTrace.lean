import Benchmarks.Midnight.LiquidatePositionBudget
import Benchmarks.Midnight.RuntimeBlocks_033

variable {fork : Ethereum.Fork}

/-! The liquidation input check and its short-circuit bytecode branches. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem midnightLiquidatePosition {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id borrower dl dp budgetRoot : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hm : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hc : borrower.toNat < EVM.addressModulus)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode ee g s0 ⟨5161⟩ (id :: dl :: borrower :: dp :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot credit (liquidatePositionMemory mem id borrower)
      aw' C' ∧ RD fork midnightBytecode ee g s0 ⟨5248⟩
      ((if calldataWord ee.calldata 100 = ⟨0⟩ then ⟨1⟩
        else UInt256.isZero (calldataWord ee.calldata 68)) ::
        UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)) ::
        positionSlot id borrower :: dp :: dl :: borrower ::
        UInt256.isZero (calldataWord ee.calldata 100) :: R)
      (liquidatePositionMemory mem id borrower) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, hb1, rd1⟩ := liquidatePositionBlock_budget hstack hm hz hc hb rd
  by_cases hr : calldataWord ee.calldata 100 = ⟨0⟩
  · rw [if_pos hr] at rd1
    exact ⟨_, _, _, hb1, by simpa only [hr, if_pos rfl] using rd1⟩
  · rw [if_neg hr] at rd1
    have rd2 := midnight_block_8453 (by simp only [List.length_cons]; omega)
      (by jump_dest) rd1
    have hb2 := transferBudgetAt rd2 (hb1.mono (by omega))
    refine ⟨aw1, k1 + 7, C1 + 23, hb2, ?_⟩
    simpa only [midnight_block_8453_stack, if_neg hr] using rd2

theorem midnightLiquidateInputGuard {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id borrower dl dp budgetRoot : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hm : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hc : borrower.toNat < EVM.addressModulus)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode ee g s0 ⟨5161⟩ (id :: dl :: borrower :: dp :: R)
      mem aw rdata σ k C) :
    (¬ (calldataWord ee.calldata 100 = ⟨0⟩ ∨ calldataWord ee.calldata 68 = ⟨0⟩) ∧
      RDrev fork midnightBytecode g s0) ∨
    ((calldataWord ee.calldata 100 = ⟨0⟩ ∨ calldataWord ee.calldata 68 = ⟨0⟩) ∧
      ∃ aw' k' C', TransferBudget budgetRoot credit (liquidatePositionMemory mem id borrower)
        aw' C' ∧ RD fork midnightBytecode ee g s0 ⟨5254⟩
        (UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)) ::
          positionSlot id borrower :: dp :: dl :: borrower ::
          UInt256.isZero (calldataWord ee.calldata 100) :: R)
        (liquidatePositionMemory mem id borrower) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, hb1, rd1⟩ := midnightLiquidatePosition hstack hm hz hc hb rd
  by_cases hi : calldataWord ee.calldata 100 = ⟨0⟩ ∨ calldataWord ee.calldata 68 = ⟨0⟩
  · have hv : UInt256.isZero (if calldataWord ee.calldata 100 = ⟨0⟩ then ⟨1⟩
        else UInt256.isZero (calldataWord ee.calldata 68)) = ⟨0⟩ := by
      rcases hi with hr | hs
      · rw [if_pos hr]; decide
      · rw [hs]; split <;> decide
    have rd2 := midnight_block_5248_fallthrough (by simp only [List.length_cons]; omega) hv rd1
    exact Or.inr ⟨hi, _, _, _, hb1.mono (by omega), rd2⟩
  · have hr : calldataWord ee.calldata 100 ≠ ⟨0⟩ := fun h ↦ hi (Or.inl h)
    have hs : calldataWord ee.calldata 68 ≠ ⟨0⟩ := fun h ↦ hi (Or.inr h)
    have hv : UInt256.isZero (if calldataWord ee.calldata 100 = ⟨0⟩ then ⟨1⟩
        else UInt256.isZero (calldataWord ee.calldata 68)) ≠ ⟨0⟩ := by
      rw [if_neg hr, isZero_eq_zero_of_ne hs]; decide
    have rd2 := midnight_block_5248_taken (by simp only [List.length_cons]; omega)
      hv (by jump_dest) rd1
    exact Or.inl ⟨hi, midnight_block_8432 (by
      simp only [midnight_block_5248_taken_stack, List.length_cons]; omega) rd2⟩

end Benchmarks.Midnight
