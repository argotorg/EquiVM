import Benchmarks.Midnight.LiquidateLossTrace

variable {fork : Ethereum.Fork}

/-! The remaining-fee ratio and its checked uint128 conversion. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateRemainingFees (fee oldLoss newLoss : UInt256) : UInt256 :=
  mulDivDown fee (complement128 newLoss) (complement128 oldLoss)

theorem midnightLiquidateFeeArithmetic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw fee oldWord newLoss : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hf : fee.toNat < 2 ^ 128) (hn : newLoss.toNat < 2 ^ 128)
    (ho : (UInt256.shiftRight oldWord ⟨128⟩).toNat < 2 ^ 128 - 1)
    (rd : RD fork midnightBytecode I g s0 ⟨7694⟩
      (fee :: oldWord :: complement128 newLoss :: R) mem aw rdata σ k C) :
    let remaining := liquidateRemainingFees fee (UInt256.shiftRight oldWord ⟨128⟩) newLoss
    (2 ^ 128 ≤ remaining.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (remaining.toNat < 2 ^ 128 ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨7735⟩ (remaining :: ⟨7768⟩ :: R) mem aw rdata σ k' C') := by
  dsimp only
  have rd1 := midnightBlocks.midnight_block_7694 (R := R) (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_7694_stack, uint128Mask_computed] at rd1
  obtain ⟨k2, C2, hc2, rd2⟩ := midnightComplement128
    (by simp only [List.length_cons]; omega) (shiftRight128_lt _) (by jump_dest) rd1
  have rd3 := midnightBlocks.midnight_block_7727
    (R := ⟨4204⟩ :: ⟨7735⟩ :: ⟨7768⟩ :: R)
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_7727_stack,
    uint128Mask_clean (complement128_lt hn)] at rd3
  obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedMul_mono
    (by simp only [List.length_cons]; omega)
    (uint128_product_bound hf (complement128_lt hn)) (by jump_dest) rd3
  have rd5 := midnightBlocks.midnight_block_6721
    (by simp only [List.length_cons]; omega) (by jump_dest) rd4
  have hnz : complement128 (UInt256.shiftRight oldWord ⟨128⟩) ≠ ⟨0⟩ := by
    intro hz
    have hh := complement128_pos ho
    rw [hz] at hh
    contradiction
  obtain ⟨k6, C6, hc6, rd6⟩ := midnightCheckedDiv_mono
    (by simp only [List.length_cons]; omega) hnz (by jump_dest) rd5
  have rd7 := midnightBlocks.midnight_block_4204
    (by simp only [List.length_cons]; omega) (by jump_dest) rd6
  by_cases hfit : (liquidateRemainingFees fee (UInt256.shiftRight oldWord ⟨128⟩) newLoss).toNat < 2 ^ 128
  · obtain ⟨k8, C8, hc8, rd8⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) hfit (by jump_dest) rd7
    exact Or.inr ⟨hfit, _, _, by omega, rd8⟩
  · exact Or.inl ⟨by omega, midnightToUint128Revert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hfit) rd7⟩

end Benchmarks.Midnight
