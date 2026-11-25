import Benchmarks.Midnight.TakeBuyerPendingSource
import Benchmarks.Midnight.CheckedMulGas
import Benchmarks.Midnight.CheckedArithmeticRevert
import Benchmarks.Midnight.CheckedUint128Gas

variable {fork : Ethereum.Fork}

/-! Checked products, division, and narrowing for the buyer's pending fee. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeBuyerPendingRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw rate time credit buyerSlot debt buyerDebt sellerSlot marketSlot decrease ratifierPtr
      increase : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨20413⟩
      ([rate, time, UInt256.ofNat 12138, UInt256.ofNat 12144, takePendingScale, UInt256.ofNat 12150,
        credit, buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr,
        increase] ++ R) mem aw rdata σ k C) :
    (¬ TakeBuyerPendingSafe rate time increase ∧ RDrev fork midnightBytecode g s0) ∨
    (TakeBuyerPendingSafe rate time increase ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨12150⟩
        ([takeBuyerPendingValue rate time increase, credit, buyerSlot, debt, buyerDebt,
          sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
        mem aw rdata σ k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hfit : rate.toNat * time.toNat < UInt256.size
  · obtain ⟨k1, C1, hC1, rd1⟩ := midnightCheckedMul_mono
      (by simp only [List.length_cons]; omega) hfit (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_12138 (by omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_12138_stack] at rd2
    by_cases hprod : increase.toNat * (UInt256.mul rate time).toNat < UInt256.size
    · obtain ⟨k3, C3, hC3, rd3⟩ := midnightCheckedMul_mono
        (by simp only [List.length_cons]; omega) hprod (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_12144
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_12144_stack] at rd4
      by_cases hsmall : (takeBuyerPendingValue rate time increase).toNat < 2^128
      · obtain ⟨k5, C5, hC5, rd5⟩ := midnightToUint128_mono
          (by simp only [List.length_cons]; omega) hsmall (by jump_dest) rd4
        exact Or.inr ⟨⟨hfit, hprod, hsmall⟩, k5, C5, by omega, rd5⟩
      · exact Or.inl ⟨fun h ↦ hsmall h.2.2, midnightToUint128Revert
          (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hsmall) rd4⟩
    · exact Or.inl ⟨fun h ↦ hprod h.2.1, midnightCheckedMulRevert
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hprod) rd2⟩
  · exact Or.inl ⟨fun h ↦ hfit h.1, midnightCheckedMulRevert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hfit) rd⟩

end Benchmarks.Midnight
