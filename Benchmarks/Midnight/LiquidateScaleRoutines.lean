import Benchmarks.Midnight.LiquidateScales
import Benchmarks.Midnight.MaxLifGas

variable {fork : Ethereum.Fork}

/-! Shared checked arithmetic routines for liquidation's fixed scales. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightAddPriceScalePred {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨19508⟩ (x :: ret :: R) mem aw rdata σ k C) :
    (¬ x.toNat + (UInt256.sub liquidatePriceScale ⟨1⟩).toNat < UInt256.size ∧
      RDrev fork midnightBytecode g s0) ∨
    (x.toNat + (UInt256.sub liquidatePriceScale ⟨1⟩).toNat < UInt256.size ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ret ((x + UInt256.sub liquidatePriceScale ⟨1⟩) :: R)
        mem aw rdata σ k' C') := by
  by_cases ha : x.toNat + (UInt256.sub liquidatePriceScale ⟨1⟩).toNat < UInt256.size
  · have hg : UInt256.gt x (x + UInt256.ofNat 999999999999999999999999999999999999) = ⟨0⟩ := by
      rw [u256_add_comm]
      exact checkedAddNoOverflowGt _ _ ha
    have rd1 := midnightBlocks.midnight_block_19508_fallthrough hstack hg rd
    simp only [midnightBlocks.midnight_block_19508_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_19535
      (by simp only [List.length_cons]; omega) hret rd1
    exact Or.inr ⟨ha, _, _, by omega, rd2⟩
  · have hg : UInt256.gt x (x + UInt256.ofNat 999999999999999999999999999999999999) ≠ ⟨0⟩ := by
      rw [u256_add_comm]
      change UInt256.gt x (UInt256.sub liquidatePriceScale ⟨1⟩ + x) ≠ ⟨0⟩
      rw [checkedAddOverflowGt _ _ (Nat.le_of_not_gt ha)]
      decide
    have rr := midnightBlocks.midnight_block_19508_taken hstack hg (by jump_dest) rd
    exact Or.inl ⟨ha, midnightBlocks.midnight_block_7302
      (by simp only [midnightBlocks.midnight_block_19508_taken_stack, List.length_cons]; omega) rr⟩

theorem midnightMulLifScale {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨20377⟩ (x :: ret :: R) mem aw rdata σ k C) :
    (¬ x.toNat * lifScale.toNat < UInt256.size ∧ RDrev fork midnightBytecode g s0) ∨
    (x.toNat * lifScale.toNat < UInt256.size ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ret (UInt256.mul x lifScale :: R) mem aw rdata σ k' C') := by
  by_cases hm : x.toNat * lifScale.toNat < UInt256.size
  · have rd1 := midnightBlocks.midnight_block_20377_fallthrough hstack (checkedMulGuardInline hm) rd
    simp only [midnightBlocks.midnight_block_20377_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_20412
      (by simp only [List.length_cons]; omega) hret rd1
    exact Or.inr ⟨hm, _, _, by omega, rd2⟩
  · have hg : UInt256.isZero (UInt256.lor (UInt256.isZero x)
        (UInt256.eq lifScale (UInt256.div (UInt256.mul x lifScale) x))) ≠ ⟨0⟩ := by
      rw [u256_lor_comm, uInt256_eq_comm lifScale,
        checkedMulGuard_overflow (Nat.le_of_not_gt hm)]
      decide
    have rr := midnightBlocks.midnight_block_20377_taken hstack hg (by jump_dest) rd
    exact Or.inl ⟨hm, midnightBlocks.midnight_block_7302
      (by simp only [midnightBlocks.midnight_block_20377_taken_stack, List.length_cons]; omega) rr⟩

end Benchmarks.Midnight
