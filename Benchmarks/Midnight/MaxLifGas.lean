import Benchmarks.Midnight.MaxLifTrace
import Benchmarks.Midnight.CheckedMulGas

/-! The maxLif routine retains the caller's accumulated execution cost. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightMaxLif_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw lltv cursor ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨24250⟩ (lltv :: cursor :: ret :: R)
      mem aw rdata σ k C) :
    (¬ MaxLifSafe lltv cursor ∧ RDrev midnightBytecode g s0) ∨
    (MaxLifSafe lltv cursor ∧ ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (maxLif lltv cursor :: R) mem aw rdata σ k' C') := by
  by_cases hsub : lltv.toNat ≤ lifScale.toNat
  · have rd1 := midnightBlocks.midnight_block_24250_fallthrough (by
      simp only [List.length_cons]; omega) (subGuard_of_le hsub) rd
    simp only [midnightBlocks.midnight_block_24250_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_24277 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_24277_stack] at rd2
    by_cases hmul : cursor.toNat * (UInt256.sub lifScale lltv).toNat < UInt256.size
    · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedMul_mono (by simp only [List.length_cons]; omega)
        hmul (by jump_dest) rd2
      by_cases hsub2 : (lifDiscount lltv cursor).toNat ≤ lifScale.toNat
      · have rd4 := midnightBlocks.midnight_block_24295_fallthrough (by
          simp only [List.length_cons]; omega) (subGuard_of_le hsub2) rd3
        simp only [midnightBlocks.midnight_block_24295_fallthrough_stack] at rd4
        by_cases hlt : (lifDiscount lltv cursor).toNat < lifScale.toNat
        · right
          refine ⟨⟨hsub, hmul, hlt⟩, ?_⟩
          have rd5 := midnightBlocks.midnight_block_24322_fallthrough (by
            simp only [List.length_cons]; omega)
            (isZero_eq_zero_of_ne (lifDenominator_ne_zero hlt)) rd4
          simp only [midnightBlocks.midnight_block_24322_fallthrough_stack] at rd5
          have rd6 := midnightBlocks.midnight_block_24344 (by omega) hret rd5
          exact ⟨_, _, by omega, rd6⟩
        · left
          refine ⟨fun hs ↦ hlt hs.2.2, ?_⟩
          have he : lifDiscount lltv cursor = lifScale := u256_inj (by omega)
          have hz : UInt256.sub lifScale (lifDiscount lltv cursor) = ⟨0⟩ := by
            rw [he]; exact u256_sub_self _
          have rd5 := midnightBlocks.midnight_block_24322_taken (by
            simp only [List.length_cons]; omega) (by
            change UInt256.isZero (UInt256.sub lifScale (lifDiscount lltv cursor)) ≠ ⟨0⟩
            rw [hz]; decide)
              (by jump_dest) rd4
          exact midnightBlocks.midnight_block_19401 (by
            simp only [midnightBlocks.midnight_block_24322_taken_stack, List.length_cons]; omega) rd5
      · left
        refine ⟨fun hs ↦ hsub2 (Nat.le_of_lt hs.2.2), ?_⟩
        have rd4 := midnightBlocks.midnight_block_24295_taken (by
          simp only [List.length_cons]; omega) (by
            change UInt256.gt (UInt256.sub lifScale (lifDiscount lltv cursor)) lifScale ≠ ⟨0⟩
            rw [subGuard_of_lt (Nat.lt_of_not_ge hsub2)]; decide) (by jump_dest) rd3
        exact midnightBlocks.midnight_block_7302 (by
          simp only [midnightBlocks.midnight_block_24295_taken_stack, List.length_cons]; omega) rd4
    · exact Or.inl ⟨fun hs ↦ hmul hs.2.1, midnightCheckedMulRevert
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hmul) rd2⟩
  · left
    refine ⟨fun hs ↦ hsub hs.1, ?_⟩
    have rd1 := midnightBlocks.midnight_block_24250_taken (by
      simp only [List.length_cons]; omega) (by
        change UInt256.gt (UInt256.sub lifScale lltv) lifScale ≠ ⟨0⟩
        rw [subGuard_of_lt (Nat.lt_of_not_ge hsub)]; decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_7302 (by
      simp only [midnightBlocks.midnight_block_24250_taken_stack, List.length_cons]; omega) rd1


end Benchmarks.Midnight
