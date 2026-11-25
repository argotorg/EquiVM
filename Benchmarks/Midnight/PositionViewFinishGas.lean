import Benchmarks.Midnight.PositionViewValues
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.RuntimeBlocks_086

variable {fork : Ethereum.Fork}

/-! The final position-view subtractions retain accumulated costs. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionViewFinish_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw postCredit postPending fee ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hfee : fee.toNat < 2 ^ 128) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨23063⟩
      (postCredit :: uint128Mask :: fee :: ⟨23069⟩ :: uint128Mask :: fee ::
        ⟨23076⟩ :: ret :: fee :: postPending :: R) mem aw rdata σ k C) :
    (¬ (fee.toNat ≤ (low128 postCredit).toNat ∧ fee.toNat ≤ (low128 postPending).toNat) ∧
      RDrev fork midnightBytecode g s0) ∨
    (fee.toNat ≤ (low128 postCredit).toNat ∧ fee.toNat ≤ (low128 postPending).toNat ∧
      ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ret
        (fee :: UInt256.sub (low128 postPending) fee :: UInt256.sub (low128 postCredit) fee :: R)
        mem aw rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_23063 (by
    simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_23063_stack] at rd1
  by_cases hcredit : fee.toNat ≤ (low128 postCredit).toNat
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedSub128_mono (by simp only [List.length_cons]; omega)
      (low128_lt _) hfee hcredit (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_23069 (by omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_23069_stack] at rd3
    by_cases hpending : fee.toNat ≤ (low128 postPending).toNat
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedSub128_mono (by simp only [List.length_cons]; omega)
        (low128_lt _) hfee hpending (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_23076 (by
        simp only [List.length_cons]; omega) hret rd4
      exact Or.inr ⟨hcredit, hpending, _, _, by omega, rd5⟩
    · exact Or.inl ⟨fun h ↦ hpending h.2,
        midnightCheckedSub128Revert (by simp only [List.length_cons]; omega)
          (low128_lt _) hfee (Nat.lt_of_not_ge hpending) rd3⟩
  · exact Or.inl ⟨fun h ↦ hcredit h.1,
      midnightCheckedSub128Revert (by simp only [List.length_cons]; omega)
        (low128_lt _) hfee (Nat.lt_of_not_ge hcredit) rd1⟩

end Benchmarks.Midnight
