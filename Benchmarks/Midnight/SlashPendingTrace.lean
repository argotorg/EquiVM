import Benchmarks.Midnight.PositionViewValues
import Benchmarks.Midnight.MulDivTrace
import Benchmarks.Midnight.RuntimeBlocks_085
import Benchmarks.Midnight.RuntimeBlocks_086

/-! Success and revert paths for pending-fee slashing. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightSlashPending {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw word0 credit word1 postCredit ret ptr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨22948⟩
      (word0 :: credit :: word1 :: postCredit :: ⟨23076⟩ :: ret :: uint128Mask :: ptr :: R)
      mem aw rdata σ k C) :
    let pending := UInt256.shiftRight word0 ⟨128⟩
    (¬ SlashPendingSafe credit pending postCredit ∧ RDrev midnightBytecode g s0) ∨
    (SlashPendingSafe credit pending postCredit ∧ ∃ k' C',
      RD midnightBytecode I g s0 ⟨22992⟩
        (ptr :: ⟨128⟩ :: word1 :: postCredit :: ⟨23076⟩ :: ret :: uint128Mask ::
          slashPending credit pending postCredit :: R) mem aw rdata σ k' C') := by
  let pending := UInt256.shiftRight word0 ⟨128⟩
  by_cases hpos : 0 < credit.toNat
  · have hnz : credit ≠ ⟨0⟩ := by intro hz; rw [hz] at hpos; contradiction
    have rd1 := midnightBlocks.midnight_block_22948_fallthrough (by
      simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hnz) rd
    simp only [midnightBlocks.midnight_block_22948_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_22959 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_22959_stack] at rd2
    by_cases hsub : postCredit.toNat ≤ credit.toNat
    · obtain ⟨k3, C3, rd3⟩ := midnightCheckedSub (by simp only [List.length_cons]; omega)
        hsub (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_22978 (by
        simp only [List.length_cons]; omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_22978_stack] at rd4
      rcases midnightMulDivUp (by simp only [List.length_cons]; omega) (by jump_dest) rd4 with
        ⟨hbad, hr⟩ | ⟨hsafe, k5, C5, rd5⟩
      · exact Or.inl ⟨fun h ↦ hbad (h hpos).2.1, hr⟩
      · have rd6 := midnightBlocks.midnight_block_22984 (by
          simp only [List.length_cons]; omega) (by jump_dest) rd5
        simp only [midnightBlocks.midnight_block_22984_stack] at rd6
        by_cases hdecrease : (mulDivUp pending (UInt256.sub credit postCredit) credit).toNat ≤
            pending.toNat
        · obtain ⟨k7, C7, rd7⟩ := midnightCheckedSub (by simp only [List.length_cons]; omega)
            hdecrease (by jump_dest) rd6
          have rd8 := midnightBlocks.midnight_block_22990 (by omega) rd7
          refine Or.inr ⟨(fun _ ↦ ⟨hsub, hsafe, hdecrease⟩), k7 + 2, C7 + 4, ?_⟩
          simpa only [midnightBlocks.midnight_block_22990_stack, slashPending, hpos, if_true]
            using rd8
        · exact Or.inl ⟨fun h ↦ hdecrease (h hpos).2.2,
            midnightCheckedSubRevert (by simp only [List.length_cons]; omega)
              (Nat.lt_of_not_ge hdecrease) rd6⟩
    · exact Or.inl ⟨fun h ↦ hsub (h hpos).1,
        midnightCheckedSubRevert (by simp only [List.length_cons]; omega) (by omega) rd2⟩
  · have hz : credit = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
    have rd1 := midnightBlocks.midnight_block_22948_taken (by
      simp only [List.length_cons]; omega) (by rw [hz]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_22948_taken_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_23097 (by omega) (by jump_dest) rd1
    refine Or.inr ⟨(fun h ↦ False.elim (hpos h)), k + 8 + 8, C + 29 + 24, ?_⟩
    simpa only [midnightBlocks.midnight_block_23097_stack, slashPending, hpos, if_false]
      using rd2

end Benchmarks.Midnight
