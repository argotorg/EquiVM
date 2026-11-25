import Benchmarks.Midnight.PositionViewValues
import Benchmarks.Midnight.CheckedArithmeticRevert
import Benchmarks.Midnight.RuntimeBlocks_027
import Benchmarks.Midnight.RuntimeBlocks_085
import Benchmarks.Midnight.RuntimeBlocks_086

variable {fork : Ethereum.Fork}

/-! Fee accrual, including time underflow and multiplication overflow. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionAccrual {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr word1 postCredit ret postPending maturity : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hmaturity : memLoad (ptr + UInt256.ofNat 128) mem = maturity)
    (rd : RD fork midnightBytecode I g s0 ⟨22992⟩
      (ptr :: UInt256.ofNat 128 :: word1 :: postCredit :: ⟨23076⟩ :: ret :: uint128Mask ::
        postPending :: R) mem aw rdata σ k C) :
    let last := UInt256.shiftRight word1 (UInt256.ofNat 128)
    let time := UInt256.ofNat I.header.timestamp
    (¬ PositionAccrualSafe postPending last maturity time ∧ RDrev fork midnightBytecode g s0) ∨
    (PositionAccrualSafe postPending last maturity time ∧ ∃ aw' k' C',
      let fee := positionAccruedFee postPending last maturity time
      RD fork midnightBytecode I g s0 ⟨23063⟩
        (postCredit :: uint128Mask :: fee :: ⟨23069⟩ :: uint128Mask :: fee ::
          ⟨23076⟩ :: ret :: fee :: postPending :: R) mem aw' rdata σ k' C') := by
  by_cases hlast : (UInt256.shiftRight word1 (UInt256.ofNat 128)).toNat < maturity.toNat
  · have rd1 := midnightBlocks.midnight_block_22992_fallthrough (by
      simp only [List.length_cons]; omega) (by rw [hmaturity, ult_one hlast]; rfl) rd
    simp only [midnightBlocks.midnight_block_22992_fallthrough_stack, hmaturity] at rd1
    have rd2 := midnightBlocks.midnight_block_23008 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_23008_stack, wordMin_branchless] at rd2
    by_cases hsub : (UInt256.shiftRight word1 (UInt256.ofNat 128)).toNat ≤
        (wordMin (UInt256.ofNat I.header.timestamp) maturity).toNat
    · obtain ⟨k3, C3, rd3⟩ := midnightCheckedSub (by simp only [List.length_cons]; omega)
        hsub (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_23043 (by
        simp only [List.length_cons]; omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_23043_stack, hmaturity] at rd4
      obtain ⟨k5, C5, rd5⟩ := midnightCheckedSub (by simp only [List.length_cons]; omega)
        (Nat.le_of_lt hlast) (by jump_dest) rd4
      have rd6 := midnightBlocks.midnight_block_23050 (by omega) (by jump_dest) rd5
      simp only [midnightBlocks.midnight_block_23050_stack] at rd6
      by_cases hmul : postPending.toNat *
          (UInt256.sub (wordMin (UInt256.ofNat I.header.timestamp) maturity)
            (UInt256.shiftRight word1 (UInt256.ofNat 128))).toNat < UInt256.size
      · obtain ⟨k7, C7, rd7⟩ := midnightCheckedMul (by simp only [List.length_cons]; omega)
          hmul (by jump_dest) rd6
        have rd8 := midnightBlocks.midnight_block_6721 (by
          simp only [List.length_cons]; omega) (by jump_dest) rd7
        have hnz : UInt256.sub maturity (UInt256.shiftRight word1 (UInt256.ofNat 128)) ≠ ⟨0⟩ := by
          intro hz
          have h := congrArg UInt256.toNat hz
          rw [usub_toNat (Nat.le_of_lt hlast)] at h
          change maturity.toNat - (UInt256.shiftRight word1 (UInt256.ofNat 128)).toNat = 0 at h
          omega
        obtain ⟨k9, C9, rd9⟩ := midnightCheckedDiv (by simp only [List.length_cons]; omega)
          hnz (by jump_dest) rd8
        have rd10 := midnightBlocks.midnight_block_23057 (by
          simp only [List.length_cons]; omega) rd9
        simp only [midnightBlocks.midnight_block_23057_stack] at rd10
        right
        refine ⟨fun _ ↦ ⟨hsub, hmul⟩, ?_⟩
        simp only [positionAccruedFee, hlast, if_true]
        exact ⟨_, _, _, rd10⟩
      · exact Or.inl ⟨fun h ↦ hmul (h hlast).2,
          midnightCheckedMulRevert (by simp only [List.length_cons]; omega) (by omega) rd6⟩
    · exact Or.inl ⟨fun h ↦ hsub (h hlast).1,
        midnightCheckedSubRevert (by simp only [List.length_cons]; omega)
          (Nat.lt_of_not_ge hsub) rd2⟩
  · have rd1 := midnightBlocks.midnight_block_22992_taken (by
      simp only [List.length_cons]; omega) (by
        rw [hmaturity, ult_zero (Nat.le_of_not_gt hlast)]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_22992_taken_stack, hmaturity] at rd1
    have rd2 := midnightBlocks.midnight_block_23080 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_23080_stack] at rd2
    right
    refine ⟨fun h ↦ False.elim (hlast h), ?_⟩
    simp only [positionAccruedFee, hlast, if_false]
    exact ⟨_, _, _, rd2⟩

end Benchmarks.Midnight
