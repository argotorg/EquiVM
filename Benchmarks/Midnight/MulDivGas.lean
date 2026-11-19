import Benchmarks.Midnight.CheckedMulGas
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.CheckedAddGas
import Benchmarks.Midnight.MulDiv
import Benchmarks.Midnight.CheckedArithmeticRevert
import Benchmarks.Midnight.RuntimeBlocks_027
import Benchmarks.Midnight.RuntimeBlocks_082
import Benchmarks.Midnight.RuntimeBlocks_089

/-! Complete bytecode trace of multiplication followed by rounded-up division. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulDivUp_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x y d ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨24124⟩ (x :: y :: d :: ret :: R) mem aw rdata σ k C) :
    (¬ MulDivUpSafe x y d ∧ RDrev midnightBytecode g s0) ∨
    (MulDivUpSafe x y d ∧ ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (mulDivUp x y d :: R) mem aw rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_24124 (by
    simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_24124_stack] at rd1
  by_cases hmul : x.toNat * y.toNat < UInt256.size
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedMul_mono (by simp only [List.length_cons]; omega)
      hmul (by jump_dest) rd1
    by_cases hpos : 0 < d.toNat
    · have hnz : d ≠ ⟨0⟩ := by intro hz; rw [hz] at hpos; contradiction
      have hpred : (UInt256.sub d ⟨1⟩).toNat = d.toNat - 1 :=
        usub_toNat hpos
      have hc : UInt256.gt (d + UInt256.lnot ⟨0⟩) d = ⟨0⟩ := by
        rw [u256_add_lnot_zero_eq_sub_one]
        exact ugt_zero (by rw [hpred]; omega)
      have rd3 := midnightBlocks.midnight_block_24134_fallthrough (by
        simp only [List.length_cons]; omega) hc rd2
      simp only [midnightBlocks.midnight_block_24134_fallthrough_stack,
        u256_add_lnot_zero_eq_sub_one] at rd3
      have rd4 := midnightBlocks.midnight_block_24148 (by
        simp only [List.length_cons]; omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_24148_stack] at rd4
      by_cases hadd : (UInt256.mul x y).toNat + (UInt256.sub d ⟨1⟩).toNat < UInt256.size
      · right
        refine ⟨⟨hmul, hpos, hadd⟩, ?_⟩
        obtain ⟨k5, C5, hc5, rd5⟩ := midnightCheckedAdd_mono (by simp only [List.length_cons]; omega)
          hadd (by jump_dest) rd4
        have rd6 := midnightBlocks.midnight_block_6721 (by
          simp only [List.length_cons]; omega) (by jump_dest) rd5
        obtain ⟨k7, C7, hc7, rd7⟩ := midnightCheckedDiv_mono (by simp only [List.length_cons]; omega)
          hnz (by jump_dest) rd6
        have rd8 := midnightBlocks.midnight_block_22033 (by omega) hret rd7
        exact ⟨_, _, by omega, rd8⟩
      · exact Or.inl ⟨(fun h ↦ hadd h.2.2), midnightCheckedAddRevert
          (by simp only [List.length_cons]; omega) (by omega) rd4⟩
    · left
      refine ⟨fun h ↦ hpos h.2.1, ?_⟩
      have hz : d = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
      have hc : UInt256.gt (d + UInt256.lnot ⟨0⟩) d = ⟨1⟩ := by
        rw [hz]
        decide +kernel
      have rd3 := midnightBlocks.midnight_block_24134_taken (by
        simp only [List.length_cons]; omega) (by rw [hc]; decide) (by jump_dest) rd2
      exact midnightBlocks.midnight_block_7302 (by
        simp only [midnightBlocks.midnight_block_24134_taken_stack, List.length_cons]; omega) rd3
  · exact Or.inl ⟨(fun h ↦ hmul h.1), midnightCheckedMulRevert
      (by simp only [List.length_cons]; omega) (by omega) rd1⟩

end Benchmarks.Midnight
