import Benchmarks.Midnight.MulDivGas

/-! The compiler's specialized rounded-up multiplication with a fixed 10^18 denominator. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takePriceScale : UInt256 := UInt256.ofNat 1000000000000000000

theorem midnightWmulUp {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x y ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨24082⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    (¬ MulDivUpSafe x y takePriceScale ∧ RDrev midnightBytecode g s0) ∨
    (MulDivUpSafe x y takePriceScale ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ret (mulDivUp x y takePriceScale :: R)
        mem aw rdata σ k' C') := by
  have hp : UInt256.sub takePriceScale ⟨1⟩ = UInt256.ofNat 999999999999999999 := by
    decide +kernel
  have rd1 := midnightBlocks.midnight_block_24082
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_24082_stack] at rd1
  by_cases hmul : x.toNat * y.toNat < UInt256.size
  · obtain ⟨k2, C2, hC2, rd2⟩ := midnightCheckedMul_mono
      (by simp only [List.length_cons]; omega) hmul (by jump_dest) rd1
    by_cases hadd : (UInt256.mul x y).toNat + 999999999999999999 < UInt256.size
    · have hn : (UInt256.mul x y + UInt256.ofNat 999999999999999999).toNat =
          (UInt256.mul x y).toNat + 999999999999999999 := addWord_toNat _ _ hadd
      have rd3 := midnightBlocks.midnight_block_24092_fallthrough
        (by simp only [List.length_cons]; omega) (ugt_zero (by rw [hn]; omega)) rd2
      simp only [midnightBlocks.midnight_block_24092_fallthrough_stack] at rd3
      have rd4 := midnightBlocks.midnight_block_24111 (by omega) hret rd3
      refine Or.inr ⟨⟨hmul, by decide, by rw [hp]; exact hadd⟩,
        k2 + 9 + 5, C2 + 32 + 22, by omega, ?_⟩
      simpa only [midnightBlocks.midnight_block_24111_stack, mulDivUp, hp, takePriceScale] using rd4
    · have hc : UInt256.gt (UInt256.mul x y)
          (UInt256.mul x y + UInt256.ofNat 999999999999999999) = ⟨1⟩ := by
        rw [u256_add_comm]
        exact u256_gt_add_right_of_overflow _ _ (by
          change UInt256.size ≤ (UInt256.mul x y).toNat + 999999999999999999
          omega)
      have rr := midnightBlocks.midnight_block_24092_taken
        (by simp only [List.length_cons]; omega) (by rw [hc]; decide) (by jump_dest) rd2
      exact Or.inl ⟨fun h ↦ hadd (by simpa only [hp] using h.2.2),
        midnightBlocks.midnight_block_7302 (by
          simp only [midnightBlocks.midnight_block_24092_taken_stack, List.length_cons]
          omega) rr⟩
  · exact Or.inl ⟨fun h ↦ hmul h.1, midnightCheckedMulRevert
      (by simp only [List.length_cons]; omega) (by omega) rd1⟩

end Benchmarks.Midnight
