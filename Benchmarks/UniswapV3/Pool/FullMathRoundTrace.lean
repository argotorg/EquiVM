import Benchmarks.UniswapV3.Pool.FullMathTrace
import Benchmarks.UniswapV3.Pool.FullMathRoundSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_053
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem fullMathRoundX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret a b d : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨16809⟩ (d :: b :: a :: ret :: R)
      mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 21 ≤ 1024) :
    (¬ fullMathRoundValid a b d ∧ RDrev (deployedRuntime v) g s0) ∨
    (fullMathRoundValid a b d ∧ ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (fullMathRoundResult a b d :: R) mem aw rdata σ k' C') := by
  have r0 := uniswapV3Pool_block_16809 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  rcases fullMathX (v := v) r0
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    with ⟨hbad, rbad⟩ | ⟨hbase, k1, C1, hC1, r1⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, rbad⟩
  · have hd := fullMath_denominator_pos hbase
    have hdword : d ≠ UInt256.ofNat 0 := by
      intro h
      have hh := congrArg UInt256.toNat h
      change d.toNat = 0 at hh
      omega
    have r2 := uniswapV3Pool_block_16822_taken (immWords := wordsOf (immStore v)) (by evm_ov)
      hdword (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have r2' : RD (deployedRuntime v) ee g s0 ⟨16834⟩
        (d :: ⟨0⟩ :: fullMathResult a b d :: d :: b :: a :: ret :: R)
        mem aw rdata σ (k1 + 8) (C1 + 28) := r2
    have hrem : (UInt256.mulMod a b d).toNat = fullMathProduct a b % d.toNat :=
      mulMod_toNat a b d hd
    by_cases hr : 0 < fullMathProduct a b % d.toNat
    · have r3 := uniswapV3Pool_block_16834_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_one (a := UInt256.mulMod a b d) (b := ⟨0⟩)
          (by rw [hrem]; exact hr)]; rfl) r2'
      by_cases hcap : (fullMathResult a b d).toNat < UInt256.size - 1
      · have hv : fullMathRoundValid a b d := ⟨hbase, fun _ ↦ hcap⟩
        have r4 := uniswapV3Pool_block_16844_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [ult_one (by exact hcap)]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
        have r5 := uniswapV3Pool_block_16857 (immWords := wordsOf (immStore v))
          (by evm_ov) hret r4
        refine Or.inr ⟨hv, k1 + 8 + 8 + 6 + 9, C1 + 28 + 34 + 25 + 27, by omega, ?_⟩
        simpa only [uniswapV3Pool_block_16857_stack, fullMathRoundResult, if_pos hr,
          u256_add_comm (UInt256.ofNat 1)] using r5
      · have hv : ¬ fullMathRoundValid a b d := fun h ↦ hcap (h.2 hr)
        have r4 := uniswapV3Pool_block_16844_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [ult_zero (by exact Nat.le_of_not_gt hcap)]; rfl) r3
        exact Or.inl ⟨hv,
          uniswapV3Pool_block_16853 (immWords := wordsOf (immStore v)) (by evm_ov) r4⟩
    · have hv : fullMathRoundValid a b d := ⟨hbase, fun h ↦ False.elim (hr h)⟩
      have r3 := uniswapV3Pool_block_16834_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_zero (a := UInt256.mulMod a b d) (b := ⟨0⟩)
          (by rw [hrem]; exact Nat.le_of_not_gt hr)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2'
      have r4 := uniswapV3Pool_block_13186 (immWords := wordsOf (immStore v))
        (by evm_ov) hret r3
      refine Or.inr ⟨hv, k1 + 8 + 8 + 7, C1 + 28 + 34 + 21, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_13186_stack, fullMathRoundResult, if_neg hr] using r4

end Benchmarks.UniswapV3.Pool
