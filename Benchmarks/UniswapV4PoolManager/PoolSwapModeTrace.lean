import Benchmarks.UniswapV4PoolManager.PoolSwapModeSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_063

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapModeAW (aw fee params : UInt256) : UInt256 :=
  if 1000000 ≤ fee.toNat then M aw params ⟨32⟩ else aw

theorem poolSwapModeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw fee params specified x1 x2 x4 x5 x6 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+11 ≤ 1024)
    (hf : fee.toNat < 2^24) (hm : memLoad params mem = specified)
    (h : RD (deployedRuntime v) I g s0 ⟨18951⟩
      (fee :: x1 :: x2 :: params :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C) :
    if poolSwapModeValid fee specified then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨18970⟩
        (x6 :: fee :: x1 :: x2 :: params :: x4 :: x5 :: fee :: R)
        mem (poolSwapModeAW aw fee params) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hclean : UInt256.land fee (UInt256.ofNat 16777215) = fee :=
    u256LandMaskCleanOfToNat _ _ rfl hf
  by_cases hg : 1000000 ≤ fee.toNat
  · have hlt : UInt256.lt fee (UInt256.ofNat 1000000) = ⟨0⟩ := ult_zero hg
    have rd1 := poolManagerBlocks.poolManager_block_18951_taken hstack
      (by rw [hclean, hlt]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_18951_taken_stack] at rd1
    by_cases hs : UInt256.sgt specified ⟨0⟩ = ⟨0⟩
    · have hv : poolSwapModeValid fee specified := by
        intro hh
        have hh' : EVM.signed specified ≤ 0 := sgt_zero_eq_zero_to_nonpos specified hs
        omega
      rw [if_pos hv, poolSwapModeAW, if_pos hg]
      have rd2 := poolManagerBlocks.poolManager_block_22170_taken
        (by change R.length+3+7 ≤ 1024; omega) (by rw [hm, hs]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact ⟨_, _, by omega, rd2⟩
    · have hv : ¬poolSwapModeValid fee specified := by
        intro hh
        exact hh ⟨hg, sgt_zero_ne_zero_to_pos specified hs⟩
      rw [if_neg hv]
      have rd2 := poolManagerBlocks.poolManager_block_22170_fallthrough
        (by change R.length+3+7 ≤ 1024; omega) (by rw [hm, isZero_eq_zero_of_ne hs]; rfl) rd1
      exact poolManagerBlocks.poolManager_block_22180 (by change R.length+8+2 ≤ 1024; omega) rd2
  · have hv : poolSwapModeValid fee specified := fun hh => hg hh.1
    rw [if_pos hv, poolSwapModeAW, if_neg hg]
    have hlt : UInt256.lt fee (UInt256.ofNat 1000000) = ⟨1⟩ := ult_one (Nat.lt_of_not_ge hg)
    have rd := poolManagerBlocks.poolManager_block_18951_fallthrough hstack (by rw [hclean, hlt]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_18951_fallthrough_stack] at rd
    exact ⟨_, _, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
