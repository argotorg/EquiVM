import Benchmarks.UniswapV4PoolManager.PoolSwapLimitSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_054
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_062
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_063

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapLimitAW (aw params : UInt256) : UInt256 :=
  M (M aw (params+UInt256.ofNat 96) ⟨32⟩) (params+UInt256.ofNat 96) ⟨32⟩

theorem poolSwapLimitBranchTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw packed limit ret params : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+8 ≤ 1024)
    (hl : limit.toNat < 2^160) (hm : memLoad (params+UInt256.ofNat 96) mem = limit)
    (h : RD (deployedRuntime v) I g s0 (if zeroForOne then ⟨18985⟩ else ⟨22052⟩)
      (slot0SqrtPriceWord packed :: ret :: params :: R) mem aw rdata σ k C) :
    if poolSwapLimitValid packed limit zeroForOne then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19061⟩ (ret :: params :: R)
        mem (poolSwapLimitAW aw params) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hclean : UInt256.land limit (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = limit :=
    solcAddrMask_clean hl
  have hclean' : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) limit = limit :=
    (u256_land_comm _ _).trans hclean
  cases zeroForOne
  · by_cases ha : (slot0SqrtPriceWord packed).toNat < limit.toNat
    · have hgt : UInt256.gt limit (slot0SqrtPriceWord packed) = ⟨1⟩ := ugt_one ha
      have rd1 := poolManagerBlocks.poolManager_block_22052_fallthrough (by omega)
        (by rw [hm, hclean, hgt]; rfl) h
      simp only [poolManagerBlocks.poolManager_block_22052_fallthrough_stack, hm, hclean] at rd1
      by_cases hb : limit.toNat < 1461446703485210103287273052203988822378723970342
      · rw [if_pos (show poolSwapLimitValid packed limit false from ⟨ha, hb⟩)]
        have hlt : UInt256.lt limit (UInt256.ofNat 1461446703485210103287273052203988822378723970342) = ⟨1⟩ := ult_one hb
        have rd2 := poolManagerBlocks.poolManager_block_22090_fallthrough
          (by change R.length+2+3 ≤ 1024; omega) (by rw [hm, hclean', hlt]; rfl) rd1
        simp only [poolManagerBlocks.poolManager_block_22090_fallthrough_stack] at rd2
        have rd3 := poolManagerBlocks.poolManager_block_22143
          (by change R.length+2+1 ≤ 1024; omega)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
        simp only [poolManagerBlocks.poolManager_block_22143_stack] at rd3
        exact ⟨_, _, by omega, rd3⟩
      · rw [if_neg (show ¬poolSwapLimitValid packed limit false from fun hh => hb hh.2)]
        have hlt : UInt256.lt limit (UInt256.ofNat 1461446703485210103287273052203988822378723970342) = ⟨0⟩ := ult_zero (Nat.le_of_not_gt hb)
        have rd2 := poolManagerBlocks.poolManager_block_22090_taken
          (by change R.length+2+3 ≤ 1024; omega) (by rw [hm, hclean', hlt]; decide)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
        simp only [poolManagerBlocks.poolManager_block_22090_taken_stack] at rd2
        exact poolManagerBlocks.poolManager_block_21954 (by change R.length+2+3 ≤ 1024; omega) rd2
    · rw [if_neg (show ¬poolSwapLimitValid packed limit false from fun hh => ha hh.1)]
      have hgt : UInt256.gt limit (slot0SqrtPriceWord packed) = ⟨0⟩ := ugt_zero (Nat.le_of_not_gt ha)
      have rd1 := poolManagerBlocks.poolManager_block_22052_taken (by omega)
        (by rw [hm, hclean, hgt]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      simp only [poolManagerBlocks.poolManager_block_22052_taken_stack] at rd1
      exact poolManagerBlocks.poolManager_block_21997 (by change R.length+2+6 ≤ 1024; omega) rd1
  · by_cases ha : limit.toNat < (slot0SqrtPriceWord packed).toNat
    · have hlt : UInt256.lt limit (slot0SqrtPriceWord packed) = ⟨1⟩ := ult_one ha
      have rd1 := poolManagerBlocks.poolManager_block_18985_fallthrough (by omega)
        (by rw [hm, hclean, hlt]; rfl) h
      simp only [poolManagerBlocks.poolManager_block_18985_fallthrough_stack, hm, hclean] at rd1
      by_cases hb : 4295128739 < limit.toNat
      · rw [if_pos (show poolSwapLimitValid packed limit true from ⟨ha, hb⟩)]
        have hgt : UInt256.gt limit (UInt256.ofNat 4295128739) = ⟨1⟩ := ugt_one hb
        have rd2 := poolManagerBlocks.poolManager_block_19022_fallthrough
          (by change R.length+2+3 ≤ 1024; omega) (by rw [hm, hclean', hgt]; rfl) rd1
        simp only [poolManagerBlocks.poolManager_block_19022_fallthrough_stack] at rd2
        have rd3 := poolManagerBlocks.poolManager_block_19060 (by change R.length+2+1 ≤ 1024; omega) rd2
        simp only [poolManagerBlocks.poolManager_block_19060_stack] at rd3
        exact ⟨_, _, by omega, rd3⟩
      · rw [if_neg (show ¬poolSwapLimitValid packed limit true from fun hh => hb hh.2)]
        have hgt : UInt256.gt limit (UInt256.ofNat 4295128739) = ⟨0⟩ := ugt_zero (Nat.le_of_not_gt hb)
        have rd2 := poolManagerBlocks.poolManager_block_19022_taken
          (by change R.length+2+3 ≤ 1024; omega) (by rw [hm, hclean', hgt]; decide)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
        simp only [poolManagerBlocks.poolManager_block_19022_taken_stack] at rd2
        exact poolManagerBlocks.poolManager_block_21954 (by change R.length+2+3 ≤ 1024; omega) rd2
    · rw [if_neg (show ¬poolSwapLimitValid packed limit true from fun hh => ha hh.1)]
      have hlt : UInt256.lt limit (slot0SqrtPriceWord packed) = ⟨0⟩ := ult_zero (Nat.le_of_not_gt ha)
      have rd1 := poolManagerBlocks.poolManager_block_18985_taken (by omega)
        (by rw [hm, hclean, hlt]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      simp only [poolManagerBlocks.poolManager_block_18985_taken_stack] at rd1
      exact poolManagerBlocks.poolManager_block_21997 (by change R.length+2+6 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
