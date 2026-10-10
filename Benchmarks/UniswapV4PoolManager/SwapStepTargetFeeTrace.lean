import Benchmarks.UniswapV4PoolManager.SwapStepFeeTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepTargetFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw available target price j dir amount fee liquidity : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨19643⟩
      ([available, target, swapStepFeeComplement fee, price, j, dir, amount, fee, liquidity] ++ R)
      mem aw rdata σ k C) :
    (swapStepTargetFeeFits amount fee → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19697⟩
        ([dir, target, liquidity, price, j, ⟨160⟩, swapStepTargetFeeWord amount fee,
          amount, target, solcAddrMask] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepTargetFeeFits amount fee → RDrev (deployedRuntime v) g s0) := by
  have hclean := u256LandMaskCleanOfToNat fee (UInt256.ofNat 16777215) rfl hf
  by_cases heq : fee = fullMathPPM
  · have hg : UInt256.eq (⟨0⟩ : UInt256)
        (UInt256.eq (UInt256.land fee (UInt256.ofNat 16777215)) (UInt256.ofNat 1000000)) = ⟨0⟩ := by
      rw [hclean, heq]
      decide +kernel
    have rd1 := poolManagerBlocks.poolManager_block_19643_fallthrough
      (by change R.length+14 ≤ 1024; omega) hg h
    simp only [poolManagerBlocks.poolManager_block_19643_fallthrough_stack] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_19692
      (by change R.length+11 ≤ 1024; omega) rd1
    simp only [poolManagerBlocks.poolManager_block_19692_stack] at rd2
    have rd3 := poolManagerBlocks.poolManager_block_19695
      (by change R.length+10 ≤ 1024; omega) rd2
    simp only [poolManagerBlocks.poolManager_block_19695_stack] at rd3
    constructor
    · intro _
      refine ⟨k+20+3+2, C+65+7+4, by omega, ?_⟩
      simpa only [swapStepTargetFeeWord, if_pos heq] using rd3
    · intro hfit
      exact False.elim (hfit (Or.inl heq))
  · have hg : UInt256.eq (⟨0⟩ : UInt256)
        (UInt256.eq (UInt256.land fee (UInt256.ofNat 16777215)) (UInt256.ofNat 1000000)) ≠ ⟨0⟩ := by
      rw [hclean]
      have hneq : UInt256.eq fee (UInt256.ofNat 1000000) = ⟨0⟩ := by
        apply uInt256_eq_zero_of_ne
        intro he
        exact heq (uInt256_eq_one_eq he)
      rw [hneq, uInt256_eq_self]
      decide +kernel
    have rd1 := poolManagerBlocks.poolManager_block_19643_taken
      (by change R.length+14 ≤ 1024; omega) hg
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_19643_taken_stack] at rd1
    have hr := swapStepInputFeeTrace v (by change R.length+23 ≤ 1024; exact hstack) hf rd1
    constructor
    · intro hfit
      obtain ⟨k2, C2, hC2, rd2⟩ := hr.1 (hfit.resolve_left heq)
      have rd3 := poolManagerBlocks.poolManager_block_19695
        (by change R.length+10 ≤ 1024; omega) rd2
      simp only [poolManagerBlocks.poolManager_block_19695_stack] at rd3
      refine ⟨k2+2, C2+4, by omega, ?_⟩
      simpa only [swapStepTargetFeeWord, if_neg heq] using rd3
    · intro hfit
      exact hr.2 (fun hf => hfit (Or.inr hf))

end Benchmarks.UniswapV4PoolManager
