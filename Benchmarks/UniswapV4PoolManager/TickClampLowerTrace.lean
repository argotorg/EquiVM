import Benchmarks.UniswapV4PoolManager.TickClampMemory
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_054
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_055
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickClampLowerTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw step tick : UInt256} {initialized : Bool}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨19401⟩
      ([initialized.toUInt256, tick, tickMinWord, step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19423⟩
      ([step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64] ++ R)
      (tickClampLowerMemory mem step tick initialized)
      (M (M aw (step+UInt256.ofNat 64) ⟨32⟩) (step+UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' := by
  have hb : UInt256.isZero (UInt256.isZero initialized.toUInt256) = initialized.toUInt256 := by
    cases initialized <;> rfl
  have hg : UInt256.sgt (UInt256.signextend (UInt256.ofNat 2) tick) tickMinWord =
      UInt256.fromBool (decide (-887272 < EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick))) := by
    rw [sgt_signed, tickMinWord_signed]
  apply RD_retainCost ?_ h
  intro budget start rd
  by_cases hl : EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick) ≤ -887272
  · have rd1 := poolManagerBlocks.poolManager_block_19401_taken hstack
      (by rw [hg, decide_eq_false (by omega)]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [poolManagerBlocks.poolManager_block_19401_taken_stack,
      poolManagerBlocks.poolManager_block_19401_taken_memory, hb] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_21048
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    rw [tickClampLowerMemory, if_pos hl]
    simp only [poolManagerBlocks.poolManager_block_21048_memory, memoryWords_idem] at rd2
    exact ⟨_, _, rd2⟩
  · have rd1 := poolManagerBlocks.poolManager_block_19401_fallthrough hstack
      (by rw [hg, decide_eq_true (by omega)]; rfl) rd
    simp only [poolManagerBlocks.poolManager_block_19401_fallthrough_stack,
      poolManagerBlocks.poolManager_block_19401_fallthrough_memory, hb] at rd1
    rw [tickClampLowerMemory, if_neg hl]
    exact ⟨_, _, rd1⟩

end Benchmarks.UniswapV4PoolManager
