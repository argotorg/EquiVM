import Benchmarks.UniswapV4PoolManager.TickSqrtConditionalTrace
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.SignedArithmetic
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_048
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_049

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickSqrtFinalStage (absTick price : UInt256) : UInt256 :=
  tickSqrtStage absTick price (UInt256.ofNat 524288) (UInt256.ofNat 1404880482679654955896180642)

theorem tickSqrtFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret absTick tick price : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16976⟩
      (absTick :: tick :: price :: UInt256.ofNat 4294967295 :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (tickSqrtRound (if 0 < EVM.signed tick then
        UInt256.div (UInt256.ofNat (2^256-1)) (tickSqrtFinalStage absTick price)
        else tickSqrtFinalStage absTick price) :: R) mem aw rdata σ k' C' := by
  have hlast : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16986⟩
      (tick :: tickSqrtFinalStage absTick price :: UInt256.ofNat 4294967295 :: ret :: R)
      mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => tick :: p :: UInt256.ofNat 4294967295 :: ret :: R)
    · intro hz
      have rd := poolManagerBlocks.poolManager_block_16976_fallthrough
        (by simp only [List.length_cons]; omega)
        (by rw [u256_land_comm]; exact hz) h
      exact ⟨_, _, rd⟩
    · intro hn
      have rd1 := poolManagerBlocks.poolManager_block_16976_taken
        (by simp only [List.length_cons]; omega)
        (by rw [u256_land_comm]; exact hn)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      have rd2 := poolManagerBlocks.poolManager_block_17039 (by simp only [List.length_cons]; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact ⟨_, _, rd2⟩
  obtain ⟨k1, C1, rd1⟩ := hlast
  by_cases ht : 0 < EVM.signed tick
  · rw [if_pos ht]
    have rd2 := poolManagerBlocks.poolManager_block_16986_taken (by simp only [List.length_cons]; omega)
      (by rw [slt_signed]; change UInt256.fromBool (decide (0 < EVM.signed tick)) ≠ UInt256.ofNat 0
          rw [decide_eq_true ht]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have rd3 := poolManagerBlocks.poolManager_block_17000 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := poolManagerBlocks.poolManager_block_16993 (by omega) hret rd3
    exact ⟨_, _, rd4⟩
  · rw [if_neg ht]
    have rd2 := poolManagerBlocks.poolManager_block_16986_fallthrough (by simp only [List.length_cons]; omega)
      (by rw [slt_signed]; change UInt256.fromBool (decide (0 < EVM.signed tick)) = UInt256.ofNat 0
          rw [decide_eq_false ht]; rfl) rd1
    have rd3 := poolManagerBlocks.poolManager_block_16993 (by omega) hret rd2
    exact ⟨_, _, rd3⟩

end Benchmarks.UniswapV4PoolManager
