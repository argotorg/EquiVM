import Benchmarks.UniswapV4PoolManager.TickClampMemory
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_055
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickClampUpperTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw step tick : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (hc : int24Canonical tick) (htick : memLoad (step+UInt256.ofNat 32) mem = tick)
    (h : RD (deployedRuntime v) I g s0 ⟨19423⟩ (step :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19442⟩ (step :: R)
      (if EVM.signed tick ≥ 887272 then writeWord mem (step+UInt256.ofNat 32).toNat tickMaxWord else mem)
      (M aw (step+UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' := by
  have hclean : UInt256.signextend (UInt256.ofNat 2) tick = tick := (signextend24_eq_iff _).mpr hc
  have hg : UInt256.slt (UInt256.signextend (UInt256.ofNat 2) (memLoad (step+UInt256.ofNat 32) mem))
      (UInt256.ofNat 887272) = UInt256.fromBool (decide (EVM.signed tick < 887272)) := by
    rw [htick, hclean, slt_signed]
    change UInt256.fromBool (decide (EVM.signed tick < EVM.signed tickMaxWord)) = _
    rw [tickMaxWord_signed]
  apply RD_retainCost ?_ h
  intro budget start rd
  by_cases hh : EVM.signed tick ≥ 887272
  · rw [if_pos hh]
    have rd1 := poolManagerBlocks.poolManager_block_19423_taken hstack
      (by rw [hg, decide_eq_false (by omega)]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    have rd2 := poolManagerBlocks.poolManager_block_21034 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_21034_memory, memoryWords_idem] at rd2
    exact ⟨_, _, rd2⟩
  · rw [if_neg hh]
    have rd1 := poolManagerBlocks.poolManager_block_19423_fallthrough hstack
      (by rw [hg, decide_eq_true (by omega)]; rfl) rd
    exact ⟨_, _, rd1⟩

end Benchmarks.UniswapV4PoolManager
