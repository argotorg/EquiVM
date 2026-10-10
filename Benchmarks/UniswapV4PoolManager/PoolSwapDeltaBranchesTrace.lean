import Benchmarks.UniswapV4PoolManager.PoolSwapDeltaWords
import Benchmarks.UniswapV4PoolManager.SafeCast128WordTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_062

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapDeltaCalculatedTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw specified remaining params calculated : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024)
    (hm : memLoad params mem = specified)
    (h : RD (deployedRuntime v) I g s0 ⟨21729⟩
      (specified :: remaining :: params :: calculated :: R) mem aw rdata σ k C) :
    if poolSwapDeltaFits true specified remaining calculated then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨21750⟩
        (UInt256.sub specified remaining :: calculated :: R) mem (M aw params ⟨32⟩) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := poolManagerBlocks.poolManager_block_21729 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_21729_stack] at rd1
  have hc1 := signedWordToInt128CostTrace v (by change R.length+3+4 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  by_cases ha : signedFits ⟨128, by decide⟩ (EVM.signed calculated)
  · rw [if_pos ha] at hc1
    obtain ⟨k2, C2, hC2, rd2⟩ := hc1
    have rd3 := poolManagerBlocks.poolManager_block_21742 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [poolManagerBlocks.poolManager_block_21742_stack, hm] at rd3
    have hc2 := signedWordToInt128CostTrace v (by change R.length+1+4 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd3
    by_cases hb : signedFits ⟨128, by decide⟩ (EVM.signed (UInt256.sub specified remaining))
    · rw [if_pos hb] at hc2
      rw [if_pos (show poolSwapDeltaFits true specified remaining calculated from ⟨ha, hb⟩)]
      obtain ⟨k4, C4, hC4, rd4⟩ := hc2
      exact ⟨k4, C4, by omega, rd4⟩
    · rw [if_neg hb] at hc2
      rw [if_neg (show ¬poolSwapDeltaFits true specified remaining calculated from fun hh => hb hh.2)]
      exact hc2
  · rw [if_neg ha] at hc1
    rw [if_neg (show ¬poolSwapDeltaFits true specified remaining calculated from fun hh => ha hh.1)]
    exact hc1

theorem poolSwapDeltaSpecifiedTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw specified remaining params calculated : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨21776⟩
      (specified :: remaining :: params :: calculated :: R) mem aw rdata σ k C) :
    if poolSwapDeltaFits false specified remaining calculated then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨21750⟩
        (calculated :: UInt256.sub specified remaining :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := poolManagerBlocks.poolManager_block_21776 (by change R.length+1+4 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_21776_stack] at rd1
  have hc1 := signedWordToInt128CostTrace v (by change R.length+2+4 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  by_cases ha : signedFits ⟨128, by decide⟩ (EVM.signed (UInt256.sub specified remaining))
  · rw [if_pos ha] at hc1
    obtain ⟨k2, C2, hC2, rd2⟩ := hc1
    have rd3 := poolManagerBlocks.poolManager_block_21792 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [poolManagerBlocks.poolManager_block_21792_stack] at rd3
    have hc2 := signedWordToInt128CostTrace v (by change R.length+1+4 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd3
    by_cases hb : signedFits ⟨128, by decide⟩ (EVM.signed calculated)
    · rw [if_pos hb] at hc2
      rw [if_pos (show poolSwapDeltaFits false specified remaining calculated from ⟨ha, hb⟩)]
      obtain ⟨k4, C4, hC4, rd4⟩ := hc2
      exact ⟨k4, C4, by omega, rd4⟩
    · rw [if_neg hb] at hc2
      rw [if_neg (show ¬poolSwapDeltaFits false specified remaining calculated from fun hh => hb hh.2)]
      exact hc2
  · rw [if_neg ha] at hc1
    rw [if_neg (show ¬poolSwapDeltaFits false specified remaining calculated from fun hh => ha hh.1)]
    exact hc1

end Benchmarks.UniswapV4PoolManager
