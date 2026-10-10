import Benchmarks.UniswapV4PoolManager.SafeCast256Source
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_050
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem uintToInt256_guard (w : UInt256) :
    UInt256.slt w ⟨0⟩ = UInt256.fromBool (decide (¬w.toNat < 2^255)) := by
  rw [slt_signed]
  change UInt256.fromBool (decide (EVM.signed w < 0)) = _
  simp only [signedNegative_iff]

theorem uintToInt256Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw w ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17653⟩ (w :: ret :: R) mem aw rdata σ k C) :
    if w.toNat < 2^255 then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (w :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hfit : w.toNat < 2^255
  · rw [if_pos hfit]
    have rd1 := poolManagerBlocks.poolManager_block_17653_fallthrough
      (by change R.length+4 ≤ 1024; exact hstack)
      (by rw [uintToInt256_guard, decide_eq_false (not_not_intro hfit)]; rfl) h
    exact ⟨_, _, poolManagerBlocks.poolManager_block_17661 (by omega) hret rd1⟩
  · rw [if_neg hfit]
    have rd1 := poolManagerBlocks.poolManager_block_17653_taken
      (by change R.length+4 ≤ 1024; exact hstack)
      (by rw [uintToInt256_guard, decide_eq_true hfit]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_12488 (by change R.length+4 ≤ 1024; omega) rd1

theorem uintToInt256CheckTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw w : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+3 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨17691⟩ (w :: R) mem aw rdata σ k C) :
    if w.toNat < 2^255 then ∃ k' C', RD (deployedRuntime v) I g s0 ⟨17699⟩
      (w :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hfit : w.toNat < 2^255
  · rw [if_pos hfit]
    exact ⟨_, _, poolManagerBlocks.poolManager_block_17691_fallthrough hstack
      (by rw [uintToInt256_guard, decide_eq_false (not_not_intro hfit)]; rfl) h⟩
  · rw [if_neg hfit]
    have rd1 := poolManagerBlocks.poolManager_block_17691_taken hstack
      (by rw [uintToInt256_guard, decide_eq_true hfit]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_12488 (by change R.length+3 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
