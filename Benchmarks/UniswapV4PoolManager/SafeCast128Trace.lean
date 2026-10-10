import Benchmarks.UniswapV4PoolManager.SafeCast128Source
import Benchmarks.UniswapV4PoolManager.Signextend128Range
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_039
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem signedToInt128CostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {n : Int} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (hn : int256Fits n)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14213⟩ (EVM.wordOfInt n :: ret :: R) mem aw rdata σ k C) :
    if signedFits ⟨128, by decide⟩ n then ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret
      (EVM.wordOfInt n :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hfit : signedFits ⟨128, by decide⟩ n
  · rw [if_pos hfit]
    have hs := (signextend128_fixed_iff hn).mpr hfit
    have rd1 := poolManagerBlocks.poolManager_block_14213_fallthrough hstack
      (u256_sub_eq_zero_iff_eq.mpr hs) h
    have rd2 := poolManagerBlocks.poolManager_block_14226 (by simp only [List.length_cons]; omega) hret rd1
    simp only [poolManagerBlocks.poolManager_block_14226_stack] at rd2
    rw [hs] at rd2
    exact ⟨_, _, by omega, rd2⟩
  · rw [if_neg hfit]
    have hs : UInt256.sub (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt n)) (EVM.wordOfInt n) ≠ ⟨0⟩ :=
      fun he => hfit ((signextend128_fixed_iff hn).mp (u256_sub_eq_zero_iff_eq.mp he))
    have rd1 := poolManagerBlocks.poolManager_block_14213_taken hstack hs
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_12488 (by change R.length+4 ≤ 1024; exact hstack) rd1

theorem signedToInt128Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {n : Int} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (hn : int256Fits n)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14213⟩ (EVM.wordOfInt n :: ret :: R) mem aw rdata σ k C) :
    if signedFits ⟨128, by decide⟩ n then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (EVM.wordOfInt n :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hr := signedToInt128CostTrace v hstack hn hret h
  by_cases hf : signedFits ⟨128, by decide⟩ n
  · rw [if_pos hf] at hr ⊢
    obtain ⟨k', C', _, rd⟩ := hr
    exact ⟨k', C', rd⟩
  · rw [if_neg hf] at hr ⊢
    exact hr

end Benchmarks.UniswapV4PoolManager
