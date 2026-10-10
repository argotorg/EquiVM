import Benchmarks.UniswapV4PoolManager.AfterSwapUpdateSource
import Benchmarks.UniswapV4PoolManager.SafeCast128WordTrace
import Benchmarks.UniswapV4PoolManager.Int128AddTrace
import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_019
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterSwapUpdateTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw delta ret : UInt256} {unspecified : Int} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hu : signedFits ⟨128, by decide⟩ unspecified)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨6381⟩
      (delta :: UInt256.ofNat 16136 :: EVM.wordOfInt unspecified :: ret :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (EVM.wordOfInt (unspecified+EVM.signed delta) :: R)
        mem aw rdata post.accountMap k' C') (fun _ _ => False)
      (afterSwapUpdateResult f evm unspecified delta) := by
  have rd1 := poolManager_block_6381 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hcast := signedWordToInt128CostTrace v (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  by_cases hc : signedFits ⟨128, by decide⟩ (EVM.signed delta)
  · rw [if_pos hc] at hcast
    rw [afterSwapUpdateResult, if_pos hc]
    obtain ⟨k1, C1, hcost1, rd2⟩ := hcast
    have rd3 := poolManager_block_16136 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [poolManager_block_16136_stack] at rd3
    have hsum := int128AddTrace (a := unspecified) (b := EVM.signed delta) (R := R) v (by omega) hu hc hret
      (by rw [wordOfInt_signed]; exact rd3)
    by_cases hs : signedFits ⟨128, by decide⟩ (unspecified+EVM.signed delta)
    · rw [if_pos hs]
      obtain ⟨k', C', hcost, rd⟩ := RD_retainCost (fun budget start hin => by
        have ht := int128AddTrace (a := unspecified) (b := EVM.signed delta) (R := R) v (by omega) hu hc hret
          (by rw [wordOfInt_signed]; exact hin)
        rw [if_pos hs] at ht
        exact ht) rd3
      exact ⟨rfl, k', C', by omega, rd⟩
    · rw [if_neg hs] at hsum ⊢
      exact hsum
  · rw [if_neg hc] at hcast
    rw [afterSwapUpdateResult, if_neg hc]
    exact hcast

end Benchmarks.UniswapV4PoolManager
