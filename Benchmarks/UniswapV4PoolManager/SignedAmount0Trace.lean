import Benchmarks.UniswapV4PoolManager.SignedAmount0Words
import Benchmarks.UniswapV4PoolManager.SignedAmount0PathTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem signedAmount0Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {delta : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17703⟩ (a :: b :: EVM.wordOfInt delta :: ret :: R) mem aw rdata σ k C) :
    if signedAmount0Fits a b delta then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (signedAmount0Word a b delta :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hcmp := liquidityNegativeCmp hdlo hdhi
  by_cases hz : delta < 0
  · have rd1 := poolManagerBlocks.poolManager_block_17703_fallthrough
      (by change R.length+7 ≤ 1024; omega)
      (by rw [hcmp, decide_eq_true hz]; rfl) h
    have rd2 := poolManagerBlocks.poolManager_block_17717
      (by change R.length+6 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_17717_stack] at rd2
    rw [liquidityMagnitude_negative hdlo hdhi hz] at rd2
    have hc := signedAmount0PathTrace v hstack false ha hb (liquidityMagnitude_bound hdlo hdhi) hret rd2
    simpa only [signedAmount0Fits, signedAmount0Word, signedAmount0Unsigned, signedAmount0Round, signedAmountRound, if_pos hz] using hc
  · have rd1 := poolManagerBlocks.poolManager_block_17703_taken
      (by change R.length+7 ≤ 1024; omega)
      (by rw [hcmp, decide_eq_false hz]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_17746
      (by change R.length+6 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_17746_stack] at rd2
    rw [liquidityMagnitude_positive hdlo hdhi hz] at rd2
    have hc := signedAmount0PathTrace v hstack true ha hb (liquidityMagnitude_bound hdlo hdhi) hret rd2
    simpa only [signedAmount0Fits, signedAmount0Word, signedAmount0Unsigned, signedAmount0Round, signedAmountRound, if_neg hz] using hc

end Benchmarks.UniswapV4PoolManager
