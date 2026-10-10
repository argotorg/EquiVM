import Benchmarks.UniswapV4PoolManager.NextAmount0Words
import Benchmarks.UniswapV4PoolManager.FullMathRoundTrace
import Benchmarks.UniswapV4PoolManager.SafeCast160Trace
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_059

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount0RoundTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw n price d ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (checked : Bool) (hstack : R.length+16 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23656⟩
      ([n, price, d, if checked then ⟨20528⟩ else ⟨23953⟩,
        if checked then ⟨13903⟩ else solcAddrMask, ret] ++ R) mem aw rdata σ k C) :
    if nextAmount0RoundFits n price d checked then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (nextAmount0RoundWord n price d checked :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hreturn : (D_J (deployedRuntime v) 0).contains (if checked then ⟨20528⟩ else ⟨23953⟩) = true := by
    cases checked <;> rw [deployedRuntime_jumps] <;> jump_dest
  by_cases hf : fullMathRoundFits n price d
  · obtain ⟨k1, C1, hC1, rd1⟩ := RD_retainCost (fun _ _ hin => by
      have hr := fullMathRoundTrace (a := n) (b := price) (d := d) v
        (by change R.length+16 ≤ 1024; exact hstack) hreturn hin
      rw [if_pos hf] at hr
      exact hr) h
    cases checked with
    | false =>
      simp only [nextAmount0RoundFits, hf, Bool.false_eq_true, if_false, and_self, if_true, nextAmount0RoundWord]
      have rd2 := poolManagerBlocks.poolManager_block_23953 (by change R.length+3 ≤ 1024; omega) hret rd1
      exact ⟨_, _, by omega, rd2⟩
    | true =>
      simp only [nextAmount0RoundFits, hf, if_true, true_and, nextAmount0RoundWord]
      have rd2 := poolManagerBlocks.poolManager_block_20528 (by change R.length+4 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hc := uintToUint160CostTrace v (by change R.length+5 ≤ 1024; omega)
        (by rw [deployedRuntime_jumps]; jump_dest) rd2
      by_cases h160 : (fullMathRoundWord n price d).toNat < 2^160
      · rw [if_pos h160] at hc ⊢
        obtain ⟨k3, C3, hC3, rd3⟩ := hc
        have rd4 := poolManagerBlocks.poolManager_block_13903 (by change R.length+2 ≤ 1024; omega) hret rd3
        exact ⟨_, _, by omega, rd4⟩
      · rw [if_neg h160] at hc ⊢
        exact hc
  · simp only [nextAmount0RoundFits, hf, false_and, if_false]
    have hr := fullMathRoundTrace (a := n) (b := price) (d := d) v
      (by change R.length+16 ≤ 1024; exact hstack) hreturn h
    rw [if_neg hf] at hr
    exact hr

end Benchmarks.UniswapV4PoolManager
