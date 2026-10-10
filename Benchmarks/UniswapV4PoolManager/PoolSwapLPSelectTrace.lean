import Benchmarks.UniswapV4PoolManager.PoolSwapLPSelectSource
import Benchmarks.UniswapV4PoolManager.LPFeeOverrideTrace
import Benchmarks.UniswapV4PoolManager.ProtocolSwapFeeTrace
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapLPSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw override packed x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (if lpFeeIsOverride override then ⟨18928⟩ else ⟨22246⟩)
      ([override, x1, x2, x3, x4, x5, x6, x7, x8, x9, packed]++R) mem aw rdata σ k C) :
    if poolSwapLPFeeValid override then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨18941⟩
        ([poolSwapLPFeeWord packed override, x1, x2, x3, x4, x5, x6, x7, x8, x9, packed]++R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases he : lpFeeIsOverride override
  · have hv : poolSwapLPFeeValid override := by
      simp only [poolSwapLPFeeValid, he, Bool.false_eq_true, false_implies]
    rw [if_pos hv, poolSwapLPFeeWord, he]
    simp only [he, Bool.false_eq_true, if_false] at h
    exact ⟨_, _, by omega, slot0GetLPFeeTrace v (by change R.length+12 ≤ 1024; omega) h⟩
  · simp only [he, if_true] at h
    by_cases hb : (lpFeeRemoveOverride override).toNat ≤ 1000000
    · rw [if_pos (show poolSwapLPFeeValid override from fun _ => hb), poolSwapLPFeeWord, he]
      apply RD_retainCost (h := h)
      intro budget start hin
      have ht := lpFeeOverrideValidateTrace v (by change R.length+10+5 ≤ 1024; omega) hin
      rw [if_pos hb] at ht
      exact ht
    · rw [if_neg (show ¬poolSwapLPFeeValid override from fun hh => hb (hh he))]
      have ht := lpFeeOverrideValidateTrace v (by change R.length+10+5 ≤ 1024; omega) h
      rwa [if_neg hb] at ht

end Benchmarks.UniswapV4PoolManager
