import Benchmarks.UniswapV4PoolManager.CheckedAmountSource
import Benchmarks.UniswapV4PoolManager.SafeCast256Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem checkedAmountReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw w ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (negate : Bool)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 (if negate then ⟨17691⟩ else ⟨17653⟩)
      (w :: ret :: R) mem aw rdata σ k C) :
    if w.toNat < 2^255 then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (checkedAmountReturnWord w negate :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases negate with
  | false => exact uintToInt256Trace v hstack hret h
  | true =>
    have hc := uintToInt256CheckTrace v (by change R.length+4 ≤ 1024; exact hstack) h
    by_cases hfit : w.toNat < 2^255
    · rw [if_pos hfit] at hc ⊢
      obtain ⟨k1, C1, rd1⟩ := hc
      exact ⟨_, _, poolManagerBlocks.poolManager_block_17699 (by omega) hret rd1⟩
    · rw [if_neg hfit] at hc ⊢
      exact hc

end Benchmarks.UniswapV4PoolManager
