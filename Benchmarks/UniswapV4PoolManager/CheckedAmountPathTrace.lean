import Benchmarks.UniswapV4PoolManager.CheckedAmountTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem checkedAmountPathTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw w ret : UInt256} {σ : AccountMap} {R : List UInt256}
    {fits : Prop} [Decidable fits]
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (negate : Bool)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hcalc : if fits then ∃ k C, RD (deployedRuntime v) I g s0
      (if negate then ⟨17691⟩ else ⟨17653⟩) (w :: ret :: R) mem aw rdata σ k C
      else RDrev (deployedRuntime v) g s0) :
    if fits ∧ w.toNat < 2^255 then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (checkedAmountReturnWord w negate :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hfit : fits
  · rw [if_pos hfit] at hcalc
    obtain ⟨k1, C1, rd1⟩ := hcalc
    have hcheck := checkedAmountReturnTrace v hstack negate hret rd1
    by_cases hc : w.toNat < 2^255
    · rw [if_pos hc] at hcheck
      rw [if_pos ⟨hfit, hc⟩]
      exact hcheck
    · rw [if_neg hc] at hcheck
      rw [if_neg (fun hh => hc hh.2)]
      exact hcheck
  · rw [if_neg hfit] at hcalc
    rw [if_neg (fun hh => hfit hh.1)]
    exact hcalc

end Benchmarks.UniswapV4PoolManager
