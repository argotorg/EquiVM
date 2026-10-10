import Benchmarks.UniswapV4PoolManager.SafeCast128Trace
import Benchmarks.UniswapV4PoolManager.SignedWordBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem signedWordToInt128CostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret word : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14213⟩ (word :: ret :: R) mem aw rdata σ k C) :
    if signedFits ⟨128, by decide⟩ (EVM.signed word) then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret (word :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hc := signedToInt128CostTrace (n := EVM.signed word) v hstack (signedWord_fits word) hret
    (by rw [wordOfInt_signed]; exact h)
  simpa only [wordOfInt_signed] using hc

end Benchmarks.UniswapV4PoolManager
