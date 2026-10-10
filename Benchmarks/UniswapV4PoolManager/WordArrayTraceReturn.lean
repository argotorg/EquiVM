import Benchmarks.UniswapV4PoolManager.WordArrayTraceLoop
import Benchmarks.UniswapV4PoolManager.WordReadTraceReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

theorem wordArrayReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n i : Nat} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hn : n ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨2508⟩ (wordArrayTraceExitStack I n i R)
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (mem.readWithPadding 160 (64+32*n)) :=
  wordReadReturnTrace v hstack (by norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega) h

/-- Complete either word-array loop, including its mandatory read for an empty array. -/
theorem wordArrayTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n : Nat} {values : Nat → UInt256} {loopPC : UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 9 ≤ 1024) (hn : n ≤ solcMaxU64)
    (step : ∀ i mem aw k C, i ≤ n →
      RD (deployedRuntime v) I g s0 loopPC (wordArrayTraceStack I n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 (if i+1 < n then loopPC else ⟨2508⟩)
        (if i+1 < n then wordArrayTraceStack I n (i+1) R else wordArrayTraceExitStack I n (i+1) R)
        (writeWord mem (224+32*i) (values i)) aw' rdata σ k' C')
    (h : RD (deployedRuntime v) I g s0 loopPC (wordArrayTraceStack I n 0 R)
      (arrayHeaderMemory n) aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n)) :=
  wordReadTraceReturn v hstack (by norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega)
    (fun i mem aw k C hi h => step i mem aw k C (by omega) h) h

end Benchmarks.UniswapV4PoolManager
