import Benchmarks.UniswapV4PoolManager.WordReadTraceLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def wordArrayTraceCursor (I : ExecutionEnv) (i : Nat) : UInt256 :=
  UInt256.ofNat (36 + (calldataWord I.calldata 4).toNat + 32*i)
abbrev wordArrayTraceStack (I : ExecutionEnv) := wordReadTraceStack (wordArrayTraceCursor I) (UInt256.ofNat 32)
abbrev wordArrayTraceExitStack (I : ExecutionEnv) := wordReadTraceExitStack (wordArrayTraceCursor I)

/-- Iterate a word-array read step while retaining the exact sequence of memory stores. -/
theorem wordArrayTraceLoop {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {σ : AccountMap} {R : List UInt256} {n : Nat}
    {values : Nat → UInt256} {loopPC : UInt256}
    (step : ∀ i mem aw k C, i ≤ n →
      RD code I g s0 loopPC (wordArrayTraceStack I n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD code I g s0 (if i+1 < n then loopPC else ⟨2508⟩)
        (if i+1 < n then wordArrayTraceStack I n (i+1) R else wordArrayTraceExitStack I n (i+1) R)
        (writeWord mem (224+32*i) (values i)) aw' rdata σ k' C')
    (remaining : Nat) :
    ∀ i mem aw k C, i + remaining + 1 = n →
      RD code I g s0 loopPC (wordArrayTraceStack I n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD code I g s0 ⟨2508⟩ (wordArrayTraceExitStack I n n R)
        (wordSequenceMemory mem (224+32*i) (wordArrayWords values i (remaining+1)))
        aw' rdata σ k' C' := by
  exact wordReadTraceLoop
    (fun i mem aw k C hi h => step i mem aw k C (by omega) h) remaining

end Benchmarks.UniswapV4PoolManager
