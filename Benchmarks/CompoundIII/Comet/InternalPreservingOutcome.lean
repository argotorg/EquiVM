import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalDynamicRun with preservation of the free pointer and allocated memory size.
def internalPreservingRun (fork : Ethereum.Fork) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (before : ByteArray) (free : UInt256) (rdata : ByteArray) (ret : UInt256) (R : List UInt256) :
    InternalOutcome → Prop
  | .ok evm => ∃ mem σ aw k C, SourceState s0 ee σ evm ∧
      RD fork code ee g s0 ret R mem aw rdata σ k C ∧
      memLoad ⟨64⟩ mem = free ∧ before.size ≤ mem.size
  | .reverted => RDrev fork code g s0
  | .staticViolation => RDstatic fork code g s0

theorem internalPreservingRun.of_size_eq {code ee g s0 before before' free rdata ret R result}
    (hr : internalPreservingRun fork code ee g s0 before free rdata ret R result)
    (hs : before'.size = before.size) :
    internalPreservingRun fork code ee g s0 before' free rdata ret R result := by
  cases result <;> simpa only [internalPreservingRun, hs] using hr

end Benchmarks.CompoundIII.Comet
