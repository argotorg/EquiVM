import Benchmarks.CompoundIII.Comet.InternalMemoryOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalMemoryRun to a routine that may allocate memory and make external calls.
def internalDynamicRun (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (ret : UInt256) (R : List UInt256) : InternalOutcome → Prop
  | .ok evm => ∃ σ mem aw rdata k C, SourceState s0 ee σ evm ∧
      RD code ee g s0 ret R mem aw rdata σ k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

theorem internalMemoryRun.dynamic {code ee g s0 mem rdata ret R result}
    (h : internalMemoryRun code ee g s0 mem rdata ret R result) :
    internalDynamicRun code ee g s0 ret R result := by
  cases result with
  | ok evm =>
    obtain ⟨σ, aw, k, C, hs, hr⟩ := h
    exact ⟨σ, mem, aw, rdata, k, C, hs, hr⟩
  | reverted => exact h
  | staticViolation => exact h

end Benchmarks.CompoundIII.Comet
