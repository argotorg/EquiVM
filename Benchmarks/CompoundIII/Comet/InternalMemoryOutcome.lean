import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalRun to routines with a specified output memory and changing active words.
def internalMemoryRun (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem rdata : ByteArray) (ret : UInt256) (R : List UInt256) : InternalOutcome → Prop
  | .ok evm => ∃ σ aw k C, SourceState s0 ee σ evm ∧
      RD code ee g s0 ret R mem aw rdata σ k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

end Benchmarks.CompoundIII.Comet
