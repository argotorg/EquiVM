import Benchmarks.CompoundIII.Comet.InternalOutcome

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalRun to routines with a specified output memory and changing active words.
def internalMemoryRun (fork : Ethereum.Fork) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem rdata : ByteArray) (ret : UInt256) (R : List UInt256) : InternalOutcome → Prop
  | .ok evm => ∃ σ aw k C, SourceState s0 ee σ evm ∧
      RD fork code ee g s0 ret R mem aw rdata σ k C
  | .reverted => RDrev fork code g s0
  | .staticViolation => RDstatic fork code g s0

end Benchmarks.CompoundIII.Comet
