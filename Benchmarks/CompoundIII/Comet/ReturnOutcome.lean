import Benchmarks.CompoundIII.Comet.InternalOutcome

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES voidOutcomeRun to an explicit ABI return value.
def returnOutcomeRun (fork : Ethereum.Fork) (code : ByteArray) (g : Sat256) (s0 : State) (data : ByteArray) :
    InternalOutcome → Prop
  | .ok evm => RDret fork code g s0 evm.accountMap data
  | .reverted => RDrev fork code g s0
  | .staticViolation => RDstatic fork code g s0

end Benchmarks.CompoundIII.Comet
