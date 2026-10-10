import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES voidOutcomeRun to an explicit ABI return value.
def returnOutcomeRun (code : ByteArray) (g : Sat256) (s0 : State) (data : ByteArray) :
    InternalOutcome → Prop
  | .ok evm => RDret code g s0 evm.accountMap data
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

end Benchmarks.CompoundIII.Comet
