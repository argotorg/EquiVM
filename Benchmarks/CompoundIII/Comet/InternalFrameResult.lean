import Benchmarks.CompoundIII.Comet.InternalOutcome

open Solm

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: a block outcome with a specified frame on its normal path.
def internalFrameResult (frame : Frame) : InternalOutcome → ExecResult
  | .ok evm => .ok frame evm
  | .reverted => .reverted
  | .staticViolation => .staticViolation

end Benchmarks.CompoundIII.Comet
