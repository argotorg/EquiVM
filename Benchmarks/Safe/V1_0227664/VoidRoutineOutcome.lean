import Benchmarks.Safe.V1_0227664.InternalCall
import Reasoning.Reach

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V1_0227664

-- LIBRARY CANDIDATE: source block outcomes paired with a void bytecode routine's exits.
inductive VoidRoutineOutcome (fork : Ethereum.Fork) (cfg : Config) (frame : Frame) (evm : EVM.State)
    (body : List Stmt) (code : ByteArray) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (ret : UInt256) (R : List UInt256) : Prop where
  | reverted (source : ExecBlock fork cfg frame evm body .reverted) (trace : RDrev fork code g s0)
  | staticHalt (source : ExecBlock fork cfg frame evm body .staticViolation)
      (trace : RDstatic fork code g s0)
  | success {frame' evm' mem aw rdata k C}
      (source : ExecBlock fork cfg frame evm body (.ok frame' evm'))
      (trace : RD fork code I g s0 ret R mem aw rdata evm'.accountMap k C)

theorem VoidRoutineOutcome.prepend {cfg frame frame' evm evm' stmt body code I g s0 ret R}
    (h : VoidRoutineOutcome fork cfg frame' evm' body code I g s0 ret R)
    (hs : ExecStmt fork cfg frame evm stmt (.ok frame' evm')) :
    VoidRoutineOutcome fork cfg frame evm (stmt :: body) code I g s0 ret R := by
  cases h with
  | reverted source trace => exact .reverted (.consNormal hs source) trace
  | staticHalt source trace => exact .staticHalt (.consNormal hs source) trace
  | success source trace => exact .success (.consNormal hs source) trace

end Benchmarks.Safe.V1_0227664
