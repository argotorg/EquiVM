import Benchmarks.Safe.InternalCall
import Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: source block outcomes paired with a void bytecode routine's exits.
inductive VoidRoutineOutcome (cfg : Config) (frame : Frame) (evm : EVM.State)
    (body : List Stmt) (code : ByteArray) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (ret : UInt256) (R : List UInt256) : Prop where
  | reverted (source : ExecBlock cfg frame evm body .reverted) (trace : RDrev code g s0)
  | staticHalt (source : ExecBlock cfg frame evm body .staticViolation)
      (trace : RDstatic code g s0)
  | success {frame' evm' mem aw rdata k C}
      (source : ExecBlock cfg frame evm body (.ok frame' evm'))
      (trace : RD code I g s0 ret R mem aw rdata evm'.accountMap k C)

theorem VoidRoutineOutcome.prepend {cfg frame frame' evm evm' stmt body code I g s0 ret R}
    (h : VoidRoutineOutcome cfg frame' evm' body code I g s0 ret R)
    (hs : ExecStmt cfg frame evm stmt (.ok frame' evm')) :
    VoidRoutineOutcome cfg frame evm (stmt :: body) code I g s0 ret R := by
  cases h with
  | reverted source trace => exact .reverted (.consNormal hs source) trace
  | staticHalt source trace => exact .staticHalt (.consNormal hs source) trace
  | success source trace => exact .success (.consNormal hs source) trace

end Benchmarks.Safe
