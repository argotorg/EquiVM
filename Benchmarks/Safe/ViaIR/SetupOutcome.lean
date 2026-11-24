import Benchmarks.Safe.ViaIR.SetupSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

inductive SetupOutcome (fork : Ethereum.Fork) (frame : Frame) (evm : State) (body : List Stmt)
    (g : Sat256) (s0 : State) : Prop where
  | reverted (source : ExecBlock fork config frame evm body .reverted)
      (trace : RDrev fork safeBytecode g s0)
  | staticHalt (source : ExecBlock fork config frame evm body .staticViolation)
      (trace : RDstatic fork safeBytecode g s0)
  | success {frame' evm'} (source : ExecBlock fork config frame evm body (.ok frame' evm'))
      (trace : RDret fork safeBytecode g s0 evm'.accountMap ByteArray.empty)

/-- A setup tail either establishes the local allocation guard or reports its failure. -/
inductive SetupTailOutcome (fork : Ethereum.Fork) (p : SetupInput) (frame : Frame) (evm : State) (body : List Stmt)
    (g : Sat256) (s0 : State) : Prop where
  | allocationRevert (bound : ¬32 * p.owners.length + p.payload.size ≤ p.allocationLimit)
      (trace : RDrev fork safeBytecode g s0)
  | reverted (source : ExecBlock fork config frame evm body .reverted)
      (trace : RDrev fork safeBytecode g s0)
  | success {frame' evm'} (bound : 32 * p.owners.length + p.payload.size ≤ p.allocationLimit)
      (source : ExecBlock fork config frame evm body (.ok frame' evm'))
      (trace : RDret fork safeBytecode g s0 evm'.accountMap ByteArray.empty)

theorem SetupTailOutcome.prepend {p frame frame' evm evm' stmt body g s0}
    (h : SetupTailOutcome fork p frame' evm' body g s0)
    (hs : ExecStmt fork config frame evm stmt (.ok frame' evm')) :
    SetupTailOutcome fork p frame evm (stmt :: body) g s0 := by
  cases h with
  | allocationRevert bound trace => exact .allocationRevert bound trace
  | reverted source trace => exact .reverted (.consNormal hs source) trace
  | success bound source trace => exact .success bound (.consNormal hs source) trace

end Benchmarks.Safe.ViaIR
