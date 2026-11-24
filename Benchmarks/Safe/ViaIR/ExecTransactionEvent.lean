import Benchmarks.Safe.ViaIR.ExecTransactionPaymentTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_023
import Benchmarks.Safe.ViaIR.Blocks.Runtime_024

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execEventStmt : Stmt :=
  .ite (.var "success") [.emit "ExecutionSuccess" [.var "txHash", .var "payment"]]
    [.emit "ExecutionFailure" [.var "txHash", .var "payment"]]

def execEventLogPC (z : Bool) : UInt256 := if z then ⟨4770⟩ else ⟨4931⟩

def execEventTopic (z : Bool) : UInt256 :=
  if z then ⟨30839331137535485569665531618491634834793013124148307919264258885536190059886⟩
  else ⟨15948521614687691110761868893838234996960037361152471596931148700057464241443⟩

theorem safeExecEventSource {frame : Frame} {evm : EVM.State} {z : Bool} {hash paid : UInt256}
    (hz : frame.locals["success"]? = some (.bool z))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hp : frame.locals["payment"]? = some (uint256Value paid))
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config frame evm execEventStmt (.ok frame evm) := by
  have he := evalLocalValue (cfg := config) (evm := evm) hz
  have ha : evalExprs? config frame evm [.var "txHash", .var "payment"] =
      .ok [wordBytes32Value hash, uint256Value paid] := by
    simp only [evalExprs?, evalLocalValue hh, evalLocalValue hp, bind, EvalResult.bind, pure]
  cases z
  · exact .iteFalse he (.consNormal (.emit (hperm := hperm) ha) .nil)
  · exact .iteTrue he (.consNormal (.emit (hperm := hperm) ha) .nil)

theorem safeExecEventSourceStatic {frame : Frame} {evm : EVM.State} {z : Bool}
    {hash paid : UInt256} (hz : frame.locals["success"]? = some (.bool z))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hp : frame.locals["payment"]? = some (uint256Value paid))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt fork config frame evm execEventStmt .staticViolation := by
  have he := evalLocalValue (cfg := config) (evm := evm) hz
  have ha : evalExprs? config frame evm [.var "txHash", .var "payment"] =
      .ok [wordBytes32Value hash, uint256Value paid] := by
    simp only [evalExprs?, evalLocalValue hh, evalLocalValue hp, bind, EvalResult.bind, pure]
  cases z
  · exact .iteFalse he (.consStatic (.emitStatic ha hperm))
  · exact .iteTrue he (.consStatic (.emitStatic ha hperm))

set_option maxRecDepth 5000 in
theorem safeExecEventPrepare {I g s0 σ k C aw mem rdata} {guard hash paid : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4763⟩ (execEventSaved guard hash paid z R)
      mem aw rdata σ k C) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 (execEventLogPC z)
      (execEventSaved guard hash paid z R) mem aw rdata σ k' C' := by
  simp only [execEventSaved, List.cons_append, List.nil_append] at h ⊢
  have h₁ := evm_run h with [dup4, push0, eq, push2 ⟨4931⟩]
  cases z
  · exact ⟨_, _, RD.jumpiT h₁ (by native_decide) (by decide) (by jump_dest)
      (by simp; omega)⟩
  · exact ⟨_, _, RD.jumpiNT h₁ (by native_decide) (by decide) (by simp; omega)⟩

set_option maxRecDepth 5000 in
theorem safeExecEventLog {I g s0 σ k C aw mem rdata paid hash}
    {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 (execEventLogPC z) (paid :: hash :: R)
      mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hp : I.perm = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4813⟩ R
      (writeWord mem (memLoad ⟨64⟩ mem).toNat paid) aw' rdata σ k' C' := by
  cases z
  · exact safeRuntime_block_4931_packed hov hp (by jump_dest) h
  · exact safeRuntime_block_4770_packed hov hp h

set_option maxRecDepth 5000 in
theorem safeExecEventLogStatic {I g s0 σ k C aw mem rdata paid hash}
    {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 (execEventLogPC z) (paid :: hash :: R)
      mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hp : I.perm = false) : RDstatic fork safeBytecode g s0 := by
  cases z
  · have h₁ := evm_run h with [jumpdest, push1 ⟨32⟩]
    have h₂ := RD.pushConst (width := 32) (op := .PUSH32) h₁ (execEventTopic false)
      (by decide) (by native_decide) (by simp; omega)
    have h₃ := evm_run h₂ with [swap2, push1 ⟨64⟩, genMload, swap1, dup2, genMstore]
    exact RD.log2Static h₃ hp (by native_decide) (by omega)
  · have h₁ := evm_run h with [push1 ⟨32⟩]
    have h₂ := RD.pushConst (width := 32) (op := .PUSH32) h₁ (execEventTopic true)
      (by decide) (by native_decide) (by simp; omega)
    have h₃ := evm_run h₂ with [swap2, push1 ⟨64⟩, genMload, swap1, dup2, genMstore]
    exact RD.log2Static h₃ hp (by native_decide) (by omega)

end Benchmarks.Safe.ViaIR
