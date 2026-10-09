import Benchmarks.Safe.ExecTransactionGasUsed
import Benchmarks.Safe.Blocks.Runtime_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def execEventStmt : Stmt :=
  .ite (.var "success") [.emit "ExecutionSuccess" [.var "txHash", .var "payment"]]
    [.emit "ExecutionFailure" [.var "txHash", .var "payment"]]

def execEventLogPC (z : Bool) : UInt256 := if z then ⟨4072⟩ else ⟨4135⟩

def execEventTopic (z : Bool) : UInt256 :=
  if z then ⟨30839331137535485569665531618491634834793013124148307919264258885536190059886⟩
  else ⟨15948521614687691110761868893838234996960037361152471596931148700057464241443⟩

theorem safeExecEventSource {frame : Frame} {evm : EVM.State} {z : Bool} {hash paid : UInt256}
    (hz : frame.locals["success"]? = some (.bool z))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hp : frame.locals["payment"]? = some (uint256Value paid)) :
    ExecStmt config frame evm execEventStmt (.ok frame evm) := by
  have he := evalLocalValue (cfg := config) (evm := evm) hz
  have ha : evalExprs? config frame evm [.var "txHash", .var "payment"] =
      .ok [wordBytes32Value hash, uint256Value paid] := by
    simp only [evalExprs?, evalLocalValue hh, evalLocalValue hp, bind, EvalResult.bind, pure]
  cases z
  · exact .iteFalse he (.consNormal (.emit ha) .nil)
  · exact .iteTrue he (.consNormal (.emit ha) .nil)

theorem safeExecEventSourceStatic {frame : Frame} {evm : EVM.State} {z : Bool}
    {hash paid : UInt256} (hz : frame.locals["success"]? = some (.bool z))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hp : frame.locals["payment"]? = some (uint256Value paid))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config frame evm execEventStmt .staticViolation := by
  have he := evalLocalValue (cfg := config) (evm := evm) hz
  have ha : evalExprs? config frame evm [.var "txHash", .var "payment"] =
      .ok [wordBytes32Value hash, uint256Value paid] := by
    simp only [evalExprs?, evalLocalValue hh, evalLocalValue hp, bind, EvalResult.bind, pure]
  cases z
  · exact .iteFalse he (.consStatic (.emitStatic ha hperm))
  · exact .iteTrue he (.consStatic (.emitStatic ha hperm))

set_option maxRecDepth 100000 in
theorem safeExecEventPrepare (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src} {sigPtr guard hash used paid : UInt256}
    {z : Bool} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4016⟩
      (paid :: used :: execResultSaved p src sigPtr guard hash z R) mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 (execEventLogPC z)
      ([UInt256.ofNat 32 + memLoad ⟨64⟩ mem, execEventTopic z, hash, paid, used] ++
        execResultSaved p src sigPtr guard hash z R)
      (writeWord mem (memLoad ⟨64⟩ mem).toNat paid) aw' rdata σ k' C' := by
  cases z
  · have h₁ := safeRuntime_block_4016_taken (by simp [execResultSaved]; omega)
      (by decide) (by jump_dest) h
    exact safeRuntime_block_4085_packed (by simp [execResultSaved]; omega) (by jump_dest) h₁
  · have h₁ := safeRuntime_block_4016_fallthrough (by simp [execResultSaved]; omega)
      (by decide) h
    exact safeRuntime_block_4023_packed (by simp [execResultSaved]; omega) (by jump_dest) h₁

set_option maxRecDepth 100000 in
theorem safeExecEventLog {I g s0 σ k C aw mem rdata finish topic hash}
    {R : List UInt256} (z : Bool)
    (h : RD safeBytecode I g s0 (execEventLogPC z) (finish :: topic :: hash :: R)
      mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hp : I.perm = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨4144⟩ R mem aw' rdata σ k' C' := by
  cases z
  · exact safeRuntime_block_4135_packed hov hp h
  · exact safeRuntime_block_4072_packed hov hp (by jump_dest) h

set_option maxRecDepth 100000 in
theorem safeExecEventLogStatic {I g s0 σ k C aw mem rdata finish topic hash}
    {R : List UInt256} (z : Bool)
    (h : RD safeBytecode I g s0 (execEventLogPC z) (finish :: topic :: hash :: R)
      mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hp : I.perm = false) : RDstatic safeBytecode g s0 := by
  cases z <;>
    have h₁ := evm_run h with [jumpdest, push1 ⟨64⟩, genMload, dup1, swap2, sub, swap1]
  · exact RD.log2Static h₁ hp (by native_decide) (by omega)
  · exact RD.log2Static h₁ hp (by native_decide) (by omega)

end Benchmarks.Safe
