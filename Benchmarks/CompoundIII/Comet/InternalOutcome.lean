import Benchmarks.CompoundIII.Comet.Common
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: outcomes shared by a void internal function and its callers.
inductive InternalOutcome where
  | ok (evm : EVM.State)
  | reverted
  | staticViolation

def internalSourceResult (fork : Ethereum.Fork) (cfg : Config) (frame : Frame) (evm : EVM.State)
    (body : List Stmt) (result : InternalOutcome) : Prop :=
  match result with
  | .ok evm' => ∃ frame', ExecFuncBody fork cfg frame evm body (.returned frame' evm' none)
  | .reverted => ExecFuncBody fork cfg frame evm body .reverted
  | .staticViolation => ExecFuncBody fork cfg frame evm body .staticViolation

def internalBlockResult (fork : Ethereum.Fork) (cfg : Config) (frame : Frame) (evm : EVM.State)
    (body : List Stmt) (result : InternalOutcome) : Prop :=
  match result with
  | .ok evm' => ∃ frame', ExecBlock fork cfg frame evm body (.ok frame' evm')
  | .reverted => ExecBlock fork cfg frame evm body .reverted
  | .staticViolation => ExecBlock fork cfg frame evm body .staticViolation

theorem internalBlockResult.toSource {cfg frame evm body result}
    (hb : internalBlockResult fork cfg frame evm body result) :
    internalSourceResult fork cfg frame evm body result := by
  cases result with
  | ok evm' =>
      obtain ⟨frame', hb⟩ := hb
      exact ⟨frame', ExecFuncBody.execBlockOK hb⟩
  | reverted => exact ExecFuncBody.execBlockRevert hb
  | staticViolation => exact ExecFuncBody.execBlockStatic hb

theorem internalBlockResult.prepend {cfg frame evm frame' evm' stmt body result}
    (hs : ExecStmt fork cfg frame evm stmt (.ok frame' evm'))
    (hb : internalBlockResult fork cfg frame' evm' body result) :
    internalBlockResult fork cfg frame evm (stmt :: body) result := by
  cases result with
  | ok evm'' =>
      obtain ⟨frame'', hb⟩ := hb
      exact ⟨frame'', ExecBlock.consNormal hs hb⟩
  | reverted => exact ExecBlock.consNormal hs hb
  | staticViolation => exact ExecBlock.consNormal hs hb

theorem internalBlockResult.iteTrue {cfg frame evm cond yes no result}
    (hc : evalExpr? cfg frame evm cond = .ok (.bool true))
    (hb : internalBlockResult fork cfg frame evm yes result) :
    internalBlockResult fork cfg frame evm [.ite cond yes no] result := by
  cases result with
  | ok evm' =>
      obtain ⟨frame', hb⟩ := hb
      exact ⟨frame', ExecBlock.consNormal (ExecStmt.iteTrue hc hb) ExecBlock.nil⟩
  | reverted => exact ExecBlock.consRevert (ExecStmt.iteTrue hc hb)
  | staticViolation => exact ExecBlock.consStatic (ExecStmt.iteTrue hc hb)

def internalStmtResult (frame : Frame) (ret : Ident) (result : InternalOutcome) : ExecResult :=
  match result with
  | .ok evm' => .ok { frame with locals := frame.locals.insert ret .unit } evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

theorem internalVoidCall {cfg frame evm name args ret callee locals argVals result}
    (ha : evalExprs? cfg frame evm args = .ok argVals)
    (hf : lookupCallable? frame.contract name = some callee)
    (hp : bindParams? callee.params argVals = some locals)
    (hb : internalSourceResult fork cfg { frame with locals := locals } evm callee.body result) :
    ExecStmt fork cfg frame evm (.internalCall name args ret) (internalStmtResult frame ret result) := by
  cases result with
  | ok evm' =>
      obtain ⟨frame', hb⟩ := hb
      exact ExecStmt.internalCallReturn ha hf hp hb
  | reverted => exact ExecStmt.internalCallRevert ha hf hp hb
  | staticViolation => exact ExecStmt.internalCallStatic ha hf hp hb

def internalRun (fork : Ethereum.Fork) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (result : InternalOutcome) : Prop :=
  match result with
  | .ok evm => ∃ σ k C, SourceState s0 ee σ evm ∧ RD fork code ee g s0 ret R mem aw rdata σ k C
  | .reverted => RDrev fork code g s0
  | .staticViolation => RDstatic fork code g s0

end Benchmarks.CompoundIII.Comet
