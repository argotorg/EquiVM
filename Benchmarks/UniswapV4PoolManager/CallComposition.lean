import Benchmarks.UniswapV4PoolManager.SourceComposition

/-! Composing internal calls without repeating every callee branch. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: translate a function result into its caller's result.
def resumeCallResult (caller : Frame) (retVar : Ident) (result : ExecResult) : ExecResult :=
  match result with
  | .returned _ evm value => .ok (resumeAfterInternalCall caller retVar value) evm
  | .staticViolation => .staticViolation
  | _ => .reverted

theorem resumeCallResult_ite (f : Frame) (ret : Ident) (p : Prop) [Decidable p] (a b : ExecResult) :
    resumeCallResult f ret (if p then a else b) =
      if p then resumeCallResult f ret a else resumeCallResult f ret b := by split <;> rfl

theorem resumeCallResult_returned (f cf : Frame) (ret : Ident) (evm : EVM.State) (value : Option (List Value)) :
    resumeCallResult f ret (.returned cf evm value) = .ok (resumeAfterInternalCall f ret value) evm := rfl
theorem resumeCallResult_reverted (f : Frame) (ret : Ident) :
    resumeCallResult f ret .reverted = .reverted := rfl
theorem resumeCallResult_static (f : Frame) (ret : Ident) :
    resumeCallResult f ret .staticViolation = .staticViolation := rfl

theorem internalCallFunctionExec {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store} {result : ExecResult}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg {caller with locals := locals} evm callee.body result) :
    ExecStmt cfg caller evm (.internalCall name args retVar) (resumeCallResult caller retVar result) := by
  cases hbody with
  | execBlockOK h => exact internalCallFunctionReturn hargs hlookup hbind (.execBlockOK h)
  | execBlockRet h => exact internalCallFunctionReturn hargs hlookup hbind (.execBlockRet h)
  | execBlockRevert h => exact internalCallFunctionRevert hargs hlookup hbind (.execBlockRevert h)
  | execBlockBreak h => exact internalCallFunctionReturn hargs hlookup hbind (.execBlockBreak h)
  | execBlockContinue h => exact internalCallFunctionReturn hargs hlookup hbind (.execBlockContinue h)
  | execBlockStatic h => exact ExecStmt.internalCallStatic hargs hlookup hbind (.execBlockStatic h)

-- LIBRARY CANDIDATE: function fallthrough and malformed loop exits return no values.
def finishBlockResult (result : ExecResult) : ExecResult :=
  match result with
  | .ok f evm | .break f evm | .continue f evm => .returned f evm none
  | result => result

theorem finishBlockResult_ite (p : Prop) [Decidable p] (a b : ExecResult) :
    finishBlockResult (if p then a else b) = if p then finishBlockResult a else finishBlockResult b := by split <;> rfl
theorem finishBlockResult_ok (f : Frame) (evm : EVM.State) :
    finishBlockResult (.ok f evm) = .returned f evm none := rfl
theorem finishBlockResult_reverted : finishBlockResult .reverted = .reverted := rfl
theorem finishBlockResult_static : finishBlockResult .staticViolation = .staticViolation := rfl

-- LIBRARY CANDIDATE: lift a block using the function body's return convention.
theorem execFuncBody_block {cfg : Config} {f : Frame} {evm : EVM.State} {stmts : List Stmt} {result : ExecResult}
    (h : ExecBlock cfg f evm stmts result) :
    ExecFuncBody cfg f evm stmts (finishBlockResult result) := by
  cases result with
  | ok => exact .execBlockOK h
  | returned => exact .execBlockRet h
  | reverted => exact .execBlockRevert h
  | «break» => exact .execBlockBreak h
  | «continue» => exact .execBlockContinue h
  | staticViolation => exact .execBlockStatic h

theorem execFuncBody_singleton {cfg : Config} {f : Frame} {evm : EVM.State} {stmt : Stmt} {result : ExecResult}
    (h : ExecStmt cfg f evm stmt result) :
    ExecFuncBody cfg f evm [stmt] (finishBlockResult result) := execFuncBody_block (execBlock_singleton h)

end Benchmarks.UniswapV4PoolManager
