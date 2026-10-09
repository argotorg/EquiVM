import Reasoning.SolmBody

open Solm Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: uniformly transport a callee result into its caller.
def internalCallResult (caller : Frame) (retVar : Ident) : ExecResult → ExecResult
  | .returned _ evm values => .ok (resumeAfterInternalCall caller retVar values) evm
  | result => result

theorem internalCallFunctionResult {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store} {result : ExecResult}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg { caller with locals := locals } evm callee.body result) :
    ExecStmt cfg caller evm (.internalCall name args retVar)
      (internalCallResult caller retVar result) := by
  cases result with
  | returned frame evm' values => exact internalCallFunctionReturn hargs hlookup hbind hbody
  | reverted => exact internalCallFunctionRevert hargs hlookup hbind hbody
  | staticViolation =>
    exact ExecStmt.internalCallStatic hargs hlookup hbind hbody
  | ok _ _ | «break» _ _ | «continue» _ _ => cases hbody

end Benchmarks.Safe
