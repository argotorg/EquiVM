import Benchmarks.UniswapV4PoolManager.CallComposition
import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: returning the value bound by an internal call.
def returnCallResult (caller : Frame) (retVar : Ident) (result : ExecResult) : ExecResult :=
  match result with
  | .returned _ evm value =>
    .returned (resumeAfterInternalCall caller retVar value) evm
      (some [(value.map collapseReturns).getD .unit])
  | .staticViolation => .staticViolation
  | _ => .reverted

theorem internalCallThenReturn {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store} {result : ExecResult}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg {caller with locals := locals} evm callee.body result) :
    ExecFuncBody cfg caller evm [.internalCall name args retVar, .return [.var retVar]]
      (returnCallResult caller retVar result) := by
  have hc := internalCallFunctionExec (retVar := retVar) hargs hlookup hbind hbody
  cases result with
  | ok => cases hbody
  | «break» => cases hbody
  | «continue» => cases hbody
  | reverted => exact .execBlockRevert (ExecBlock.consRevert hc)
  | staticViolation => exact .execBlockStatic (ExecBlock.consStatic hc)
  | returned cf evm' value =>
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal hc
    apply ABlock.start.returns
    cases value <;> exact evalLocalValue (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager
