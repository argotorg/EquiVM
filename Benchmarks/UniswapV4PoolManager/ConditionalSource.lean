import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a conditional rejection with an arbitrary boolean expression.
theorem execStmt_rejectIf {cfg : Config} {f : Frame} {evm : State} {cond : Expr} {b : Bool}
    (hc : evalExpr? cfg f evm cond = .ok (.bool b)) :
    ExecStmt cfg f evm (.ite cond [.require (.boolLit false)] [])
      (if b then .reverted else .ok f evm) := by
  cases b with
  | false => exact ExecStmt.iteFalse hc ExecBlock.nil
  | true => exact ExecStmt.iteTrue hc (ExecBlock.consRevert
      (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))

-- LIBRARY CANDIDATE: conditional calls preceded by a compiler-generated storage alias.
theorem execStmt_conditionalAliasCall {cfg : Config} {f : Frame} {evm : State} {cond : Expr} {b : Bool}
    {aliasName : Ident} {ref : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {call : Stmt} {result : ExecResult}
    (hc : evalExpr? cfg f evm cond = .ok (.bool b))
    (ha : resolveStorageRef? cfg f evm ref = .ok (er, ty))
    (hcall : ExecStmt cfg {f with locals := f.locals.insert aliasName (.storageRef er ty)} evm call result) :
    ExecStmt cfg f evm (.ite cond [.letStorage aliasName ref, call] []) (if b then result else .ok f evm) := by
  cases b with
  | false => exact ExecStmt.iteFalse hc ExecBlock.nil
  | true => exact ExecStmt.iteTrue hc (ExecBlock.consNormal (ExecStmt.letStorage ha) (execBlock_singleton hcall))

end Benchmarks.UniswapV4PoolManager
