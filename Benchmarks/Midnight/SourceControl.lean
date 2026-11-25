import Benchmarks.Midnight.InternalCall

variable {fork : Ethereum.Fork}

/-! Compositional source steps used by branching internal functions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Reasoning.Theory.assignLocalVarBase_ok: preserve an arbitrary frame.
theorem execLocalAssign {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value} {expr : Expr}
    (hget : frame.locals.get? name = some old)
    (heval : evalExpr? cfg frame evm expr = .ok value) :
    ExecStmt fork cfg frame evm (.assign .localVar { base := name } expr)
      (.ok { frame with locals := frame.locals.insert name value } evm) := by
  apply ExecStmt.assign (Or.inl rfl) heval
  simp only [assignStorageRef?, hget, updateLocalPath?, bind, pure, EvalResult.bind]

-- LIBRARY CANDIDATE: comparison of a word-valued local with a natural literal.
theorem evalLocalLtNat {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {word : UInt256} (n : Nat)
    (hget : frame.locals.get? name = some (.int word.toNat)) :
    evalExpr? cfg frame evm (.binary .lt (.var name) (.intLit n)) =
      .ok (.bool (decide (word.toNat < n))) := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, pure, EvalResult.bind,
    evalBinaryOp?, Int.ofNat_lt]

theorem evalLocalGeNat {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {word : UInt256} (n : Nat)
    (hget : frame.locals.get? name = some (.int word.toNat)) :
    evalExpr? cfg frame evm (.binary .ge (.var name) (.intLit n)) =
      .ok (.bool (decide (n ≤ word.toNat))) := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, pure, EvalResult.bind,
    evalBinaryOp?, Int.ofNat_le]

-- LIBRARY CANDIDATE: an else-if branch whose nested statement completes normally.
theorem execElseIf {cfg : Config} {frame frame' : Frame} {evm evm' : EVM.State}
    {cond : Expr} {thenBody : List Stmt} {nested : Stmt}
    (heval : evalExpr? cfg frame evm cond = .ok (.bool false))
    (hbody : ExecStmt fork cfg frame evm nested (.ok frame' evm')) :
    ExecStmt fork cfg frame evm (.ite cond thenBody [nested]) (.ok frame' evm') :=
  ExecStmt.iteFalse heval (ExecBlock.consNormal hbody ExecBlock.nil)

end Benchmarks.Midnight
