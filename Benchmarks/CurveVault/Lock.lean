import Benchmarks.CurveVault.Common
import Reasoning.TransientStorage
import Reasoning.SteleArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultLockExpr : Expr := .binary .ne
  (.transient {base := "nonreentrant_lock", steps := []}) (.intLit 1)

theorem vaultLockRead (evm : EVM.State) (locals : Store) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.transient {base := "nonreentrant_lock", steps := []}) =
      .ok (.int (Int.ofNat (Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply evalExpr_transient_scalar_value
    (er := {base := "nonreentrant_lock", steps := []})
    (t := .int (.uint ⟨256, by decide⟩))
    (loc := uint256Loc ⟨0⟩)
    (by simp [evalTransientStorageRef, evalTransientStorageRefSteps, EvalResult.bind, pure, bind])
    rfl rfl rfl
  exact transientLocLoad_uint256 evm ⟨0⟩

theorem vaultLockEval_pass (evm : EVM.State) (locals : Store)
    (h : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩) :
    evalExpr? config {contract := contract, locals := locals} evm vaultLockExpr = .ok (.bool true) := by
  apply evalExpr_ne_int_true (b := 1) (vaultLockRead evm locals) (by simp [evalExpr?, pure])
  intro hn
  apply h
  apply uInt256_toNat_eq_one
  exact Int.ofNat.inj hn

theorem vaultLockEval_fail (evm : EVM.State) (locals : Store)
    (h : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨1⟩) :
    evalExpr? config {contract := contract, locals := locals} evm vaultLockExpr = .ok (.bool false) := by
  apply evalExpr_ne_int_false (b := 1) (vaultLockRead evm locals) (by simp [evalExpr?, pure])
  rw [h]
  rfl

theorem vaultLockedBodyReverts (evm : EVM.State) (locals : Store) (rest : List Stmt)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨1⟩) :
    ExecTransitionBody fork config contract evm locals
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: .require vaultLockExpr :: rest)
      .reverted :=
  ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) <|
      ExecBlock.consRevert (ExecStmt.requireFalse (vaultLockEval_fail evm locals hlock))

theorem vaultViewBodyReturns {evm calleeEvm : EVM.State} {locals calleeLocals : Store}
    {fn : FunctionDecl} {calleeStele : Frame} {args : List Expr} {argVals : List Value} {value : Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩)
    (hargs : evalExprs? config {contract := contract, locals := locals} evm args = .ok argVals)
    (hlookup : lookupCallable? contract fn.name = some fn.toCallable)
    (hbind : bindParams? fn.params argVals = some calleeLocals)
    (hbody : ExecFuncBody fork config {contract := contract, locals := calleeLocals} evm fn.body
      (.returned calleeStele calleeEvm (some [value]))) :
    ExecTransitionBody fork config contract evm locals
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .require vaultLockExpr,
        .internalCall fn.name args "__r", .return [.var "__r"]]
      (.returned {contract := contract, locals := locals.insert "__r" value} calleeEvm (some [value])) := by
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (retVar := "__r") hargs hlookup hbind hbody
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock)) <|
        ExecBlock.consNormal hcall <|
          ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
            simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption])))

theorem vaultViewBodyReverts {evm : EVM.State} {locals calleeLocals : Store}
    {fn : FunctionDecl} {args : List Expr} {argVals : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩)
    (hargs : evalExprs? config {contract := contract, locals := locals} evm args = .ok argVals)
    (hlookup : lookupCallable? contract fn.name = some fn.toCallable)
    (hbind : bindParams? fn.params argVals = some calleeLocals)
    (hbody : ExecFuncBody fork config {contract := contract, locals := calleeLocals} evm fn.body .reverted) :
    ExecTransitionBody fork config contract evm locals
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .require vaultLockExpr,
        .internalCall fn.name args "__r", .return [.var "__r"]] .reverted :=
  ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock)) <|
        ExecBlock.consRevert (internalCallFunctionRevert hargs hlookup hbind hbody)

end Benchmarks.CurveVault
