import Benchmarks.UniswapV4PoolManager.SettleSource
import Benchmarks.UniswapV4PoolManager.ReturnCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def settleEntryStatements (recipientExpr : Expr) : List Stmt := calldataPrefix ++
  [.internalCall "Lock_isUnlocked" [] "__c0",
   .ite (.unary .not (.var "__c0")) [.require (.boolLit false)] [],
   .internalCall "_settle" [recipientExpr] "__c1", .return [.var "__c1"]]

def settleEntryFrame (locals imms : Store) (evm : EVM.State) : Frame :=
  let f := calldataFrame contract locals imms evm
  {f with locals := f.locals.insert "__c0" (.bool true)}

theorem settleEntryLocked {evm : EVM.State} {locals imms : Store} (recipientExpr : Expr)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hl : transientWord evm lockSlot = ⟨0⟩) :
    ExecTransitionBody config contract evm locals (settleEntryStatements recipientExpr) .reverted imms := by
  have hlock := lockCall (f := calldataFrame contract locals imms evm) (evm := evm) rfl "__c0"
  rw [decide_eq_false (not_not.mpr hl)] at hlock
  apply ExecFuncBody.execBlockRevert
  apply calldataBlock hhi
  exact ExecBlock.consNormal hlock (ExecBlock.consRevert (ExecStmt.iteTrue
    (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
    (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))

theorem settleEntryReturnsCall {evm : EVM.State} {locals imms : Store} {recipient : AccountAddress}
    {recipientExpr : Expr} {result : ExecResult}
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hl : transientWord evm lockSlot ≠ ⟨0⟩)
    (hr : evalExpr? config (settleEntryFrame locals imms evm) evm recipientExpr = .ok (.address recipient))
    (hbody : ExecFuncBody config
      {settleEntryFrame locals imms evm with locals := (∅ : Store).insert "recipient" (.address recipient)}
      evm settleFunction.body result) :
    ExecTransitionBody config contract evm locals (settleEntryStatements recipientExpr)
      (returnCallResult (settleEntryFrame locals imms evm) "__c1" result) imms := by
  have hlock := lockCall (f := calldataFrame contract locals imms evm) (evm := evm) rfl "__c0"
  rw [decide_eq_true hl] at hlock
  have hcall := internalCallThenReturn (retVar := "__c1") (evalExprs?_singleton hr)
    settleFunction_lookup rfl hbody
  apply calldataBody hhi
  apply execFuncBody_prepend (pre := [.internalCall "Lock_isUnlocked" [] "__c0",
    .ite (.unary .not (.var "__c0")) [.require (.boolLit false)] []]) ?_ hcall
  exact ExecBlock.consNormal hlock (ExecBlock.consNormal (ExecStmt.iteFalse
    (evalNotBool (va := true) (evalLocalValue (store_get_self _ _ _))) ExecBlock.nil) ExecBlock.nil)

end Benchmarks.UniswapV4PoolManager
