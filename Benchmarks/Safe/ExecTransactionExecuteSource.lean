import Benchmarks.Safe.ExecTransactionContext
import Benchmarks.Safe.ExecuteCallerSource
import Benchmarks.Safe.SignatureSwitchSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execExecuteFrame (locals : Store) (before gasLeft : UInt256) : Frame :=
  { contract := contract
    locals := (locals.insert "gasBefore" (uint256Value before)).insert
      "txGasLeft" (uint256Value gasLeft) }

def execCallGasExpr : Expr :=
  .ite (eqE (.var "gasPrice") (.intLit 0))
    (sub256 (.var "txGasLeft") (.intLit 2500)) (.var "safeTxGas")

def execExecuteCall : Stmt :=
  .internalCall "execute"
    [.var "to", .var "value", .var "data", .var "operation", execCallGasExpr] "success"

def execCallGas (p : ExecTransactionInput) (gasLeft : UInt256) : UInt256 :=
  if p.tx.gasPrice = ⟨0⟩ then UInt256.sub gasLeft ⟨2500⟩ else p.tx.safeTxGas

theorem execExecuteFrame_locals {p : ExecTransactionInput} {locals : Store}
    (hl : ExecTransactionLocals p locals) (before gasLeft : UInt256) :
    ExecTransactionLocals p (execExecuteFrame locals before gasLeft).locals :=
  ((hl.set _ _ (by decide)).set _ _ (by decide))

theorem safeExecCallGas (p : ExecTransactionInput) (evm : EVM.State) {locals : Store}
    {gasLeft : UInt256} (hl : ExecTransactionLocals p locals)
    (hg : locals["txGasLeft"]? = some (uint256Value gasLeft))
    (hfit : p.tx.gasPrice = ⟨0⟩ → 2500 ≤ gasLeft.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm execCallGasExpr =
      .ok (uint256Value (execCallGas p gasLeft)) := by
  have he := naturalEqSource (cfg := config) (frame := { contract := contract, locals := locals })
    (evm := evm) (rhs := .intLit 0) (evalLocalValue hl.tx.gasPrice) (b := 0)
    (by simp [evalExpr?, pure])
  rw [execCallGasExpr, evalExpr?, eqE, he]
  by_cases hz : p.tx.gasPrice = ⟨0⟩
  · have hn : p.tx.gasPrice.toNat = 0 := by rw [hz]; rfl
    simp only [hn, decide_true, bind, EvalResult.bind, execCallGas, if_pos hz]
    exact evalExpr_uint256_sub (evalLocalValue hg) (b := ⟨2500⟩)
      (by simp [evalExpr?, uint256Value, pure]; decide +kernel) (hfit hz)
  · have hn : p.tx.gasPrice.toNat ≠ 0 := fun h ↦ hz (uint256_toNat_eq_zero h)
    simp only [hn, decide_false, bind, EvalResult.bind, execCallGas, if_neg hz]
    exact evalLocalValue hl.tx.safeTxGas

theorem safeExecCallGasRevert (p : ExecTransactionInput) (evm : EVM.State) {locals : Store}
    {gasLeft : UInt256} (hl : ExecTransactionLocals p locals)
    (hg : locals["txGasLeft"]? = some (uint256Value gasLeft))
    (hz : p.tx.gasPrice = ⟨0⟩) (hfit : gasLeft.toNat < 2500) :
    evalExpr? config { contract := contract, locals := locals } evm execCallGasExpr = .revert :=
    by
  have he := naturalEqSource (cfg := config) (frame := { contract := contract, locals := locals })
    (evm := evm) (rhs := .intLit 0) (evalLocalValue hl.tx.gasPrice) (b := 0)
    (by simp [evalExpr?, pure])
  have hn : p.tx.gasPrice.toNat = 0 := by rw [hz]; rfl
  rw [execCallGasExpr, evalExpr?, eqE, he]
  simp only [hn, decide_true, bind, EvalResult.bind]
  exact evalExpr_checkedSub256_revert (evalLocalValue hg) (b := ⟨2500⟩)
    (by simp [evalExpr?, uint256Value, pure]; decide +kernel) hfit

theorem safeExecExecuteCall (p : ExecTransactionInput) (evm : EVM.State) {locals : Store}
    {txGas : UInt256} {result : ExecResult} (hl : ExecTransactionLocals p locals)
    (hg : evalExpr? config { contract := contract, locals := locals } evm execCallGasExpr =
      .ok (uint256Value txGas))
    (hb : ExecFuncBody config (executeFrame p.tx.target p.tx.value p.tx.payload p.tx.operation
      txGas) evm executeFunction.body result) :
    ExecStmt config { contract := contract, locals := locals } evm execExecuteCall
      (internalCallResult { contract := contract, locals := locals } "success" result) :=
  safeInternalExecute rfl rfl (evalLocalValue hl.tx.target) (evalLocalValue hl.tx.value)
    (evalLocalValue hl.tx.data) (evalLocalValue hl.tx.operation) hg hb

theorem safeExecExecuteArgsRevert (p : ExecTransactionInput) (evm : EVM.State) {locals : Store}
    (hl : ExecTransactionLocals p locals)
    (hg : evalExpr? config { contract := contract, locals := locals } evm execCallGasExpr =
      .revert) :
    ExecStmt config { contract := contract, locals := locals } evm execExecuteCall .reverted :=
    by
  apply ExecStmt.internalCallArgsRevert
  simp only [evalExprs?, hg, evalExpr?, Std.HashMap.get?_eq_getElem?, hl.tx.target, hl.tx.value,
    hl.tx.data, hl.tx.operation, EvalResult.ofOption, EvalResult.bind, bind]

end Benchmarks.Safe
