import Benchmarks.Safe.ExecTransactionContext
import Benchmarks.Safe.PaymentTrace
import Benchmarks.Safe.SignatureBranchSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execPaymentInput (p : ExecTransactionInput) (used : UInt256) : PaymentInput :=
  ⟨used, p.tx.baseGas, p.tx.gasPrice, p.tx.gasToken, p.tx.refundReceiver⟩

def execPaymentInit (locals : Store) : Frame :=
  { contract := contract, locals := locals.insert "payment" (uint256Value ⟨0⟩) }

def execPaymentFinal (locals : Store) (paid : UInt256) (called : Bool) : Frame :=
  { contract := contract
    locals := if called then
      ((execPaymentInit locals).locals.insert "paymentCall" (uint256Value paid)).insert
        "payment" (uint256Value paid)
    else locals.insert "payment" (uint256Value paid) }

def execPaymentStmt : Stmt :=
  .ite (gtE (.var "gasPrice") (.intLit 0))
    [.internalCall "handlePayment"
      [.var "gasUsed", .var "baseGas", .var "gasPrice", .var "gasToken",
        .var "refundReceiver"] "paymentCall",
      .assign .localVar (varRef "payment") (.var "paymentCall")] []

theorem execPaymentFinal_locals {p locals} (hl : ExecTransactionLocals p locals)
    (paid : UInt256) (called : Bool) :
    ExecTransactionLocals p (execPaymentFinal locals paid called).locals := by
  cases called
  · exact hl.set _ _ (by decide)
  · exact (((hl.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide))

theorem execPaymentFinal_get (locals : Store) (paid : UInt256) (called : Bool)
    (name : Ident) (hn : name ≠ "payment") (hc : name ≠ "paymentCall") :
    (execPaymentFinal locals paid called).locals[name]? = locals[name]? := by
  cases called <;> simp [execPaymentFinal, execPaymentInit, Std.HashMap.getElem?_insert,
    Ne.symm hn, Ne.symm hc]

theorem execPaymentFinal_paid (locals : Store) (paid : UInt256) (called : Bool) :
    (execPaymentFinal locals paid called).locals["payment"]? = some (uint256Value paid) := by
  cases called <;> simp [execPaymentFinal]

theorem safeExecPaymentInit (locals : Store) (evm : EVM.State) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.letDecl "payment" (some uint256) (.intLit 0)) (.ok (execPaymentInit locals) evm) :=
  .letDecl (by simp [evalExpr?, uint256Value, pure])

theorem safeExecPaymentCondition (p : ExecTransactionInput) (evm : EVM.State) {locals : Store}
    (hl : ExecTransactionLocals p locals) :
    evalExpr? config { contract := contract, locals := locals } evm
      (gtE (.var "gasPrice") (.intLit 0)) = .ok (.bool (decide (p.tx.gasPrice ≠ ⟨0⟩))) := by
  have hp : 0 < p.tx.gasPrice.toNat ↔ p.tx.gasPrice ≠ ⟨0⟩ := by
    constructor
    · intro h hz; rw [hz] at h; exact (Nat.lt_irrefl 0) h
    · intro h; exact Nat.pos_of_ne_zero (fun he ↦ h (uint256_toNat_eq_zero he))
  simpa only [gtE, hp] using evalExpr_uint256_var_positive
    (frame := { contract := contract, locals := locals }) evm "gasPrice" p.tx.gasPrice
    (by simpa only [Std.HashMap.get?_eq_getElem?] using hl.tx.gasPrice)

theorem safeExecPaymentCall (p : ExecTransactionInput) (evm : EVM.State) {locals : Store}
    {used : UInt256} {result : ExecResult} (hl : ExecTransactionLocals p locals)
    (hu : locals["gasUsed"]? = some (uint256Value used))
    (hb : ExecFuncBody config (execPaymentInput p used).frame evm handlePaymentFunction.body
      result) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "handlePayment"
        [.var "gasUsed", .var "baseGas", .var "gasPrice", .var "gasToken",
          .var "refundReceiver"] "paymentCall")
      (internalCallResult { contract := contract, locals := locals } "paymentCall" result) :=
  safeInternalPayment (p := execPaymentInput p used) rfl rfl (evalLocalValue hu)
    (evalLocalValue hl.tx.baseGas) (evalLocalValue hl.tx.gasPrice)
    (evalLocalValue hl.tx.gasToken) (evalLocalValue hl.tx.refundReceiver) hb

theorem safeExecPaymentAssign (locals : Store) (evm : EVM.State) (paid : UInt256) :
    ExecStmt config
      (resumeAfterInternalCall (execPaymentInit locals) "paymentCall"
        (some [uint256Value paid])) evm
      (.assign .localVar (varRef "payment") (.var "paymentCall"))
      (.ok (execPaymentFinal locals paid true) evm) := by
  apply ExecStmt.assign (value := uint256Value paid)
  · apply evalLocalValue
    simp [resumeAfterInternalCall, collapseReturns]
  · apply assignLocalValue (old := uint256Value ⟨0⟩)
    simp [resumeAfterInternalCall, collapseReturns, execPaymentInit,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

end Benchmarks.Safe
