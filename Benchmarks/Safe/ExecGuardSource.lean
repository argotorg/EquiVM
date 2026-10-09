import Benchmarks.Safe.ExecGuardCallEncoding
import Benchmarks.Safe.ExecTransactionSignatureSource
import Benchmarks.Safe.OptionalCheckedCall
import Benchmarks.Safe.PreModuleSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execGuardArgumentExprs : List Expr :=
  [.var "to", .var "value", .var "data", .var "operation", .var "safeTxGas", .var "baseGas",
    .var "gasPrice", .var "gasToken", .var "refundReceiver", .var "signatures", sender]

def execGuardCheck : Stmt :=
  optionalCheckedCall (.var "guard") "checkTransaction" execGuardArgumentExprs "_guardChecked"

def execGuardWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner guardSlot

def execGuardFrame (p : ExecTransactionInput) (initial current : EVM.State) : Frame :=
  { contract := contract
    locals := (execSignedFrame p initial).locals.insert
      "guard" (.address (AccountAddress.ofUInt256 (execGuardWord current))) }

theorem execGuardFrame_locals (p : ExecTransactionInput) (initial current : EVM.State) :
    ExecTransactionLocals p (execGuardFrame p initial current).locals :=
  (execSignedFrame_locals p initial).set _ _ (by decide)

theorem safeExecGuardArguments (p : ExecTransactionInput) (evm : EVM.State) {locals : Store}
    (hl : ExecTransactionLocals p locals) :
    evalExprs? config { contract := contract, locals := locals } evm execGuardArgumentExprs =
      .ok (execGuardArguments p evm.executionEnv.source) := by
  simp only [execGuardArgumentExprs, execGuardArguments, uint256Value, evalExprs?, evalExpr?,
    sender, envValue, Std.HashMap.get?_eq_getElem?,
    hl.tx.target, hl.tx.value, hl.tx.data, hl.tx.operation,
    hl.tx.safeTxGas, hl.tx.baseGas, hl.tx.gasPrice, hl.tx.gasToken, hl.tx.refundReceiver,
    hl.signatures, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem safeExecGuardLoad (p : ExecTransactionInput) (initial current : EVM.State) :
    ExecStmt config (execSignedFrame p initial) current
      (.letDecl "guard" (some addr) (.storage guardRef))
      (.ok (execGuardFrame p initial current) current) := by
  apply ExecStmt.letDecl
  apply evalExpr_storage_scalar_value (er := { base := "_guard" })
    (loc := wordLoc guardSlot .address)
  · simp [execSignedFrame, resumeAfterInternalCall, execHashFrame, execNonceFrame,
      ExecTransactionInput.args, guardRef, Std.HashMap.getElem_insert]
  · simp [evalStorageRef, evalStorageRefSteps, guardRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact storageLocLoad_address_word current guardSlot

end Benchmarks.Safe
