import Benchmarks.Safe.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def postModuleArgs (guard : EVM.Address) (hash : UInt256) (z : Bool) : Store :=
  (((∅ : Store).insert "success" (.bool z)).insert
    "guardHash" (.fixedBytes bytes32Width (EVM.Word.toBytesBE hash))).insert
      "guard" (.address guard)

def postModuleFrame (guard : EVM.Address) (hash : UInt256) (z : Bool) : Frame :=
  { contract := contract, locals := postModuleArgs guard hash z }

def postModuleCheck : Stmt :=
  .ite (neE (.var "guard") zeroAddr)
    (checkedExternalCallStmts (.var "guard") "checkAfterModuleExecution" (.intLit 0)
      [.var "guardHash", .var "success"] "_after") []

def postModuleEmit : Stmt :=
  .ite (.var "success") [.emit "ExecutionFromModuleSuccess" [sender]]
    [.emit "ExecutionFromModuleFailure" [sender]]

theorem safePostModuleCondition (evm : EVM.State) (guard : EVM.Address)
    (hash : UInt256) (z : Bool) :
    evalExpr? config (postModuleFrame guard hash z) evm (neE (.var "guard") zeroAddr) =
      .ok (.bool (decide (guard ≠ 0))) := by
  simp [postModuleFrame, postModuleArgs, neE, zeroAddr, addrSt, evalExpr?, castValue?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert, evalBinaryOp?]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]
  rfl

theorem safePostModuleReceiver (evm : EVM.State) (guard : EVM.Address)
    (hash : UInt256) (z : Bool) :
    evalExpr? config (postModuleFrame guard hash z) evm (.var "guard") =
      .ok (.address guard) := by
  simp [postModuleFrame, postModuleArgs, evalExpr?, EvalResult.ofOption,
    pure, Std.HashMap.getElem_insert]

theorem safePostModuleArguments (evm : EVM.State) (guard : EVM.Address)
    (hash : UInt256) (z : Bool) :
    evalExprs? config (postModuleFrame guard hash z) evm [.var "guardHash", .var "success"] =
      .ok [.fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z] := by
  simp [postModuleFrame, postModuleArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]

theorem safePostModuleCheckZero (evm : EVM.State) (hash : UInt256) (z : Bool) :
    ExecStmt config (postModuleFrame 0 hash z) evm postModuleCheck
      (.ok (postModuleFrame 0 hash z) evm) := by
  exact .iteFalse (by simpa using safePostModuleCondition evm 0 hash z) .nil

theorem safePostModuleCheckNoCode {evm : EVM.State} {guard : EVM.Address}
    {hash target : UInt256} {z : Bool} (hg : guard ≠ 0)
    (ht : guard = AccountAddress.ofUInt256 target)
    (hc : extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    ExecStmt config (postModuleFrame guard hash z) evm postModuleCheck .reverted := by
  apply ExecStmt.iteTrue (by simpa [hg] using safePostModuleCondition evm guard hash z)
  apply checkedExternalCallNoCode
  simpa only [hc, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalExpr_codeGuard_of_accounts_eq rfl ht (safePostModuleReceiver evm guard hash z)

theorem safePostModuleCheckFailed {evm evm' : EVM.State} {guard : EVM.Address}
    {hash target : UInt256} {z : Bool} {out : ByteArray} (hg : guard ≠ 0)
    (ht : guard = AccountAddress.ofUInt256 target)
    (hc : extCodeSizeWord evm.accountMap target ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm (EVM.address guard) "checkAfterModuleExecution" 0
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z] (false, evm', out)) :
    ExecStmt config (postModuleFrame guard hash z) evm postModuleCheck .reverted := by
  apply ExecStmt.iteTrue (by simpa [hg] using safePostModuleCondition evm guard hash z)
  apply checkedExternalCallFailure _ (safePostModuleReceiver evm guard hash z)
    (safePostModuleArguments evm guard hash z) hcall
  have hp : 0 < (extCodeSizeWord evm.accountMap target).toNat :=
    Nat.pos_of_ne_zero (fun hz ↦ hc (u256_inj hz))
  simpa only [hp, decide_true] using
    evalExpr_codeGuard_of_accounts_eq rfl ht (safePostModuleReceiver evm guard hash z)

theorem safePostModuleCheckSuccess {evm evm' : EVM.State} {guard : EVM.Address}
    {hash target : UInt256} {z : Bool} {out : ByteArray} (hg : guard ≠ 0)
    (ht : guard = AccountAddress.ofUInt256 target)
    (hc : extCodeSizeWord evm.accountMap target ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm (EVM.address guard) "checkAfterModuleExecution" 0
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z] (true, evm', out)) :
    ExecStmt config (postModuleFrame guard hash z) evm postModuleCheck
      (.ok { postModuleFrame guard hash z with
        locals := (postModuleArgs guard hash z).insert "_after" (collapseReturns []) } evm') := by
  apply ExecStmt.iteTrue (by simpa [hg] using safePostModuleCondition evm guard hash z)
  apply checkedExternalCallSuccess _ (safePostModuleReceiver evm guard hash z)
    (safePostModuleArguments evm guard hash z) hcall rfl
  have hp : 0 < (extCodeSizeWord evm.accountMap target).toNat :=
    Nat.pos_of_ne_zero (fun hz ↦ hc (u256_inj hz))
  simpa only [hp, decide_true] using
    evalExpr_codeGuard_of_accounts_eq rfl ht (safePostModuleReceiver evm guard hash z)

theorem safePostModuleEvent (evm : EVM.State) (frame : Frame) (z : Bool)
    (hs : frame.locals["success"]? = some (.bool z)) :
    ExecStmt config frame evm postModuleEmit (.ok frame evm) := by
  have he : evalExpr? config frame evm (.var "success") = .ok (.bool z) := by
    simp [evalExpr?, EvalResult.ofOption, hs]
  have ha : evalExprs? config frame evm [sender] = .ok [.address evm.executionEnv.source] := by
    simp only [evalExprs?, sender, evalExpr?, envValue, bind, EvalResult.bind, pure]
  cases z
  · exact .iteFalse he (.consNormal (.emit ha) .nil)
  · exact .iteTrue he (.consNormal (.emit ha) .nil)

theorem safePostModuleEventStatic (evm : EVM.State) (frame : Frame) (z : Bool)
    (hs : frame.locals["success"]? = some (.bool z))
    (hp : evm.executionEnv.perm = false) :
    ExecStmt config frame evm postModuleEmit .staticViolation := by
  have he : evalExpr? config frame evm (.var "success") = .ok (.bool z) := by
    simp [evalExpr?, EvalResult.ofOption, hs]
  have ha : evalExprs? config frame evm [sender] = .ok [.address evm.executionEnv.source] := by
    simp only [evalExprs?, sender, evalExpr?, envValue, bind, EvalResult.bind, pure]
  cases z
  · exact .iteFalse he (.consStatic (.emitStatic ha hp))
  · exact .iteTrue he (.consStatic (.emitStatic ha hp))

theorem safePostModuleSourceRevert {evm : EVM.State} {guard : EVM.Address}
    {hash : UInt256} {z : Bool}
    (hc : ExecStmt config (postModuleFrame guard hash z) evm postModuleCheck .reverted) :
    ExecFuncBody config (postModuleFrame guard hash z) evm postModuleExecutionFunction.body
      .reverted :=
  .execBlockRevert (.consRevert hc)

theorem safePostModuleSourceSuccess {evm evm' : EVM.State} {guard : EVM.Address}
    {hash : UInt256} {z : Bool} {frame : Frame}
    (hc : ExecStmt config (postModuleFrame guard hash z) evm postModuleCheck (.ok frame evm'))
    (hs : frame.locals["success"]? = some (.bool z)) :
    ExecFuncBody config (postModuleFrame guard hash z) evm postModuleExecutionFunction.body
      (.returned frame evm' none) :=
  .execBlockOK (.consNormal hc (.consNormal (safePostModuleEvent evm' frame z hs) .nil))

theorem safePostModuleSourceStatic {evm evm' : EVM.State} {guard : EVM.Address}
    {hash : UInt256} {z : Bool} {frame : Frame}
    (hc : ExecStmt config (postModuleFrame guard hash z) evm postModuleCheck (.ok frame evm'))
    (hs : frame.locals["success"]? = some (.bool z)) (hp : evm'.executionEnv.perm = false) :
    ExecFuncBody config (postModuleFrame guard hash z) evm postModuleExecutionFunction.body
      .staticViolation :=
  .execBlockStatic (.consNormal hc (.consStatic (safePostModuleEventStatic evm' frame z hs hp)))

end Benchmarks.Safe
