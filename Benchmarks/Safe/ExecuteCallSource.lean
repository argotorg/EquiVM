import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def executeCallStmt : Stmt :=
  .ite (eqE (.var "operation") (.intLit 1))
    [.delegateCall (.var "to") (.var "data") "success" "returnData"]
    [.lowLevelCall (.var "to") (.var "value") (.var "data") "success" "returnData"]

def executeCallFrame (frame : Frame) (z : Bool) (out : ByteArray) : Frame :=
  { frame with
    locals := (frame.locals.insert "success" (.bool z)).insert "returnData" (.bytes out) }

structure ExecuteLocals (frame : Frame) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation : UInt256) : Prop where
  target : frame.locals["to"]? = some (.address target)
  value : frame.locals["value"]? = some (.int (Int.ofNat value.toNat))
  data : frame.locals["data"]? = some (.bytes payload)
  operation : frame.locals["operation"]? = some (.int (Int.ofNat operation.toNat))

def executeViaEVM (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation : UInt256) (z : Bool) (evm' : EVM.State)
    (out : ByteArray) : Prop :=
  (operation = ⟨1⟩ ∧ delegateCallViaEVM evm (EVM.address target) payload (z, evm', out)) ∨
    (operation ≠ ⟨1⟩ ∧
      callViaEVM evm (EVM.address target) (Int.ofNat value.toNat) payload (z, evm', out))

theorem safeExecuteCallCondition {cfg : Config} {frame : Frame} {evm : EVM.State}
    {target : EVM.Address} {value operation : UInt256} {payload : ByteArray}
    (hl : ExecuteLocals frame target value payload operation) :
    evalExpr? cfg frame evm (eqE (.var "operation") (.intLit 1)) =
      .ok (.bool (decide (operation = ⟨1⟩))) := by
  simp [eqE, evalExpr?, hl.operation, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp_eq_int_ok]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro h
    apply u256_inj
    change operation.toNat = 1
    omega
  · intro h
    subst operation
    rfl

theorem safeExecuteCallStatement {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {target : EVM.Address} {value operation : UInt256} {payload out : ByteArray} {z : Bool}
    (hl : ExecuteLocals frame target value payload operation)
    (hc : executeViaEVM evm target value payload operation z evm' out) :
    ExecStmt cfg frame evm executeCallStmt (.ok (executeCallFrame frame z out) evm') := by
  have ht : evalExpr? cfg frame evm (.var "to") = .ok (.address target) := by
    simp [evalExpr?, hl.target, EvalResult.ofOption, pure]
  have hv : evalExpr? cfg frame evm (.var "value") = .ok (.int (Int.ofNat value.toNat)) := by
    simp [evalExpr?, hl.value, EvalResult.ofOption, pure]
  have hd : evalExpr? cfg frame evm (.var "data") = .ok (.bytes payload) := by
    simp [evalExpr?, hl.data, EvalResult.ofOption, pure]
  rcases hc with ⟨hop, hc⟩ | ⟨hop, hc⟩
  · apply ExecStmt.iteTrue (by simpa only [hop, decide_true] using safeExecuteCallCondition hl)
    cases z
    · exact .consNormal (.delegateCallFailure ht hd hc) .nil
    · exact .consNormal (.delegateCallSuccess ht hd hc) .nil
  · apply ExecStmt.iteFalse (by simpa only [hop, decide_false] using safeExecuteCallCondition hl)
    cases z
    · exact .consNormal (.lowLevelCallFailure ht hv hd hc) .nil
    · exact .consNormal (.lowLevelCallSuccess ht hv hd hc) .nil

theorem safeExecuteCallStatementStatic {cfg : Config} {frame : Frame} {evm : EVM.State}
    {target : EVM.Address} {value operation : UInt256} {payload : ByteArray}
    (hl : ExecuteLocals frame target value payload operation)
    (hop : operation ≠ ⟨1⟩) (hp : evm.executionEnv.perm = false) (hv : value ≠ ⟨0⟩) :
    ExecStmt cfg frame evm executeCallStmt .staticViolation := by
  apply ExecStmt.iteFalse (by simpa only [hop, decide_false] using safeExecuteCallCondition hl)
  exact .consStatic (.lowLevelCallStatic (sendVal := Int.ofNat value.toNat)
    (target := target) (calldata := payload) (by
      simp [evalExpr?, hl.target, EvalResult.ofOption, pure]) (by
      simp [evalExpr?, hl.value, EvalResult.ofOption, pure]) (by
      simp [evalExpr?, hl.data, EvalResult.ofOption, pure])
    (by simpa only [wordOfInt_ofNat_toNat] using hv) hp)

end Benchmarks.Safe
