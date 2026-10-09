import Benchmarks.Safe.PreModuleSource
import Benchmarks.Safe.ExecuteSource
import Benchmarks.Safe.PostModuleSource
import Benchmarks.Safe.InternalCall
import Benchmarks.Safe.ModuleArguments
import Benchmarks.Safe.Operation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def moduleAfterPre (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation : UInt256) (guard : EVM.Address) (hash : UInt256) : Frame :=
  resumeAfterInternalCall (moduleFrame target value payload operation) "pre"
    (some [.address guard, .fixedBytes bytes32Width (EVM.Word.toBytesBE hash)])

def moduleAfterExecute (target : EVM.Address) (value : UInt256) (payload : ByteArray)
    (operation : UInt256) (guard : EVM.Address) (hash : UInt256) (z : Bool) : Frame :=
  resumeAfterInternalCall (moduleAfterPre target value payload operation guard hash)
    "success" (some [.bool z])

def modulePreCall : Stmt :=
  .internalCall "preModuleExecution" [.var "to", .var "value", .var "data", .var "operation"] "pre"

def moduleExecuteCall : Stmt :=
  .internalCall "execute"
    [.var "to", .var "value", .var "data", .var "operation", maxUint256Expr] "success"

def modulePostCall : Stmt :=
  .internalCall "postModuleExecution" [tuple0 (.var "pre"), tuple1 (.var "pre"), .var "success"]
    "_post"

theorem safeModulePreCall {evm : EVM.State} {target : EVM.Address} {payload : ByteArray}
    {value operation : UInt256} {result : ExecResult}
    (hbody : ExecFuncBody config (preModuleFrame target value payload operation) evm
      preModuleExecutionFunction.body result) :
    ExecStmt config (moduleFrame target value payload operation) evm modulePreCall
      (internalCallResult (moduleFrame target value payload operation) "pre" result) := by
  apply internalCallFunctionResult (callee := preModuleExecutionFunction)
    (argVals := [.address target, .int (Int.ofNat value.toNat), .bytes payload,
      .int (Int.ofNat operation.toNat)])
    (locals := preModuleArgs target value payload operation)
  · simp [moduleFrame, moduleArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · exact hbody

theorem safeModuleExecuteCall {evm : EVM.State} {target guard : EVM.Address}
    {payload : ByteArray} {value operation hash : UInt256} {result : ExecResult}
    (hbody : ExecFuncBody config (executeFrame target value payload operation (UInt256.lnot ⟨0⟩))
      evm executeFunction.body result) :
    ExecStmt config (moduleAfterPre target value payload operation guard hash) evm
      moduleExecuteCall
      (internalCallResult (moduleAfterPre target value payload operation guard hash)
        "success" result) := by
  apply internalCallFunctionResult (callee := executeFunction)
    (argVals := [.address target, .int (Int.ofNat value.toNat), .bytes payload,
      .int (Int.ofNat operation.toNat), .int (Int.ofNat (UInt256.lnot ⟨0⟩).toNat)])
    (locals := executeArgs target value payload operation (UInt256.lnot ⟨0⟩))
  · simp [moduleAfterPre, moduleFrame, moduleArgs, resumeAfterInternalCall,
      evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      Std.HashMap.getElem_insert, maxUint256Expr, maxUint256]
    decide +kernel
  · rfl
  · rfl
  · exact hbody

theorem safeModulePostCall {evm : EVM.State} {target guard : EVM.Address}
    {payload : ByteArray} {value operation hash : UInt256} {z : Bool} {result : ExecResult}
    (hbody : ExecFuncBody config (postModuleFrame guard hash z) evm
      postModuleExecutionFunction.body result) :
    ExecStmt config (moduleAfterExecute target value payload operation guard hash z) evm
      modulePostCall
      (internalCallResult (moduleAfterExecute target value payload operation guard hash z)
        "_post" result) := by
  apply internalCallFunctionResult (callee := postModuleExecutionFunction)
    (argVals := [.address guard, .fixedBytes bytes32Width (EVM.Word.toBytesBE hash), .bool z])
    (locals := postModuleArgs guard hash z)
  · simp [moduleAfterExecute, moduleAfterPre, moduleFrame, moduleArgs,
      resumeAfterInternalCall, collapseReturns, tuple0, tuple1, tupleGetValue?, evalExprs?,
      evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · exact hbody

def moduleCallTail : List Stmt :=
  [modulePreCall, moduleExecuteCall, modulePostCall, .return [.var "success"]]

-- LIBRARY CANDIDATE: a local bytes-length guard from its sole local lookup.
theorem evalLocalBytesLengthLe {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {payload : ByteArray} (bound : Nat)
    (hl : frame.locals[name]? = some (.bytes payload)) :
    evalExpr? cfg frame evm
      (.binary .le (.arrayLength .localVar { base := name }) (.intLit (Int.ofNat bound))) =
        .ok (.bool (decide (payload.size ≤ bound))) := by
  simp [evalExpr?, evalStorageRef, evalStorageRefSteps, readLocalPath?, hl,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, Int.ofNat_eq_natCast]

theorem safeModuleLength (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation : UInt256) :
    evalExpr? config (moduleFrame target value payload operation) evm
      (leE (localLength "data") (.intLit (2 ^ 64 - 192))) =
        .ok (.bool (decide (payload.size ≤ 2 ^ 64 - 192))) := by
  exact evalLocalBytesLengthLe _ (by
    simp [moduleFrame, moduleArgs, Std.HashMap.getElem_insert])

theorem safeModuleOperation (evm : EVM.State) (target : EVM.Address) (value : UInt256)
    (payload : ByteArray) (operation : UInt256) :
    evalExpr? config (moduleFrame target value payload operation) evm validOperation =
      .ok (.bool (decide (operation.toNat < 2))) := by
  exact evalValidOperation (by
    simp [moduleFrame, moduleArgs, Std.HashMap.getElem_insert])

theorem safeModuleChecks {evm : EVM.State} {target : EVM.Address} {value operation : UInt256}
    {payload : ByteArray} {result : ExecResult} {tail : List Stmt}
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hn : payload.size ≤ 2 ^ 64 - 192)
    (ho : operation.toNat < 2)
    (ht : ExecBlock config (moduleFrame target value payload operation) evm tail result) :
    ExecBlock config (moduleFrame target value payload operation) evm
      (nonpayable ++ decodeMemoryBytes "data" ++ .require validOperation :: tail) result := by
  exact .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by
      simpa only [hn, decide_true] using safeModuleLength evm target value payload operation))
      (.consNormal (.requireTrue (by
        simpa only [ho, decide_true] using
          safeModuleOperation evm target value payload operation)) ht))

theorem safeModuleInvalidChecks {evm : EVM.State} {target : EVM.Address} {value operation : UInt256}
    {payload : ByteArray} {tail : List Stmt}
    (hbad : ¬payload.size ≤ 2 ^ 64 - 192 ∨ ¬operation.toNat < 2) :
    ExecTransitionBody config contract evm (moduleArgs target value payload operation)
      (nonpayable ++ decodeMemoryBytes "data" ++ .require validOperation :: tail) .reverted := by
  by_cases hv : evm.executionEnv.weiValue = ⟨0⟩
  swap
  · exact bodyReverts_nonPayable hv
  apply ExecFuncBody.execBlockRevert
  refine .consNormal (.requireTrue (evalCallvalueEq_true hv)) ?_
  by_cases hn : payload.size ≤ 2 ^ 64 - 192
  swap
  · exact .consRevert (.requireFalse (by
      simpa only [hn, decide_false] using safeModuleLength evm target value payload operation))
  refine .consNormal (.requireTrue (by
    simpa only [hn, decide_true] using safeModuleLength evm target value payload operation)) ?_
  have ho : ¬operation.toNat < 2 := hbad.resolve_left (not_not_intro hn)
  exact .consRevert (.requireFalse (by
    simpa only [ho, decide_false] using safeModuleOperation evm target value payload operation))

theorem safeModulePrefix {evm : EVM.State} {target : EVM.Address} {value operation : UInt256}
    {payload : ByteArray} {result : ExecResult}
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hn : payload.size ≤ 2 ^ 64 - 192)
    (ho : operation.toNat < 2)
    (ht : ExecBlock config (moduleFrame target value payload operation) evm moduleCallTail result) :
    ExecBlock config (moduleFrame target value payload operation) evm
      exectransactionfrommoduleTransition.body result := by
  exact safeModuleChecks hv hn ho ht

theorem safeModuleInvalid {evm : EVM.State} {target : EVM.Address} {value operation : UInt256}
    {payload : ByteArray} (hbad : ¬payload.size ≤ 2 ^ 64 - 192 ∨ ¬operation.toNat < 2) :
    ExecTransitionBody config contract evm (moduleArgs target value payload operation)
      exectransactionfrommoduleTransition.body .reverted := by
  exact safeModuleInvalidChecks hbad

theorem safeModuleReturn (evm : EVM.State) (target guard : EVM.Address)
    (value operation hash : UInt256) (payload : ByteArray) (z : Bool) :
    ExecBlock config
      (resumeAfterInternalCall (moduleAfterExecute target value payload operation guard hash z)
        "_post" none) evm [.return [.var "success"]]
      (.returned
        (resumeAfterInternalCall (moduleAfterExecute target value payload operation guard hash z)
          "_post" none) evm (some [.bool z])) := by
  exact .consReturn (.return (by
    simp [moduleAfterExecute, resumeAfterInternalCall, collapseReturns, evalExprs?, evalExpr?,
      EvalResult.ofOption, EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]))

end Benchmarks.Safe
