import Benchmarks.Midnight.MulticallDecode
import Benchmarks.Midnight.FlashLoanLoopSource

/-! Source evaluation of the multicall loop, its delegate call, and its guards. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def multicallLoopCondition : Expr :=
  .binary .lt (.var "i") (.arrayLength .localVar { base := "calls" })

def multicallReturnGuard : Expr :=
  .binary .le (.arrayLength .localVar { base := "returnData" }) (.intLit (2^64 - 1))

def multicallLoopBody : List Stmt :=
  [.letDecl "self" (some Model.addr) (.env .this),
    .delegateCall (.var "self") (.index (.var "calls") (.var "i")) "success" "returnData",
    .require multicallReturnGuard,
    .ite (.unary .not (.var "success")) [.require (.boolLit false)] []]

def multicallSelfFrame (frame : Frame) (evm : State) : Frame :=
  { frame with locals := frame.locals.insert "self" (.address evm.executionEnv.codeOwner) }

def multicallCallFrame (frame : Frame) (evm : State) (success : Bool) (out : ByteArray) : Frame :=
  { multicallSelfFrame frame evm with locals :=
    ((((multicallSelfFrame frame evm).locals).insert "success" (.bool success)).insert
      "returnData" (.bytes out)) }

theorem multicallLoop_shape : multicallTransition.body.drop 3 =
    [.for [.letDecl "i" (some Model.u256) (.intLit 0)]
      multicallLoopCondition flashLoanLoopPost multicallLoopBody] := rfl

theorem multicallLoopCondition_eval {frame : Frame} {evm : State} {calls : List ByteArray} {i : Nat}
    (hf : frame.locals.get? "calls" = some (.array (calls.map Value.bytes)))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) :
    evalExpr? config frame evm multicallLoopCondition = .ok (.bool (decide (i < calls.length))) := by
  simp only [multicallLoopCondition, evalExpr?, hi, hf, readLocalPath?, List.length_map,
    EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Int.ofNat_lt]

theorem multicallIndex_eval {frame : Frame} {evm : State} {calls : List ByteArray} {i : Nat}
    (hf : frame.locals.get? "calls" = some (.array (calls.map Value.bytes)))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) (hb : i < calls.length) :
    evalExpr? config frame evm (.index (.var "calls") (.var "i")) = .ok (.bytes calls[i]) := by
  simp only [evalExpr?, hf, hi, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?]
  rw [if_pos (by simpa only [List.length_map, Int.ofNat_eq_natCast,
    Int.natCast_nonneg, true_and, Int.ofNat_lt] using hb)]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  rw [lookupNth_get _ i (by simpa only [List.length_map] using hb)]
  simp only [List.getElem_map]
  rfl

theorem multicallCallFrame_get {frame : Frame} {evm : State} {success : Bool} {out : ByteArray}
    (name : Ident) (hn : name ∉ ["self", "success", "returnData"]) :
    (multicallCallFrame frame evm success out).locals.get? name = frame.locals.get? name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  simp [multicallCallFrame, multicallSelfFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Ne.symm hn.1, Ne.symm hn.2.1, Ne.symm hn.2.2]

-- LIBRARY CANDIDATE: a raw delegate call binds both success and failure results.
theorem delegateCallSource {cfg : Config} {frame : Frame} {evm evm' : State}
    {receiver cdata : Expr} {target : AccountAddress} {calldata out : ByteArray}
    {success data : Ident} {z : Bool}
    (hr : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hd : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hc : delegateCallViaEVM evm target calldata (z, evm', out)) :
    ExecStmt cfg frame evm (.delegateCall receiver cdata success data)
      (.ok { frame with locals := (frame.locals.insert success (.bool z)).insert data (.bytes out) }
        evm') := by
  have ht : EVM.address target.val = target := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt target.isLt
  rw [← ht] at hc
  cases z with
  | false => exact ExecStmt.delegateCallFailure hr hd hc
  | true => exact ExecStmt.delegateCallSuccess hr hd hc

theorem multicallSourceCall {frame : Frame} {evm evm' : State} {calls : List ByteArray}
    {i : Nat} {success : Bool} {out : ByteArray}
    (hf : frame.locals.get? "calls" = some (.array (calls.map Value.bytes)))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) (hb : i < calls.length)
    (hc : delegateCallViaEVM evm evm.executionEnv.codeOwner calls[i] (success, evm', out))
    {result : ExecResult}
    (htail : ExecBlock config (multicallCallFrame frame evm success out) evm'
      (multicallLoopBody.drop 2) result) :
    ExecBlock config frame evm multicallLoopBody result := by
  refine ExecBlock.consNormal (stele' := multicallSelfFrame frame evm) (ExecStmt.letDecl ?_) ?_
  · simp only [evalExpr?, envValue, pure]
  apply ExecBlock.consNormal (stele' := multicallCallFrame frame evm success out) ?_ htail
  apply delegateCallSource ?_ ?_ hc
  · simp [evalExpr?, multicallSelfFrame, Std.HashMap.get?_eq_getElem?, EvalResult.ofOption]
  · apply multicallIndex_eval (calls := calls) (i := i) ?_ ?_ hb
    · simpa only [multicallSelfFrame,
        store_get_ne (k := "self") (a := "calls") _ _ (by decide)] using hf
    · simpa only [multicallSelfFrame,
        store_get_ne (k := "self") (a := "i") _ _ (by decide)] using hi

theorem multicallReturnGuard_eval (frame : Frame) (evm evm' : State) (success : Bool)
    (out : ByteArray) :
    evalExpr? config (multicallCallFrame frame evm success out) evm' multicallReturnGuard =
      .ok (.bool (decide (out.size < 2^64))) := by
  have hr : (multicallCallFrame frame evm success out).locals.get? "returnData" =
      some (.bytes out) := store_get_self _ _ _
  simp only [multicallReturnGuard, evalExpr?, readLocalPath?, hr, EvalResult.ofOption,
    bind, pure, EvalResult.bind, evalBinaryOp?]
  simp only [Int.ofNat_eq_natCast]
  congr 2
  congr 1
  apply propext
  omega

theorem multicallSuccessGuard_eval (frame : Frame) (evm evm' : State) (success : Bool)
    (out : ByteArray) :
    evalExpr? config (multicallCallFrame frame evm success out) evm'
      (.unary .not (.var "success")) = .ok (.bool (!success)) := by
  have hr : (multicallCallFrame frame evm success out).locals.get? "success" =
      some (.bool success) := by
    exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
  simp only [evalExpr?, hr, EvalResult.ofOption, bind, pure, EvalResult.bind, evalUnaryOp?]

theorem multicallSourceReturn {frame : Frame} {evm evm' : State} {calls : List ByteArray}
    {i : Nat} {out : ByteArray}
    (hf : frame.locals.get? "calls" = some (.array (calls.map Value.bytes)))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) (hb : i < calls.length)
    (hc : delegateCallViaEVM evm evm.executionEnv.codeOwner calls[i] (true, evm', out))
    (hout : out.size < 2^64) :
    ExecBlock config frame evm multicallLoopBody
      (.ok (multicallCallFrame frame evm true out) evm') := by
  apply multicallSourceCall hf hi hb hc
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [multicallReturnGuard_eval, decide_eq_true hout]
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
  exact multicallSuccessGuard_eval frame evm evm' true out

theorem multicallSourceRevert {frame : Frame} {evm evm' : State} {calls : List ByteArray}
    {i : Nat} {success : Bool} {out : ByteArray}
    (hf : frame.locals.get? "calls" = some (.array (calls.map Value.bytes)))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i))) (hb : i < calls.length)
    (hc : delegateCallViaEVM evm evm.executionEnv.codeOwner calls[i] (success, evm', out))
    (hbad : success = false ∨ 2^64 ≤ out.size) :
    ExecBlock config frame evm multicallLoopBody .reverted := by
  apply multicallSourceCall hf hi hb hc
  by_cases hout : out.size < 2^64
  · have hz : success = false := hbad.resolve_right (by omega)
    subst success
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · rw [multicallReturnGuard_eval, decide_eq_true hout]
    apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
    · exact multicallSuccessGuard_eval frame evm evm' false out
    · exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, pure]))
  · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    rw [multicallReturnGuard_eval, decide_eq_false hout]

theorem multicallLoopStatement {frame : Frame} {evm : State} {result : ExecResult}
    (h : ExecForLoop config (flashLoanSetIndex frame 0) evm multicallLoopCondition
      flashLoanLoopPost multicallLoopBody result) :
    ExecStmt config frame evm
      (.for [.letDecl "i" (some Model.u256) (.intLit 0)]
        multicallLoopCondition flashLoanLoopPost multicallLoopBody) result := by
  apply ExecStmt.for (ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil) h
  simp [evalExpr?, pure, Int.ofNat_eq_natCast]

end Benchmarks.Midnight
