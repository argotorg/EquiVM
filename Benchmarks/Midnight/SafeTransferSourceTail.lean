import Benchmarks.Midnight.Common
import Reasoning.ExternalCall
import Reasoning.ABIComposite

/-! The common return-data checks of both safe token-transfer functions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

abbrev safeTransferFunctionFor (isFrom : Bool) : FunctionDecl :=
  if isFrom then contract.functions[13]! else contract.functions[1]!

def safeTransferCap : Expr :=
  .binary .le (.arrayLength .localVar ⟨"returndata", []⟩) (.intLit 18446744073709551615)

def safeTransferEmpty : Expr :=
  .binary .eq (.arrayLength .localVar ⟨"returndata", []⟩) (.intLit 0)

def safeTransferCondition : Expr :=
  .binary .or safeTransferEmpty (.abiDecode abiBool (.var "returndata"))

def safeTransferTail : List Stmt :=
  [.require safeTransferCap,
   .ite (.unary .not (.var "success")) [.require (.boolLit false)] [],
   .require safeTransferCondition]

theorem safeTransferFunction_tail (isFrom : Bool) :
    (safeTransferFunctionFor isFrom).body.drop 3 = safeTransferTail := by
  cases isFrom <;> rfl

theorem safeTransferLength_eval {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? config frame evm (.arrayLength .localVar ⟨"returndata", []⟩) =
      .ok (.int (Int.ofNat out.size)) := by
  simp only [evalExpr?, hout, readLocalPath?, bind, EvalResult.bind, pure]

theorem safeTransferCap_eval {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? config frame evm safeTransferCap = .ok (.bool (decide (out.size < 2 ^ 64))) := by
  have he := naturalLeSource (safeTransferLength_eval (evm := evm) hout)
    (show evalExpr? config frame evm (.intLit 18446744073709551615) =
      .ok (.int (Int.ofNat 18446744073709551615)) by simp [evalExpr?, pure])
  exact he.trans (congrArg (fun b ↦ EvalResult.ok (Value.bool b))
    (by simp only [decide_eq_decide]; omega))

theorem safeTransferEmpty_eval {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? config frame evm safeTransferEmpty = .ok (.bool (decide (out.size = 0))) := by
  simp only [safeTransferEmpty, evalExpr?, safeTransferLength_eval hout, bind, EvalResult.bind,
    pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

theorem safeTransferFailure_eval {frame : Frame} {evm : EVM.State} {success : Bool}
    (hz : frame.locals.get? "success" = some (.bool success)) :
    evalExpr? config frame evm (.unary .not (.var "success")) = .ok (.bool (!success)) := by
  simp only [evalExpr?, hz, EvalResult.ofOption, bind, EvalResult.bind, evalUnaryOp?]

theorem safeTransferCondition_empty {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hempty : out.size = 0) :
    evalExpr? config frame evm safeTransferCondition = .ok (.bool true) := by
  have he := safeTransferEmpty_eval (evm := evm) hout
  rw [decide_eq_true hempty] at he
  simp only [safeTransferCondition, evalExpr?, he, bind, EvalResult.bind, pure]

theorem safeTransferCondition_bool {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hne : out.size ≠ 0)
    {result : Bool}
    (hd : config.externalABI.decodeValue? abiBool out = some (.bool result)) :
    evalExpr? config frame evm safeTransferCondition = .ok (.bool result) := by
  have he := safeTransferEmpty_eval (evm := evm) hout
  rw [decide_eq_false hne] at he
  simp only [safeTransferCondition, evalExpr?, he, hout, EvalResult.ofOption, hd,
    bind, EvalResult.bind, pure]

theorem safeTransferCondition_bad {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hne : out.size ≠ 0)
    (hd : config.externalABI.decodeValue? abiBool out = none) :
    evalExpr? config frame evm safeTransferCondition = .revert := by
  have he := safeTransferEmpty_eval (evm := evm) hout
  rw [decide_eq_false hne] at he
  simp only [safeTransferCondition, evalExpr?, he, hout, EvalResult.ofOption, hd,
    bind, EvalResult.bind, pure]

theorem safeTransferTail_oversize {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hb : 2 ^ 64 ≤ out.size) :
    ExecBlock config frame evm safeTransferTail .reverted := by
  exact .consRevert (.requireFalse
    ((safeTransferCap_eval hout).trans (by rw [decide_eq_false (by omega)])))

theorem safeTransferTail_callFailure {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool false)) :
    ExecBlock config frame evm safeTransferTail .reverted := by
  by_cases hb : out.size < 2 ^ 64
  · apply ExecBlock.consNormal (ExecStmt.requireTrue
      ((safeTransferCap_eval hout).trans (by rw [decide_eq_true hb])))
    exact .consRevert (.iteTrue (safeTransferFailure_eval hz)
      (.consRevert (.requireFalse (by simp only [evalExpr?, pure]))))
  · exact safeTransferTail_oversize hout (by omega)

theorem safeTransferTail_decodeFailure {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool true)) (hne : out.size ≠ 0)
    (hd : config.externalABI.decodeValue? abiBool out = none ∨
      config.externalABI.decodeValue? abiBool out = some (.bool false)) :
    ExecBlock config frame evm safeTransferTail .reverted := by
  by_cases hb : out.size < 2 ^ 64
  · apply ExecBlock.consNormal (ExecStmt.requireTrue
      ((safeTransferCap_eval hout).trans (by rw [decide_eq_true hb])))
    apply ExecBlock.consNormal (ExecStmt.iteFalse (safeTransferFailure_eval hz) ExecBlock.nil)
    rcases hd with hd | hd
    · exact .consRevert (.requireRevert (safeTransferCondition_bad hout hne hd))
    · exact .consRevert (.requireFalse (safeTransferCondition_bool hout hne hd))
  · exact safeTransferTail_oversize hout (by omega)

theorem safeTransferTail_success {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool true)) (hb : out.size < 2 ^ 64)
    (hd : out.size = 0 ∨ config.externalABI.decodeValue? abiBool out = some (.bool true)) :
    ExecBlock config frame evm safeTransferTail (.ok frame evm) := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue
    ((safeTransferCap_eval hout).trans (by rw [decide_eq_true hb])))
  apply ExecBlock.consNormal (ExecStmt.iteFalse (safeTransferFailure_eval hz) ExecBlock.nil)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  by_cases hempty : out.size = 0
  · exact safeTransferCondition_empty hout hempty
  · exact safeTransferCondition_bool hout hempty (hd.resolve_left hempty)

end Benchmarks.Midnight
