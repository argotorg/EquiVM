import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnSource
import Reasoning.ABIComposite

/-! SafeERC20 accepts an empty result or the canonical ABI Boolean true. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def optionalReturnValid (out : ByteArray) : Prop :=
  out.size = 0 ∨ (32 ≤ out.size ∧ calldataWord out 0 = ⟨1⟩)

instance (out : ByteArray) : Decidable (optionalReturnValid out) :=
  inferInstanceAs (Decidable (_ ∨ _))

def optionalReturnGuard : Expr :=
  .unary .not (.binary .and (.binary .ne returnBytesLength (.intLit 0))
    (.unary .not (.abiDecode abiBool (.var "returndata"))))

theorem returnBoolSource {frame : Frame} {evm : State} {out : ByteArray} {flag : Bool}
    (hget : frame.locals.get? "returndata" = some (.bytes out))
    (hdecode : decodeReturnValue? abiBool out = some (.bool flag)) :
    evalExpr? config frame evm (.abiDecode abiBool (.var "returndata")) =
      .ok (.bool flag) := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, EvalResult.bind]
  change (match decodeReturnValue? abiBool out with
    | some value => EvalResult.ok value | none => EvalResult.revert) = _
  rw [hdecode]

theorem returnBoolSourceRevert {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? "returndata" = some (.bytes out))
    (hdecode : decodeReturnValue? abiBool out = none) :
    evalExpr? config frame evm (.abiDecode abiBool (.var "returndata")) = .revert := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, EvalResult.bind]
  change (match decodeReturnValue? abiBool out with
    | some value => EvalResult.ok value | none => EvalResult.revert) = _
  rw [hdecode]

theorem optionalReturnSourcePasses {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? "returndata" = some (.bytes out))
    (hsize : out.size < 2 ^ 255) (hvalid : optionalReturnValid out) :
    ExecStmt config frame evm (.require optionalReturnGuard) (.ok frame evm) := by
  apply ExecStmt.requireTrue
  have hc := returnBytesNonemptySource (cfg := config) (evm := evm) hget
  by_cases hz : out.size = 0
  · simp only [hz, ne_eq, not_true_eq_false, decide_false] at hc
    simp only [optionalReturnGuard, evalExpr?, hc, bind, EvalResult.bind, evalUnaryOp?,
      EvalResult.ofOption, pure, Bool.not_false, Bool.not_true]
  · obtain ⟨hl, hw⟩ := hvalid.resolve_left hz
    have hd : decodeReturnValue? abiBool out = some (.bool true) := by
      rw [decodeReturnBool_long hl hsize, hw]
      decide
    have he := returnBoolSource (evm := evm) hget hd
    simp only [hz, ne_eq, not_false_eq_true, decide_true] at hc
    simp only [optionalReturnGuard, evalExpr?, hc, he, bind, EvalResult.bind, evalUnaryOp?,
      EvalResult.ofOption, pure, Bool.not_false, Bool.not_true]

theorem optionalReturnSourceReverts {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? "returndata" = some (.bytes out))
    (hsize : out.size < 2 ^ 255) (hbad : ¬ optionalReturnValid out) :
    ExecStmt config frame evm (.require optionalReturnGuard) .reverted := by
  have hz : out.size ≠ 0 := fun h ↦ hbad (.inl h)
  have hc := returnBytesNonemptySource (cfg := config) (evm := evm) hget
  simp only [hz, ne_eq, not_false_eq_true, decide_true] at hc
  by_cases hv : BoolReturnValid out
  · have hw : calldataWord out 0 = ⟨0⟩ := hv.2.resolve_right (fun h ↦ hbad (.inr ⟨hv.1, h⟩))
    have hd : decodeReturnValue? abiBool out = some (.bool false) := by
      rw [decodeReturnBool_long hv.1 hsize, if_pos hw]
    have he := returnBoolSource (evm := evm) hget hd
    apply ExecStmt.requireFalse
    simp only [optionalReturnGuard, evalExpr?, hc, he, bind, EvalResult.bind, evalUnaryOp?,
      EvalResult.ofOption, pure, Bool.not_false, Bool.not_true]
  · have he := returnBoolSourceRevert (evm := evm) hget (decodeReturnBool_invalid hv hsize)
    apply ExecStmt.requireRevert
    simp only [optionalReturnGuard, evalExpr?, hc, he, bind, EvalResult.bind]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
