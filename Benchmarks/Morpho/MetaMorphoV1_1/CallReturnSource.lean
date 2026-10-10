import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnMemory

/-! Source semantics of the optional reservation for raw return bytes. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def callReturnFrame (frame : Frame) (ptr : UInt256) (out : ByteArray) : Frame :=
  { frame with locals := if out.size = 0 then frame.locals else
      frame.locals.insert cursorName (uint256Value (bytesAllocPtr ptr out.size)) }

theorem callReturnFrame_cursor (frame : Frame) (ptr : UInt256) (out : ByteArray)
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr)) :
    (callReturnFrame frame ptr out).locals.get? cursorName =
      some (uint256Value (callReturnCursor ptr out)) := by
  unfold callReturnFrame callReturnCursor
  split
  · exact hptr
  · exact store_get_self _ _ _

theorem callReturnFrame_get (frame : Frame) (ptr : UInt256) (out : ByteArray)
    (name : Ident) (hne : (cursorName == name) = false) :
    (callReturnFrame frame ptr out).locals.get? name = frame.locals.get? name := by
  unfold callReturnFrame
  split
  · rfl
  · exact store_get_ne _ _ hne

theorem returnBytesLengthSource {cfg : Config} {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? cfg frame evm returnBytesLength = .ok (.int (Int.ofNat out.size)) := by
  simp only [returnBytesLength, evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure]

theorem returnBytesNonemptySource {cfg : Config} {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? cfg frame evm (.binary .ne returnBytesLength (.intLit 0)) =
      .ok (.bool (decide (out.size ≠ 0))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [returnBytesLengthSource hget, evalExpr?, bind, EvalResult.bind, pure]
  simp [evalBinaryOp?, BEq.beq]

theorem returnBytesBoundSource {cfg : Config} {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? cfg frame evm (.binary .lt returnBytesLength (.intLit (Int.ofNat (2 ^ 64)))) =
      .ok (.bool (decide (out.size < 2 ^ 64))) :=
  naturalLtSource (returnBytesLengthSource hget) (by simp only [evalExpr?, pure])

theorem returnBytesSizeSource {cfg : Config} {frame : Frame} {evm : State} {out : ByteArray}
    (hget : frame.locals.get? "returndata" = some (.bytes out)) (hsize : out.size < 2 ^ 64) :
    evalExpr? cfg frame evm (.binary .add (.intLit 32) returnBytesLength) =
      .ok (uint256Value (UInt256.ofNat (32 + out.size))) := by
  have hs : 32 + out.size < UInt256.size := by change _ < 2 ^ 256; omega
  simpa only [uint256Value, UInt256.toNat_ofNat_of_lt hs] using
    naturalAddSource (show evalExpr? cfg frame evm (.intLit 32) =
      .ok (.int (Int.ofNat 32)) by simp only [evalExpr?, pure]; rfl)
      (returnBytesLengthSource hget)

theorem reserveCallReturnReturns {cfg : Config} {frame : Frame} {evm : State}
    {ptr : UInt256} {out : ByteArray}
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hget : frame.locals.get? "returndata" = some (.bytes out))
    (hfit : callReturnFits ptr out) :
    ExecStmt cfg frame evm reserveCallReturn (.ok (callReturnFrame frame ptr out) evm) := by
  by_cases hz : out.size = 0
  · rw [callReturnFrame, if_pos hz]
    exact ExecStmt.iteFalse (by
      simpa only [hz, ne_eq, not_true_eq_false, decide_false] using returnBytesNonemptySource hget)
      ExecBlock.nil
  · obtain ⟨hsize, ha⟩ := hfit.resolve_left hz
    rw [callReturnFrame, if_neg hz]
    apply ExecStmt.iteTrue (by simpa only [hz, ne_eq, not_false_eq_true, decide_true] using
      returnBytesNonemptySource hget)
    apply ExecBlock.consNormal (ExecStmt.requireTrue (by
      simpa only [hsize, decide_true] using returnBytesBoundSource hget))
    have halloc := allocateCallReturns (cfg := cfg) (evm := evm) cursorName hlookup
      (show evalExpr? cfg frame evm (.var cursorName) = .ok (uint256Value ptr) by
        simp only [evalExpr?, hptr, EvalResult.ofOption]) (returnBytesSizeSource hget hsize) ha
    rw [nextCursor_bytesAlloc] at halloc
    exact ExecBlock.consNormal halloc ExecBlock.nil

theorem reserveCallReturnReverts {cfg : Config} {frame : Frame} {evm : State}
    {ptr : UInt256} {out : ByteArray}
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hget : frame.locals.get? "returndata" = some (.bytes out))
    (hbad : ¬ callReturnFits ptr out) : ExecStmt cfg frame evm reserveCallReturn .reverted := by
  have hz : out.size ≠ 0 := fun h ↦ hbad (.inl h)
  apply ExecStmt.iteTrue (by simpa only [hz, ne_eq, not_false_eq_true, decide_true] using
    returnBytesNonemptySource hget)
  by_cases hsize : out.size < 2 ^ 64
  · apply ExecBlock.consNormal (ExecStmt.requireTrue (by
      simpa only [hsize, decide_true] using returnBytesBoundSource hget))
    apply ExecBlock.consRevert
    exact allocateCallReverts cursorName hlookup
      (by simp only [evalExpr?, hptr, EvalResult.ofOption]) (returnBytesSizeSource hget hsize)
      (fun h ↦ hbad (.inr ⟨hsize, h⟩))
  · exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [hsize, decide_false] using returnBytesBoundSource hget))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
