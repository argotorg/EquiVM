import Benchmarks.CompoundIII.Comet.WithdrawBaseTransferSource
import Benchmarks.CompoundIII.Comet.BorrowMinimumSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem withdrawBaseTail_source {v src recipient amount balance evm result}
    (ht : WithdrawBaseTailTrace v src recipient amount balance evm result)
    (frame : Frame) (supplied : UInt256)
    (hf : WithdrawBaseArgs frame v src recipient amount supplied)
    (hsupplied : supplied.toNat < 2^104)
    (hbalance : frame.locals.get? "srcBalance" = some (.int (signedWord balance)))
    (hbound : -(2^255 : Int) < signedWord balance) :
    internalBlockResult config frame evm withdrawBaseTail result := by
  have he : evalExpr? config frame evm (.var "srcBalance") = .ok (.int (signedWord balance)) := by
    simp only [evalExpr?, hbalance, EvalResult.ofOption]
  have hg : evalExpr? config frame evm (.binary .lt (.var "srcBalance") (.intLit 0)) =
      .ok (.bool (decide (signedWord balance < 0))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  have hmin hn := withdrawBaseBorrowMin_eval hf.immutables he hn hbound
  have hcall {r} (hc : CollateralCheckTrace v true src evm r) :=
    collateralCheck_call hc frame (.var "src") "__c6" hf.contract hf.immutables
      (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
  have hbool (value : Bool) (evm' : EVM.State) : evalExpr? config
      { frame with locals := frame.locals.insert "__c6" (.bool value) } evm' (.var "__c6") =
      .ok (.bool value) := by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  cases ht with
  | nonnegative hn tail =>
    exact (withdrawBaseTransfer_source tail frame src supplied hf hsupplied).prepend
      (ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false (by omega)])) .nil)
  | tooSmall hn hm =>
    exact ExecBlock.consRevert (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hn]))
      (ExecBlock.consRevert (ExecStmt.requireFalse ((hmin hn).trans
        (by rw [decide_eq_false hm])))))
  | failed hn hm hc =>
    exact ExecBlock.consRevert (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hn]))
      (ExecBlock.consNormal (ExecStmt.requireTrue ((hmin hn).trans (by rw [decide_eq_true hm])))
        (ExecBlock.consRevert (hcall hc))))
  | rejected hn hm hc =>
    exact ExecBlock.consRevert (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hn]))
      (ExecBlock.consNormal (ExecStmt.requireTrue ((hmin hn).trans (by rw [decide_eq_true hm])))
        (ExecBlock.consNormal (hcall hc) (ExecBlock.consRevert
          (ExecStmt.requireFalse (hbool false _))))))
  | accepted hn hm hc tail =>
    have hb : ExecBlock config frame evm withdrawBaseChecks
        (.ok { frame with locals := frame.locals.insert "__c6" (.bool true) } _) :=
      ExecBlock.consNormal (ExecStmt.requireTrue ((hmin hn).trans (by rw [decide_eq_true hm])))
        (ExecBlock.consNormal (hcall hc)
          (ExecBlock.consNormal (ExecStmt.requireTrue (hbool true _)) .nil))
    exact (withdrawBaseTransfer_source tail _ src supplied
      (hf.insert "__c6" (.bool true) (by decide)) hsupplied).prepend
        (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hn])) hb)

end Benchmarks.CompoundIII.Comet
