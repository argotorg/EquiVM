import Benchmarks.CompoundIII.Comet.TransferBaseTailModel
import Benchmarks.CompoundIII.Comet.BorrowMinimumSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem transferBaseTail_source {v src balance evm result}
    (ht : TransferBaseTailTrace v src balance evm result) (frame : Frame) (dst : AccountAddress)
    (withdrawn supplied : UInt256) (hf : TransferBaseTailArgs frame v src dst balance withdrawn supplied)
    (hW : withdrawn.toNat < 2^104) (hS : supplied.toNat < 2^104)
    (hbound : -(2^255 : Int) < signedWord balance) :
    internalBlockResult config frame evm transferBaseTail result := by
  have he : evalExpr? config frame evm (.var "srcBalance") = .ok (.int (signedWord balance)) := by
    simp only [evalExpr?, hf.balance, EvalResult.ofOption]
  have hg : evalExpr? config frame evm (.binary .lt (.var "srcBalance") (.intLit 0)) =
      .ok (.bool (decide (signedWord balance < 0))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  have hmin hn := withdrawBaseBorrowMin_eval hf.immutables he hn hbound
  have hcall {r} (hc : CollateralCheckTrace v true src evm r) :=
    collateralCheck_call hc frame (.var "src") "__c11" hf.contract hf.immutables
      (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
  have hbool (value : Bool) (evm' : EVM.State) : evalExpr? config
      { frame with locals := frame.locals.insert "__c11" (.bool value) } evm' (.var "__c11") =
      .ok (.bool value) := by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  cases ht with
  | nonnegative hn =>
      obtain ⟨final, hev⟩ := transferBaseEvents_source frame evm src dst withdrawn supplied
        hf.contract hf.src hf.dst hf.withdrawn hf.supplied hf.index hW hS
      exact ⟨final, ExecBlock.consNormal
        (ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false (by omega)])) .nil) hev⟩
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
          (ExecBlock.consNormal (hcall hc)
            (ExecBlock.consRevert (ExecStmt.requireFalse (hbool false _))))))
  | @accepted evm' hn hm hc =>
      have hb : ExecBlock config frame evm transferBaseChecks
          (.ok { frame with locals := frame.locals.insert "__c11" (.bool true) } evm') :=
        ExecBlock.consNormal (ExecStmt.requireTrue ((hmin hn).trans (by rw [decide_eq_true hm])))
          (ExecBlock.consNormal (hcall hc)
            (ExecBlock.consNormal (ExecStmt.requireTrue (hbool true _)) .nil))
      have hf' := hf.insert "__c11" (.bool true) (by decide)
      obtain ⟨final, hev⟩ := transferBaseEvents_source _ evm' src dst withdrawn supplied
        hf'.contract hf'.src hf'.dst hf'.withdrawn hf'.supplied hf'.index hW hS
      exact ⟨final, ExecBlock.consNormal
        (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hn])) hb) hev⟩

end Benchmarks.CompoundIII.Comet
