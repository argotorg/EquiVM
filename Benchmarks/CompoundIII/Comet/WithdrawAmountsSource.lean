import Benchmarks.CompoundIII.Comet.WithdrawAmountsModel
import Benchmarks.CompoundIII.Comet.PrincipalDifferenceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- Keep the packed-field decoder abstract when splitting source-level signed comparisons.
attribute [local irreducible] signed104

theorem withdrawAmountsDiff_source {cfg frame evm old next}
    (ho : evalExpr? cfg frame evm (.var "oldPrincipal") = .ok (.int (signed104 old)))
    (hn : evalExpr? cfg frame evm (.var "newPrincipal") = .ok (.int (signed104 next)))
    (hle : signed104 next ≤ signed104 old) :
    if signed104 old - signed104 next < (2^103 : Int) then
      evalExpr? cfg frame evm withdrawAmountsDiffExpr =
        .ok (.int (principalDecrease old next).toNat)
    else evalExpr? cfg frame evm withdrawAmountsDiffExpr = .revert := by
  exact principalDifference_source ho hn hle

theorem withdrawAmounts_source (evm : EVM.State) (imms : Store) (old next : UInt256) :
    if WithdrawAmountsFits old next then
      ExecFuncBody config (withdrawAmountsEntry imms old next) evm withdrawAmountsCallable.body
        (.returned (withdrawAmountsEntry imms old next) evm
          (some [.int (withdrawSupplyAmount old next).toNat,
            .int (withdrawBorrowAmount old next).toNat]))
    else ExecFuncBody config (withdrawAmountsEntry imms old next) evm
      withdrawAmountsCallable.body .reverted := by
  let frame := withdrawAmountsEntry imms old next
  have ho : evalExpr? config frame evm (.var "oldPrincipal") = .ok (.int (signed104 old)) := by
    simp only [evalExpr?, frame, withdrawAmountsEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hn : evalExpr? config frame evm (.var "newPrincipal") = .ok (.int (signed104 next)) := by
    simp only [evalExpr?, frame, withdrawAmountsEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hg : evalExpr? config frame evm (.binary .gt (.var "newPrincipal")
      (.var "oldPrincipal")) = .ok (.bool (decide (signed104 old < signed104 next))) := by
    simp only [evalExpr?, ho, hn, bind, EvalResult.bind, evalBinaryOp?]
  have hgN : evalExpr? config frame evm (.binary .ge (.var "newPrincipal") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ signed104 next))) := by
    simp only [evalExpr?, hn, pure, bind, EvalResult.bind, evalBinaryOp?]
  have hgO : evalExpr? config frame evm (.binary .le (.var "oldPrincipal") (.intLit 0)) =
      .ok (.bool (decide (signed104 old ≤ 0))) := by
    simp only [evalExpr?, ho, pure, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hinc : signed104 old < signed104 next
  · simp only [WithdrawAmountsFits, withdrawSupplyAmount, withdrawBorrowAmount, if_pos hinc]
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consReturn (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hinc])) ?_)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, pure, bind, EvalResult.bind]; rfl
  · have hle : signed104 next ≤ signed104 old := by omega
    have hi := ExecStmt.iteFalse (cfg := config) (thenB := [.return [.intLit 0, .intLit 0]])
      (hg.trans (by rw [decide_eq_false hinc])) (ExecBlock.nil (solm := frame) (evm := evm))
    have hd := withdrawAmountsDiff_source ho hn hle
    by_cases hp : 0 ≤ signed104 next
    · simp only [WithdrawAmountsFits, withdrawSupplyAmount, withdrawBorrowAmount,
        if_neg hinc, if_pos hp]
      split_ifs with hf
      · rw [if_pos hf] at hd
        apply ExecFuncBody.execBlockRet
        apply ExecBlock.consNormal hi
        apply ExecBlock.consReturn (ExecStmt.iteTrue (hgN.trans (by rw [decide_eq_true hp])) ?_)
        apply ExecBlock.consReturn (ExecStmt.return ?_)
        simp only [evalExprs?, hd, evalExpr?, pure, bind, EvalResult.bind]
        rfl
      · rw [if_neg hf] at hd
        apply ExecFuncBody.execBlockRevert
        apply ExecBlock.consNormal hi
        apply ExecBlock.consRevert (ExecStmt.iteTrue (hgN.trans (by rw [decide_eq_true hp])) ?_)
        apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
        simp only [evalExprs?, hd, bind, EvalResult.bind]
    · by_cases ho0 : signed104 old ≤ 0
      · simp only [WithdrawAmountsFits, withdrawSupplyAmount, withdrawBorrowAmount,
          if_neg hinc, if_neg hp, if_pos ho0]
        split_ifs with hf
        · rw [if_pos hf] at hd
          apply ExecFuncBody.execBlockRet
          apply ExecBlock.consNormal hi
          apply ExecBlock.consReturn (ExecStmt.iteFalse
            (hgN.trans (by rw [decide_eq_false hp])) ?_)
          apply ExecBlock.consReturn (ExecStmt.iteTrue
            (hgO.trans (by rw [decide_eq_true ho0])) ?_)
          apply ExecBlock.consReturn (ExecStmt.return ?_)
          simp only [evalExprs?, hd, evalExpr?, pure, bind, EvalResult.bind]
          rfl
        · rw [if_neg hf] at hd
          apply ExecFuncBody.execBlockRevert
          apply ExecBlock.consNormal hi
          apply ExecBlock.consRevert (ExecStmt.iteFalse
            (hgN.trans (by rw [decide_eq_false hp])) ?_)
          apply ExecBlock.consRevert (ExecStmt.iteTrue
            (hgO.trans (by rw [decide_eq_true ho0])) ?_)
          apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
          simp only [evalExprs?, hd, evalExpr?, pure, bind, EvalResult.bind]
      · have ho' := ho
        rw [← positivePrincipal_int (by omega : 0 ≤ signed104 old)] at ho'
        have hc := castUintSourceOk ⟨104, by decide⟩ ho'
          (lt_trans (positivePrincipal_lt old) (by decide))
        simp only [WithdrawAmountsFits, withdrawSupplyAmount, withdrawBorrowAmount,
          if_neg hinc, if_neg hp, if_neg ho0]
        split_ifs with hf
        · have he := checkedPrincipalNegSource hn (by omega) hf
          have he' := castUintSourceOk ⟨104, by decide⟩ he
            (lt_trans (negativePrincipal_lt hf) (by decide))
          apply ExecFuncBody.execBlockRet
          apply ExecBlock.consNormal hi
          apply ExecBlock.consReturn (ExecStmt.iteFalse
            (hgN.trans (by rw [decide_eq_false hp])) ?_)
          apply ExecBlock.consReturn (ExecStmt.iteFalse
            (hgO.trans (by rw [decide_eq_false ho0])) ?_)
          apply ExecBlock.consReturn (ExecStmt.return ?_)
          simp only [evalExprs?, hc, he', pure, bind, EvalResult.bind]
          rfl
        · have hmin : signed104 next = -(2^103 : Int) := by
            have hb := signed104_bounds next; omega
          have he := checkedPrincipalNegSource_revert hn hmin
          apply ExecFuncBody.execBlockRevert
          apply ExecBlock.consNormal hi
          apply ExecBlock.consRevert (ExecStmt.iteFalse
            (hgN.trans (by rw [decide_eq_false hp])) ?_)
          apply ExecBlock.consRevert (ExecStmt.iteFalse
            (hgO.trans (by rw [decide_eq_false ho0])) ?_)
          apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
          simp only [evalExprs?, hc, evalExpr?, he, pure, bind, EvalResult.bind]

theorem withdrawAmounts_call (frame : Frame) (evm : EVM.State) (old next : UInt256)
    (oldExpr nextExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (ho : evalExpr? config frame evm oldExpr = .ok (.int (signed104 old)))
    (hn : evalExpr? config frame evm nextExpr = .ok (.int (signed104 next))) :
    ExecStmt config frame evm (.internalCall "withdrawAndBorrowAmount" [oldExpr, nextExpr] ret)
      (if WithdrawAmountsFits old next then
        .ok { frame with
          locals := frame.locals.insert ret
            (.tuple [.int (withdrawSupplyAmount old next).toNat,
              .int (withdrawBorrowAmount old next).toNat]) } evm
      else .reverted) := by
  have hb := withdrawAmounts_source evm frame.immutables old next
  have he : evalExprs? config frame evm [oldExpr, nextExpr] =
      .ok [.int (signed104 old), .int (signed104 next)] := by
    simp only [evalExprs?, ho, hn, pure, bind, EvalResult.bind]
  split_ifs with hf
  · rw [if_pos hf] at hb
    exact ExecStmt.internalCallReturn (callee := withdrawAmountsCallable)
      (locals := (withdrawAmountsEntry frame.immutables old next).locals) he
      (by rw [hc]; exact withdrawAmountsCallable_lookup) rfl (by simpa only [hc] using hb)
  · rw [if_neg hf] at hb
    exact ExecStmt.internalCallRevert (callee := withdrawAmountsCallable)
      (locals := (withdrawAmountsEntry frame.immutables old next).locals) he
      (by rw [hc]; exact withdrawAmountsCallable_lookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
