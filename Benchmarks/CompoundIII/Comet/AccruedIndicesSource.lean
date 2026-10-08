import Benchmarks.CompoundIII.Comet.AccruedIndicesModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem accruedIndicesThen_result (v : CometWithExtendedAssetListImmutables)
    (elapsed : UInt256) (evm : EVM.State) (ht : elapsed.toNat < 2^40) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    ExecBlock config (accruedIndicesInitialFrame v w0 elapsed) evm accruedIndicesThen
      (if AccruedWorkValid v w0 w1 elapsed then
        .ok (accruedIndicesUpdatedFrame v w0 w1 elapsed) evm else .reverted) := by
  dsimp only
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let u := utilizationWord w0 w1
  let f0 := accruedIndicesInitialFrame v w0 elapsed
  let f1 : Frame := { f0 with locals := f0.locals.insert "utilization" (.int u.toNat) }
  let f2 : Frame := { f1 with locals := f1.locals.insert "supplyRate" (.int (accruedRate v w0 w1 false).toNat) }
  let f3 := accruedIndicesRatesFrame v w0 w1 elapsed
  change ExecBlock config f0 evm _
    (if AccruedWorkValid v w0 w1 elapsed then
      .ok (accruedIndicesUpdatedFrame v w0 w1 elapsed) evm else .reverted)
  apply ExecBlock.consNormal (utilization_call f0 evm "utilization" rfl)
  have hu : evalExpr? config f1 evm (.var "utilization") = .ok (.int u.toNat) := by
    simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  by_cases hs : RateValid (rateParams v false) (utilizationWord w0 w1)
  · apply ExecBlock.consNormal (rate_call_ok v false f1 evm u _ "supplyRate" rfl rfl hu hs)
    have hu' : evalExpr? config f2 evm (.var "utilization") = .ok (.int u.toNat) := by
      simp only [evalExpr?, f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    by_cases hb : RateValid (rateParams v true) (utilizationWord w0 w1)
    · apply ExecBlock.consNormal (rate_call_ok v true f2 evm u _ "borrowRate" rfl rfl hu' hb)
      have hsi := indexAccrualBlock_result f3 evm false (totalsIndexWord w0 false)
        (accruedRate v w0 w1 false) elapsed rfl
        (by simp only [f3, accruedIndicesRatesFrame, accruedIndicesInitialFrame,
          accruedIndicesEntry, indexLocalName, indexRateName, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
        (by simp only [f3, accruedIndicesRatesFrame, accruedIndicesInitialFrame,
          accruedIndicesEntry, indexLocalName, indexRateName, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
        (by simp only [f3, accruedIndicesRatesFrame, accruedIndicesInitialFrame,
          accruedIndicesEntry, indexLocalName, indexRateName, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl) (totalsIndexWord_lt _ _) (rateWord_lt hs) ht
      by_cases hsf : IndexAccrualValid (totalsIndexWord w0 false)
          (accruedRate v w0 w1 false) elapsed
      · rw [if_pos hsf] at hsi
        let f4 := indexAccrualFrame f3 false (totalsIndexWord w0 false)
          (accruedRate v w0 w1 false) elapsed
        have hbi := indexAccrualBlock_result f4 evm true (totalsIndexWord w0 true)
          (accruedRate v w0 w1 true) elapsed rfl
            (by simp only [f4, f3, indexAccrualFrame, accruedIndicesRatesFrame,
            accruedIndicesInitialFrame, accruedIndicesEntry, indexLocalName, indexRateName,
            indexMulName, indexSafeName, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert]; rfl)
          (by simp only [f4, f3, indexAccrualFrame, accruedIndicesRatesFrame,
            accruedIndicesInitialFrame, accruedIndicesEntry, indexLocalName, indexRateName,
            indexMulName, indexSafeName, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert]; rfl)
          (by simp only [f4, f3, indexAccrualFrame, accruedIndicesRatesFrame,
            accruedIndicesInitialFrame, accruedIndicesEntry, indexLocalName, indexRateName,
            indexMulName, indexSafeName, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert]; rfl) (totalsIndexWord_lt _ _) (rateWord_lt hb) ht
        by_cases hbf : IndexAccrualValid (totalsIndexWord w0 true)
            (accruedRate v w0 w1 true) elapsed
        · rw [if_pos hbf] at hbi
          rw [if_pos (show AccruedWorkValid v w0 w1 elapsed from ⟨hs, hb, hsf, hbf⟩)]
          exact execBlockAppendOk hsi hbi
        · rw [if_neg hbf] at hbi
          rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun h ↦ hbf h.2.2.2)]
          exact execBlockAppendOk hsi hbi
      · rw [if_neg hsf] at hsi
        rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun h ↦ hsf h.2.2.1)]
        exact execBlockAppendReverted hsi
    · rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun h ↦ hb h.2.1)]
      exact ExecBlock.consRevert (rate_call_revert v true f2 evm u _ "borrowRate" rfl rfl hu' hb)
  · rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun h ↦ hs h.1)]
    exact ExecBlock.consRevert (rate_call_revert v false f1 evm u _ "supplyRate" rfl rfl hu hs)

theorem accruedIndicesFinalFrame_get (v : CometWithExtendedAssetListImmutables)
    (w0 w1 elapsed : UInt256) (borrow : Bool) :
    (accruedIndicesFinalFrame v w0 w1 elapsed).locals.get? (indexLocalName borrow) =
      some (.int (accruedIndex v w0 w1 elapsed borrow).toNat) := by
  by_cases hz : elapsed = ⟨0⟩ <;>
    simp only [accruedIndicesFinalFrame, accruedIndex, hz, if_true, if_false] <;>
    cases borrow <;>
      simp only [accruedIndicesInitialFrame, accruedIndicesUpdatedFrame, indexAccrualFrame,
        indexLocalName, indexMulName, indexSafeName, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] <;> rfl

theorem accruedIndicesCallable_block (v : CometWithExtendedAssetListImmutables)
    (elapsed : UInt256) (evm : EVM.State) (ht : elapsed.toNat < 2^40) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    ExecBlock config (accruedIndicesEntry v elapsed) evm accruedIndicesCallable.body
      (if AccruedIndicesValid v w0 w1 elapsed then
        .returned (accruedIndicesFinalFrame v w0 w1 elapsed) evm
          (some [.int (accruedIndex v w0 w1 elapsed false).toNat,
            .int (accruedIndex v w0 w1 elapsed true).toNat]) else .reverted) := by
  dsimp only
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let f0 := accruedIndicesEntry v elapsed
  let f1 : Frame := { f0 with locals := f0.locals.insert "baseSupplyIndex_" (.int (totalsIndexWord w0 false).toNat) }
  let f2 := accruedIndicesInitialFrame v w0 elapsed
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (evalTotalsIndex evm f0.locals (immStore v) false (by simp [f0, accruedIndicesEntry, totalsIndexName])))
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (evalTotalsIndex evm f1.locals (immStore v) true (by simp [f1, f0, accruedIndicesEntry, totalsIndexName,
      Std.HashMap.getElem?_insert])))
  have he : evalExpr? config f2 evm (.var "timeElapsed") = .ok (.int (Int.ofNat elapsed.toNat)) := by
    simp only [evalExpr?, f2, accruedIndicesInitialFrame, accruedIndicesEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hcond : evalExpr? config f2 evm (.binary .gt (.var "timeElapsed") (.intLit 0)) =
      .ok (.bool (decide (0 < elapsed.toNat))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
    simp
  have hret : ExecBlock config (accruedIndicesFinalFrame v w0 w1 elapsed) evm
      [.return [.var "baseSupplyIndex_", .var "baseBorrowIndex_"]]
      (.returned (accruedIndicesFinalFrame v w0 w1 elapsed) evm
        (some [.int (accruedIndex v w0 w1 elapsed false).toNat,
          .int (accruedIndex v w0 w1 elapsed true).toNat])) := by
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    have hs := accruedIndicesFinalFrame_get v w0 w1 elapsed false
    have hb := accruedIndicesFinalFrame_get v w0 w1 elapsed true
    simp only [indexLocalName, Bool.false_eq_true, if_false, if_true] at hs hb
    simp only [evalExprs?, evalExpr?, hs, hb, EvalResult.ofOption, pure, bind, EvalResult.bind]
  change ExecBlock config f2 evm _ (if AccruedIndicesValid v w0 w1 elapsed then _ else _)
  by_cases hz : elapsed = ⟨0⟩
  · simp only [AccruedIndicesValid, if_pos hz, if_true]
    have hfalse := hcond.trans (show _ = .ok (.bool false) by rw [hz]; rfl)
    apply ExecBlock.consNormal (ExecStmt.iteFalse hfalse ExecBlock.nil)
    simpa only [accruedIndicesFinalFrame, if_pos hz] using hret
  · have hpos : 0 < elapsed.toNat := by
      by_contra h
      apply hz
      exact u256_inj (by change elapsed.toNat = 0; omega)
    have htcond := hcond.trans (by rw [decide_eq_true hpos])
    have hb := accruedIndicesThen_result v elapsed evm ht
    change ExecBlock config f2 evm accruedIndicesThen
      (if AccruedWorkValid v w0 w1 elapsed then
        .ok (accruedIndicesUpdatedFrame v w0 w1 elapsed) evm else .reverted) at hb
    by_cases hv : AccruedWorkValid v w0 w1 elapsed
    · rw [if_pos hv] at hb
      simp only [AccruedIndicesValid, if_neg hz, if_pos hv]
      apply ExecBlock.consNormal (ExecStmt.iteTrue htcond hb)
      simpa only [accruedIndicesFinalFrame, if_neg hz] using hret
    · rw [if_neg hv] at hb
      simp only [AccruedIndicesValid, if_neg hz, if_neg hv]
      exact ExecBlock.consRevert (ExecStmt.iteTrue htcond hb)

theorem accruedIndices_call_ok (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (elapsed : UInt256) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.int elapsed.toNat))
    (ht : elapsed.toNat < 2^40)
    (hv : AccruedIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) elapsed) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    ExecStmt config frame evm (.internalCall "accruedInterestIndices" [expr] ret)
      (.ok { frame with
        locals := frame.locals.insert ret (.tuple
          [.int (accruedIndex v w0 w1 elapsed false).toNat,
            .int (accruedIndex v w0 w1 elapsed true).toNat]) } evm) := by
  have hb := accruedIndicesCallable_block v elapsed evm ht
  dsimp only at hb ⊢
  rw [if_pos hv] at hb
  have hf := ExecFuncBody.execBlockRet hb
  exact ExecStmt.internalCallReturn (callee := accruedIndicesCallable)
    (locals := (∅ : Store).insert "timeElapsed" (.int elapsed.toNat))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr])
    (argVals := [.int elapsed.toNat])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact accruedIndicesCallable_lookup) rfl
    (by simpa only [hc, hi] using hf)

theorem accruedIndices_call_revert (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (elapsed : UInt256) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.int elapsed.toNat))
    (ht : elapsed.toNat < 2^40)
    (hv : ¬ AccruedIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) elapsed) :
    ExecStmt config frame evm (.internalCall "accruedInterestIndices" [expr] ret) .reverted := by
  have hb := accruedIndicesCallable_block v elapsed evm ht
  dsimp only at hb
  rw [if_neg hv] at hb
  apply ExecStmt.internalCallRevert (callee := accruedIndicesCallable)
    (locals := (∅ : Store).insert "timeElapsed" (.int elapsed.toNat))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr])
    (argVals := [.int elapsed.toNat])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hc]; exact accruedIndicesCallable_lookup) rfl
  apply ExecFuncBody.execBlockRevert
  simpa only [hc, hi] using hb

end Benchmarks.CompoundIII.Comet
