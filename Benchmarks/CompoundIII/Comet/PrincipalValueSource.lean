import Benchmarks.CompoundIII.Comet.PrincipalValueModel
import Benchmarks.CompoundIII.Comet.PrincipalMagnitudeSource
import Benchmarks.CompoundIII.Comet.Signed104Source
import Benchmarks.CompoundIII.Comet.SignedNegation
import Benchmarks.CompoundIII.Comet.AccountMagnitude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem principalValueAmount_source {cfg frame evm present}
    (borrow : Bool) (he : evalExpr? cfg frame evm (.var "presentValue_") =
      .ok (.int (signedWord present))) (hmin : -(2^255 : Int) < signedWord present)
    (hsign : if borrow then signedWord present < 0 else 0 ≤ signedWord present) :
    evalExpr? cfg frame evm (principalValueAmountExpr borrow) =
      .ok (.int (principalValueAmount present borrow).toNat) := by
  cases borrow
  · rw [signedWord_low ((signedWord_nonneg_iff present).mp hsign)] at he
    exact castUintSourceOk ⟨256, by decide⟩ he present.val.isLt
  · have hn : evalExpr? cfg frame evm (.binary .sub (.intLit 0) (.var "presentValue_")) =
        .ok (.int (-signedWord present)) := by
      simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, zero_sub]
    have hb := signedWord_bounds present
    have hn' := signedRangeSourceOk hn (by omega) (by omega)
    rw [← signedWord_negativeMagnitude (le_of_lt hsign)] at hn'
    exact castUintSourceOk ⟨256, by decide⟩ hn' (UInt256.sub (UInt256.ofNat 0) present).val.isLt

theorem principalValueReturn_source {cfg frame evm} (borrow : Bool) (value : UInt256)
    (hv : value.toNat < 2^103)
    (he : evalExpr? cfg frame evm (.var (if borrow then "__c3" else "__c1")) =
      .ok (.int value.toNat)) :
    evalExpr? cfg frame evm (principalValueReturnExpr borrow) =
      .ok (.int (if borrow then -Int.ofNat value.toNat else Int.ofNat value.toNat)) := by
  cases borrow
  · exact he
  · change evalExpr? cfg frame evm (.var "__c3") = .ok (.int value.toNat) at he
    have hl : ¬ -(value.toNat : Int) < -(2^103 : Int) := by omega
    have hh : ¬ -(value.toNat : Int) ≥ (2^103 : Int) := by omega
    simp only [principalValueReturnExpr, if_true, evalExpr?, he, pure, bind, EvalResult.bind,
      evalBinaryOp?, hl, hh, decide_false, Bool.or_self, Bool.false_eq_true, if_false, zero_sub]
    rfl

theorem principalValueBranch_source (evm : EVM.State) (imms : Store) (present : UInt256)
    (borrow : Bool) (hmin : -(2^255 : Int) < signedWord present)
    (hsign : if borrow then signedWord present < 0 else 0 ≤ signedWord present) :
    if PrincipalValueBranchFits evm present borrow then
      ∃ final, ExecBlock config (principalValueEntry imms present) evm (principalValueBranch borrow)
        (.returned final evm (some [.int (if borrow then
          -Int.ofNat (principalValueMagnitude evm present borrow).toNat
          else Int.ofNat (principalValueMagnitude evm present borrow).toNat)]))
    else ExecBlock config (principalValueEntry imms present) evm (principalValueBranch borrow)
      .reverted := by
  let frame := principalValueEntry imms present
  let index := principalValueIndex evm borrow
  let amount := principalValueAmount present borrow
  let value := principalValueMagnitude evm present borrow
  have he : evalExpr? config frame evm (.var "presentValue_") = .ok (.int (signedWord present)) := by
    simp only [evalExpr?, frame, principalValueEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have ha := principalValueAmount_source borrow he hmin hsign
  have hi : evalExpr? config frame evm (.storage ⟨totalsIndexName borrow, []⟩) =
      .ok (.int index.toNat) := evalTotalsIndex evm frame.locals imms borrow (by
        cases borrow <;> simp only [frame, principalValueEntry, totalsIndexName,
          Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] <;> rfl)
  have hc := principalMagnitude_call borrow frame evm index amount _ _
    (if borrow then "__c2" else "__c0") rfl hi ha
  by_cases hm : PrincipalMagnitudeFits borrow index amount
  · rw [if_pos hm] at hc
    let f1 : Frame := { frame with
      locals := frame.locals.insert (if borrow then "__c2" else "__c0") (.int value.toNat) }
    have hv : evalExpr? config f1 evm (.var (if borrow then "__c2" else "__c0")) =
        .ok (.int value.toNat) := by
      simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, if_true, EvalResult.ofOption]
    have hs := signed104_call f1 evm value _ (if borrow then "__c3" else "__c1") rfl hv
    by_cases hval : value.toNat < 2^103
    · rw [if_pos hval] at hs
      rw [if_pos ⟨hm, hval⟩]
      let f2 : Frame := { f1 with
        locals := f1.locals.insert (if borrow then "__c3" else "__c1") (.int value.toNat) }
      refine ⟨f2, ExecBlock.consNormal hc (ExecBlock.consNormal hs ?_)⟩
      apply ABlock.start.returns
      apply principalValueReturn_source borrow value hval
      simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, if_true, EvalResult.ofOption]
    · rw [if_neg hval] at hs
      rw [if_neg (fun h ↦ hval h.2)]
      exact ExecBlock.consNormal hc (ExecBlock.consRevert hs)
  · rw [if_neg hm] at hc
    rw [if_neg (fun h ↦ hm h.1)]
    exact ExecBlock.consRevert hc

theorem principalValue_min_source (evm : EVM.State) (imms : Store) (present : UInt256)
    (hmin : ¬ -(2^255 : Int) < signedWord present) :
    ExecFuncBody config (principalValueEntry imms present) evm principalValueCallable.body
      .reverted := by
  let frame := principalValueEntry imms present
  have he : evalExpr? config frame evm (.var "presentValue_") = .ok (.int (signedWord present)) := by
    simp only [evalExpr?, frame, principalValueEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hg : evalExpr? config frame evm (.binary .ge (.var "presentValue_") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ signedWord present))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  have hb := signedWord_bounds present
  have hpos : ¬ 0 ≤ signedWord present := by omega
  have hn : evalExpr? config frame evm (.binary .sub (.intLit 0) (.var "presentValue_")) =
      .ok (.int (-signedWord present)) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, zero_sub]
  have hn' := signedRangeSourceOverflow hn (by omega)
  have ha : evalExpr? config frame evm (principalValueAmountExpr true) = .revert := by
    simp only [principalValueAmountExpr, if_true, evalExpr?, hn', bind, EvalResult.bind]
  have hi : evalExpr? config frame evm (.storage ⟨totalsIndexName true, []⟩) =
      .ok (.int (principalValueIndex evm true).toNat) :=
    evalTotalsIndex evm frame.locals imms true (by
      simp only [frame, principalValueEntry, totalsIndexName, if_true,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hpos])) ?_)
  apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
  change evalExprs? config frame evm
    [.storage ⟨totalsIndexName true, []⟩, principalValueAmountExpr true] = .revert
  simp only [evalExprs?, hi, ha, bind, EvalResult.bind]

theorem principalValue_source_ok (evm : EVM.State) (imms : Store) (present : UInt256)
    (hf : PrincipalValueFits evm present) :
    ∃ final, ExecFuncBody config (principalValueEntry imms present) evm principalValueCallable.body
      (.returned final evm (some [.int (principalValueInt evm present)])) := by
  let frame := principalValueEntry imms present
  have he : evalExpr? config frame evm (.var "presentValue_") = .ok (.int (signedWord present)) := by
    simp only [evalExpr?, frame, principalValueEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hg : evalExpr? config frame evm (.binary .ge (.var "presentValue_") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ signedWord present))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hpos : 0 ≤ signedWord present
  · have hneg : ¬ signedWord present < 0 := by omega
    have hb := principalValueBranch_source evm imms present false hf.1 hpos
    have hbranch : PrincipalValueBranchFits evm present false := by
      simpa only [decide_eq_false hneg] using hf.2
    rw [if_pos hbranch] at hb
    obtain ⟨final, hb⟩ := hb
    simp only [Bool.false_eq_true, if_false] at hb
    rw [principalValueInt, if_pos hpos]
    exact ⟨final, ExecFuncBody.execBlockRet (ExecBlock.consReturn
      (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hpos])) hb))⟩
  · have hneg : signedWord present < 0 := by omega
    have hb := principalValueBranch_source evm imms present true hf.1 hneg
    have hbranch : PrincipalValueBranchFits evm present true := by
      simpa only [decide_eq_true hneg] using hf.2
    rw [if_pos hbranch] at hb
    obtain ⟨final, hb⟩ := hb
    simp only [if_true] at hb
    rw [principalValueInt, if_neg hpos]
    exact ⟨final, ExecFuncBody.execBlockRet (ExecBlock.consReturn
      (ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hpos])) hb))⟩

theorem principalValue_source_revert (evm : EVM.State) (imms : Store) (present : UInt256)
    (hf : ¬ PrincipalValueFits evm present) :
    ExecFuncBody config (principalValueEntry imms present) evm principalValueCallable.body
      .reverted := by
  let frame := principalValueEntry imms present
  have he : evalExpr? config frame evm (.var "presentValue_") = .ok (.int (signedWord present)) := by
    simp only [evalExpr?, frame, principalValueEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hg : evalExpr? config frame evm (.binary .ge (.var "presentValue_") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ signedWord present))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hmin : -(2^255 : Int) < signedWord present
  · by_cases hpos : 0 ≤ signedWord present
    · have hneg : ¬ signedWord present < 0 := by omega
      have hb := principalValueBranch_source evm imms present false hmin hpos
      have hbranch : ¬ PrincipalValueBranchFits evm present false := by
        intro hb; apply hf; exact ⟨hmin, by simpa only [decide_eq_false hneg] using hb⟩
      rw [if_neg hbranch] at hb
      exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hpos])) hb))
    · have hneg : signedWord present < 0 := by omega
      have hb := principalValueBranch_source evm imms present true hmin hneg
      have hbranch : ¬ PrincipalValueBranchFits evm present true := by
        intro hb; apply hf; exact ⟨hmin, by simpa only [decide_eq_true hneg] using hb⟩
      rw [if_neg hbranch] at hb
      exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hpos])) hb))
  · exact principalValue_min_source evm imms present hmin

theorem principalValue_source (evm : EVM.State) (imms : Store) (present : UInt256) :
    if PrincipalValueFits evm present then
      ∃ final, ExecFuncBody config (principalValueEntry imms present) evm principalValueCallable.body
        (.returned final evm (some [.int (principalValueInt evm present)]))
    else ExecFuncBody config (principalValueEntry imms present) evm principalValueCallable.body
      .reverted := by
  split_ifs with hf
  · exact principalValue_source_ok evm imms present hf
  · exact principalValue_source_revert evm imms present hf

theorem principalValue_call (frame : Frame) (evm : EVM.State) (present : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int (signedWord present))) :
    ExecStmt config frame evm (.internalCall "principalValue" [expr] ret)
      (if PrincipalValueFits evm present then
        .ok { frame with locals := frame.locals.insert ret (.int (principalValueInt evm present)) } evm
      else .reverted) := by
  have hb := principalValue_source evm frame.immutables present
  split_ifs with hf
  · rw [if_pos hf] at hb
    obtain ⟨final, hb⟩ := hb
    exact ExecStmt.internalCallReturn (cfg := config) (solm := frame) (evm := evm)
      (args := [expr]) (callee := principalValueCallable)
      (locals := (principalValueEntry frame.immutables present).locals)
      (evalExprs?_singleton he) (by rw [hc]; exact principalValueCallable_lookup) rfl
      (by simpa only [hc] using hb)
  · rw [if_neg hf] at hb
    exact ExecStmt.internalCallRevert (cfg := config) (solm := frame) (evm := evm)
      (args := [expr]) (callee := principalValueCallable)
      (locals := (principalValueEntry frame.immutables present).locals)
      (evalExprs?_singleton he) (by rw [hc]; exact principalValueCallable_lookup) rfl
      (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
