import Benchmarks.CompoundIII.Comet.SignedPresentValueModel
import Benchmarks.CompoundIII.Comet.Signed256
import Benchmarks.CompoundIII.Comet.AccountMagnitude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: a bounded nonnegative value can be returned with either sign.
theorem signedPresentReturn_source (frame : Frame) (evm : EVM.State)
    (borrow : Bool) (val : UInt256) (hval : val.toNat < 2^255)
    (hv : evalExpr? config frame evm (.var (if borrow then "__c3" else "__c1")) =
      .ok (.int val.toNat)) :
    evalExpr? config frame evm (signedPresentReturnExpr borrow) =
      .ok (.int (if borrow then -Int.ofNat val.toNat else Int.ofNat val.toNat)) := by
  cases borrow with
  | false => exact hv
  | true =>
      change evalExpr? config frame evm (.var "__c3") = .ok (.int val.toNat) at hv
      apply signedRangeSourceOk (cfg := config) (frame := frame) (evm := evm)
        (i := -Int.ofNat val.toNat)
      · simp only [evalExpr?, hv, pure, bind, EvalResult.bind,
          evalBinaryOp?, Int.zero_sub, Int.ofNat_eq_natCast]
      · change -(2^255 : Int) ≤ -(val.toNat : Int)
        have : (val.toNat : Int) < 2^255 := by exact_mod_cast hval
        omega
      · change -(val.toNat : Int) < (2^255 : Int)
        omega

theorem signedPresentBranch_source (evm : EVM.State) (imms : Store)
    (principal : UInt256) (borrow : Bool) (hmin : -(2^103 : Int) < signed104 principal)
    (hsign : if borrow then signed104 principal < 0 else 0 ≤ signed104 principal) :
    ∃ final, ExecBlock config (signedPresentEntry imms principal) evm
      (signedPresentBranch borrow) (.returned final evm (some [.int
        (if borrow then -Int.ofNat (signedPresentMagnitude evm principal borrow).toNat
          else Int.ofNat (signedPresentMagnitude evm principal borrow).toNat)])) := by
  let frame := signedPresentEntry imms principal
  let index := totalsIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) borrow
  let mag := if borrow then negativePrincipal principal else positivePrincipal principal
  let val := signedPresentMagnitude evm principal borrow
  let f1 : Frame :=
    { frame with
      locals := frame.locals.insert (if borrow then "__c2" else "__c0") (.int val.toNat) }
  let f2 : Frame :=
    { f1 with locals := f1.locals.insert (if borrow then "__c3" else "__c1") (.int val.toNat) }
  have hm : mag.toNat < 2^104 := by
    cases borrow
    · exact lt_trans (positivePrincipal_lt _) (by decide)
    · exact lt_trans (negativePrincipal_lt hmin) (by decide)
  have hi := totalsIndexWord_lt
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) borrow
  have he : evalExpr? config frame evm (.var "principalValue_") =
      .ok (.int (signed104 principal)) := by
    simp only [evalExpr?, frame, signedPresentEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hp : evalExpr? config frame evm (signedPresentPrincipalExpr borrow) =
      .ok (.int mag.toNat) := by
    cases borrow
    · rw [← positivePrincipal_int hsign] at he
      exact castUintSourceOk ⟨104, by decide⟩ he hm
    · exact castUintSourceOk ⟨104, by decide⟩ (checkedPrincipalNegSource he hsign hmin) hm
  have hx : evalExpr? config frame evm (.storage ⟨totalsIndexName borrow, []⟩) =
      .ok (.int index.toNat) :=
    evalTotalsIndex evm frame.locals imms borrow (by
      cases borrow <;> simp [frame, signedPresentEntry, totalsIndexName])
  have hcall := presentValue_call frame evm borrow index mag _ _
    (if borrow then "__c2" else "__c0") rfl hi hm hx hp
  have hval : val.toNat < 2^255 :=
    lt_trans (signedPresentMagnitude_lt evm principal borrow hmin) (by decide)
  have hv : evalExpr? config f1 evm (.var (if borrow then "__c2" else "__c0")) =
      .ok (.int val.toNat) := by
    simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_self_eq_true, if_true, EvalResult.ofOption]
  have hs := signed256_call_ok f1 evm val _ (if borrow then "__c3" else "__c1") rfl hv hval
  refine ⟨f2, ExecBlock.consNormal hcall (ExecBlock.consNormal hs ?_)⟩
  apply ABlock.start.returns
  have hv2 : evalExpr? config f2 evm (.var (if borrow then "__c3" else "__c1")) =
      .ok (.int val.toNat) := by
    simp only [evalExpr?, f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_self_eq_true, if_true, EvalResult.ofOption]
  exact signedPresentReturn_source f2 evm borrow val hval hv2

theorem signedPresent_source_nonneg (evm : EVM.State) (imms : Store) (principal : UInt256)
    (hmin : -(2^103 : Int) < signed104 principal) (hp : 0 ≤ signed104 principal) :
    ∃ final, ExecFuncBody config (signedPresentEntry imms principal) evm
      signedPresentCallable.body (.returned final evm
        (some [.int (signedPresentMagnitude evm principal false).toNat])) := by
  obtain ⟨final, hb⟩ := signedPresentBranch_source evm imms principal false hmin hp
  refine ⟨final, ExecFuncBody.execBlockRet (ExecBlock.consReturn (ExecStmt.iteTrue ?_ hb))⟩
  change evalExpr? config (signedPresentEntry imms principal) evm
    (.binary .ge (.var "principalValue_") (.intLit 0)) = .ok (.bool true)
  simp only [evalExpr?, signedPresentEntry, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption, pure, bind, EvalResult.bind,
    evalBinaryOp?, beq_self_eq_true, if_true]
  exact congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_true hp)

theorem signedPresent_source_neg (evm : EVM.State) (imms : Store) (principal : UInt256)
    (hmin : -(2^103 : Int) < signed104 principal) (hp : signed104 principal < 0) :
    ∃ final, ExecFuncBody config (signedPresentEntry imms principal) evm
      signedPresentCallable.body (.returned final evm
        (some [.int (-Int.ofNat (signedPresentMagnitude evm principal true).toNat)])) := by
  obtain ⟨final, hb⟩ := signedPresentBranch_source evm imms principal true hmin hp
  simp only [if_true] at hb
  refine ⟨final, ExecFuncBody.execBlockRet (ExecBlock.consReturn (ExecStmt.iteFalse ?_ hb))⟩
  change evalExpr? config (signedPresentEntry imms principal) evm
    (.binary .ge (.var "principalValue_") (.intLit 0)) = .ok (.bool false)
  simp only [evalExpr?, signedPresentEntry, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption, pure, bind, EvalResult.bind,
    evalBinaryOp?, beq_self_eq_true, if_true]
  exact congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_false (not_le.mpr hp))

theorem signedPresent_source_ok (evm : EVM.State) (imms : Store) (principal : UInt256)
    (hmin : -(2^103 : Int) < signed104 principal) :
    ∃ final, ExecFuncBody config (signedPresentEntry imms principal) evm
      signedPresentCallable.body
      (.returned final evm (some [.int (signedPresentValueInt evm principal)])) := by
  by_cases hp : 0 ≤ signed104 principal
  · simpa only [signedPresentValueInt, if_pos hp] using
      signedPresent_source_nonneg evm imms principal hmin hp
  · simpa only [signedPresentValueInt, if_neg hp] using
      signedPresent_source_neg evm imms principal hmin (by omega)

theorem signedPresent_source_revert (evm : EVM.State) (imms : Store) (principal : UInt256)
    (hmin : ¬ -(2^103 : Int) < signed104 principal) :
    ExecFuncBody config (signedPresentEntry imms principal) evm signedPresentCallable.body
      .reverted := by
  let frame := signedPresentEntry imms principal
  have hmin' : signed104 principal = -(2^103 : Int) := by
    have := signed104_bounds principal
    omega
  have he : evalExpr? config frame evm (.var "principalValue_") =
      .ok (.int (signed104 principal)) := by
    simp only [evalExpr?, frame, signedPresentEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hg : evalExpr? config frame evm (.binary .ge (.var "principalValue_") (.intLit 0)) =
      .ok (.bool false) := by
    simp only [evalExpr?, he, hmin', pure, bind, EvalResult.bind, evalBinaryOp?]
    rfl
  have hn := checkedPrincipalNegSource_revert he hmin'
  have hp : evalExpr? config frame evm (signedPresentPrincipalExpr true) = .revert := by
    simp only [signedPresentPrincipalExpr, if_true, evalExpr?, hn, bind, EvalResult.bind]
  have hx : evalExpr? config frame evm (.storage ⟨totalsIndexName true, []⟩) =
      .ok (.int (totalsIndexWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) true).toNat) :=
    evalTotalsIndex evm frame.locals imms true (by
      simp [frame, signedPresentEntry, totalsIndexName])
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.iteFalse hg ?_)
  apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
  change evalExprs? config frame evm
    [.storage ⟨totalsIndexName true, []⟩, signedPresentPrincipalExpr true] = .revert
  simp only [evalExprs?, hx, hp, bind, EvalResult.bind]

theorem signedPresent_call (frame : Frame) (evm : EVM.State) (principal : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int (signed104 principal))) :
    ExecStmt config frame evm (.internalCall "presentValue" [expr] ret)
      (if -(2^103 : Int) < signed104 principal then
        .ok { frame with locals := frame.locals.insert ret (.int
          (signedPresentValueInt evm principal)) } evm else .reverted) := by
  by_cases hmin : -(2^103 : Int) < signed104 principal
  · rw [if_pos hmin]
    obtain ⟨final, hb⟩ := signedPresent_source_ok evm frame.immutables principal hmin
    exact ExecStmt.internalCallReturn (cfg := config) (solm := frame) (evm := evm)
      (args := [expr]) (callee := signedPresentCallable)
      (locals := (signedPresentEntry frame.immutables principal).locals)
      (argVals := [.int (signed104 principal)])
      (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
      (by rw [hc]; exact signedPresentCallable_lookup) rfl
      (by simpa only [hc] using hb)
  · rw [if_neg hmin]
    exact ExecStmt.internalCallRevert (cfg := config) (solm := frame) (evm := evm)
      (args := [expr]) (callee := signedPresentCallable)
      (locals := (signedPresentEntry frame.immutables principal).locals)
      (argVals := [.int (signed104 principal)])
      (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
      (by rw [hc]; exact signedPresentCallable_lookup) rfl
      (by simpa only [hc] using signedPresent_source_revert evm frame.immutables principal hmin)

end Benchmarks.CompoundIII.Comet
