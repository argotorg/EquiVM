import Benchmarks.CompoundIII.Comet.RateModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def rateEntryFrame (v : CometWithExtendedAssetListImmutables) (u : UInt256) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "utilization" (.int u.toNat),
    immutables := immStore v }

def rateFinalFrame (v : CometWithExtendedAssetListImmutables) (b : Bool) (u : UInt256) : Frame :=
  let p := rateParams v b
  let frame := rateEntryFrame v u
  if u.toNat ≤ p.kink.toNat then
    { frame with
      locals := (frame.locals.insert "__c0" (.int (mulFactorWord p.low u).toNat)).insert
        "__c1" (.int (p.base + mulFactorWord p.low u).toNat) }
  else
    { frame with
      locals := ((frame.locals.insert "__c2" (.int (mulFactorWord p.low p.kink).toNat)).insert
        "__c3" (.int (mulFactorWord p.high (UInt256.sub u p.kink)).toNat)).insert
          "__c4" (.int ((p.base + mulFactorWord p.low p.kink) +
            mulFactorWord p.high (UInt256.sub u p.kink)).toNat) }

theorem evalRateKink (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (frame : Frame) (evm : EVM.State) (hi : frame.immutables = immStore v) :
    evalExpr? config frame evm (.immutable (rateKinkName b)) =
      .ok (.int (Int.ofNat (rateParams v b).kink.toNat)) := by
  simp only [evalExpr?, hi, rateKink_get, EvalResult.ofOption]
  rfl

theorem evalRateLow (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (frame : Frame) (evm : EVM.State) (hi : frame.immutables = immStore v) :
    evalExpr? config frame evm (.immutable (rateLowName b)) =
      .ok (.int (Int.ofNat (rateParams v b).low.toNat)) := by
  simp only [evalExpr?, hi, rateLow_get, EvalResult.ofOption]
  rfl

theorem evalRateHigh (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (frame : Frame) (evm : EVM.State) (hi : frame.immutables = immStore v) :
    evalExpr? config frame evm (.immutable (rateHighName b)) =
      .ok (.int (Int.ofNat (rateParams v b).high.toNat)) := by
  simp only [evalExpr?, hi, rateHigh_get, EvalResult.ofOption]
  rfl

theorem evalRateBase (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (frame : Frame) (evm : EVM.State) (hi : frame.immutables = immStore v) :
    evalExpr? config frame evm (.immutable (rateBaseName b)) =
      .ok (.int (Int.ofNat (rateParams v b).base.toNat)) := by
  simp only [evalExpr?, hi, rateBase_get, EvalResult.ofOption]
  rfl

theorem rateCallable_block (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (u : UInt256) (evm : EVM.State) :
    ExecBlock config (rateEntryFrame v u) evm (rateCallable b).body
      (if RateValid (rateParams v b) u then
        .returned (rateFinalFrame v b u) evm (some [.int (rateWord (rateParams v b) u).toNat])
       else .reverted) := by
  let p := rateParams v b
  let f0 := rateEntryFrame v u
  have hu : evalExpr? config f0 evm (.var "utilization") = .ok (.int (Int.ofNat u.toNat)) := by
    simp only [evalExpr?, f0, rateEntryFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hk := evalRateKink v b f0 evm rfl
  have hc := naturalLeSource hu hk
  change ExecBlock config f0 evm _ (if RateValid p u then
    .returned (rateFinalFrame v b u) evm (some [.int (rateWord p u).toNat]) else .reverted)
  by_cases hle : u.toNat ≤ p.kink.toNat
  · have hcond : evalExpr? config f0 evm
        (.binary .le (.var "utilization") (.immutable (rateKinkName b))) = .ok (.bool true) :=
      hc.trans (by rw [decide_eq_true hle])
    apply execBlock_singleton (ExecStmt.iteTrue hcond ?_)
    by_cases hm : p.low.toNat * u.toNat < UInt256.size
    · let f1 : Frame := { f0 with locals := f0.locals.insert "__c0" (.int (mulFactorWord p.low u).toNat) }
      apply ExecBlock.consNormal
        (mulFactor_call_ok f0 evm p.low u _ _ "__c0" rfl (evalRateLow v b f0 evm rfl) hu hm)
      have hv : evalExpr? config f1 evm (.var "__c0") =
          .ok (.int (Int.ofNat (mulFactorWord p.low u).toNat)) := by
        simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl
      have hb := evalRateBase v b f1 evm rfl
      by_cases ha : p.base.toNat + (mulFactorWord p.low u).toNat < UInt256.size
      · have he := checkedAddSourceOk hb hv ha
        by_cases hs : (p.base + mulFactorWord p.low u).toNat < 2^64
        · simp only [RateValid, hle, hm, ha, hs, and_self, if_true]
          apply ExecBlock.consNormal (safe64_call_ok f1 evm _ _ "__c1" rfl he hs)
          have hframe : rateFinalFrame v b u =
              { f1 with locals := f1.locals.insert "__c1" (.int (p.base + mulFactorWord p.low u).toNat) } := by
            simp only [rateFinalFrame, show u.toNat ≤ (rateParams v b).kink.toNat from hle, if_true]
            rfl
          rw [hframe]
          apply ABlock.start.returns
          simp only [evalExpr?, rateWord, hle, if_true, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]
          rfl
        · simp only [RateValid, hle, hm, ha, hs, and_false, if_true, if_false]
          exact ExecBlock.consRevert (safe64_call_revert f1 evm _ _ "__c1" rfl he hs)
      · simp only [RateValid, hle, hm, ha, false_and, and_false, if_true, if_false]
        apply ExecBlock.consRevert
        apply ExecStmt.internalCallArgsRevert
        have he := checkedAddSourceOverflow hb hv (Nat.le_of_not_gt ha)
        change evalExprs? config f1 evm _ = _
        simp only [evalExprs?, he, bind, EvalResult.bind]
    · simp only [RateValid, hle, hm, false_and, if_true, if_false]
      exact ExecBlock.consRevert
        (mulFactor_call_revert f0 evm p.low u _ _ "__c0" rfl (evalRateLow v b f0 evm rfl) hu hm)
  · have hcond : evalExpr? config f0 evm
        (.binary .le (.var "utilization") (.immutable (rateKinkName b))) = .ok (.bool false) :=
      hc.trans (by rw [decide_eq_false hle])
    apply execBlock_singleton (ExecStmt.iteFalse hcond ?_)
    by_cases hm : p.low.toNat * p.kink.toNat < UInt256.size
    · let f1 : Frame :=
        { f0 with locals := f0.locals.insert "__c2" (.int (mulFactorWord p.low p.kink).toNat) }
      apply ExecBlock.consNormal (mulFactor_call_ok f0 evm p.low p.kink _ _ "__c2" rfl
        (evalRateLow v b f0 evm rfl) hk hm)
      have hu1 : evalExpr? config f1 evm (.var "utilization") = .ok (.int (Int.ofNat u.toNat)) := by
        simp only [evalExpr?, f1, f0, rateEntryFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl
      have hsub := uint256RangeSourceOk
        (subSourceOk hu1 (evalRateKink v b f1 evm rfl) (Nat.le_of_lt (Nat.lt_of_not_ge hle)))
        (UInt256.sub u p.kink).val.isLt
      by_cases hh : p.high.toNat * (UInt256.sub u p.kink).toNat < UInt256.size
      · let f2 : Frame := { f1 with
          locals := f1.locals.insert "__c3" (.int (mulFactorWord p.high (UInt256.sub u p.kink)).toNat) }
        apply ExecBlock.consNormal (mulFactor_call_ok f1 evm p.high (UInt256.sub u p.kink)
          _ _ "__c3" rfl (evalRateHigh v b f1 evm rfl) hsub hh)
        have hlo : evalExpr? config f2 evm (.var "__c2") =
            .ok (.int (Int.ofNat (mulFactorWord p.low p.kink).toNat)) := by
          simp only [evalExpr?, f2, f1, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]
          rfl
        have hhi : evalExpr? config f2 evm (.var "__c3") =
            .ok (.int (Int.ofNat (mulFactorWord p.high (UInt256.sub u p.kink)).toNat)) := by
          simp only [evalExpr?, f2, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]
          rfl
        have hb := evalRateBase v b f2 evm rfl
        by_cases ha : p.base.toNat + (mulFactorWord p.low p.kink).toNat < UInt256.size
        · have he1 := checkedAddSourceOk hb hlo ha
          by_cases ha2 : (p.base + mulFactorWord p.low p.kink).toNat +
              (mulFactorWord p.high (UInt256.sub u p.kink)).toNat < UInt256.size
          · have he2 := checkedAddSourceOk he1 hhi ha2
            by_cases hs : ((p.base + mulFactorWord p.low p.kink) +
                mulFactorWord p.high (UInt256.sub u p.kink)).toNat < 2^64
            · simp only [RateValid, hle, hm, hh, ha, ha2, hs, and_self, if_false, if_true]
              apply ExecBlock.consNormal (safe64_call_ok f2 evm _ _ "__c4" rfl he2 hs)
              have hframe : rateFinalFrame v b u =
                  { f2 with
                    locals := f2.locals.insert "__c4"
                      (.int ((p.base + mulFactorWord p.low p.kink) +
                        mulFactorWord p.high (UInt256.sub u p.kink)).toNat) } := by
                simp only [rateFinalFrame, show ¬ u.toNat ≤ (rateParams v b).kink.toNat from hle, if_false]
                rfl
              rw [hframe]
              apply ABlock.start.returns
              simp only [evalExpr?, rateWord, hle, if_false, Std.HashMap.get?_eq_getElem?,
                Std.HashMap.getElem?_insert, EvalResult.ofOption]
              rfl
            · simp only [RateValid, hle, hm, hh, ha, ha2, hs, and_false, if_false]
              exact ExecBlock.consRevert (safe64_call_revert f2 evm _ _ "__c4" rfl he2 hs)
          · simp only [RateValid, hle, hm, hh, ha, ha2, false_and, and_false, if_false]
            apply ExecBlock.consRevert
            apply ExecStmt.internalCallArgsRevert
            have he := checkedAddSourceOverflow he1 hhi (Nat.le_of_not_gt ha2)
            change evalExprs? config f2 evm _ = _
            simp only [evalExprs?, he, bind, EvalResult.bind]
        · simp only [RateValid, hle, hm, hh, ha, false_and, and_false, if_false]
          apply ExecBlock.consRevert
          apply ExecStmt.internalCallArgsRevert
          have he := checkedAddSourceOverflow hb hlo (Nat.le_of_not_gt ha)
          change evalExprs? config f2 evm _ = _
          simp only [evalExprs?, evalExpr?, he, bind, EvalResult.bind]
      · simp only [RateValid, hle, hm, hh, false_and, and_false, if_false]
        exact ExecBlock.consRevert (mulFactor_call_revert f1 evm p.high (UInt256.sub u p.kink)
          _ _ "__c3" rfl (evalRateHigh v b f1 evm rfl) hsub hh)
    · simp only [RateValid, hle, hm, false_and, if_false]
      exact ExecBlock.consRevert (mulFactor_call_revert f0 evm p.low p.kink _ _ "__c2" rfl
        (evalRateLow v b f0 evm rfl) hk hm)

theorem rateCallable_returns (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (u : UInt256) (evm : EVM.State) (hvalid : RateValid (rateParams v b) u) :
    ExecFuncBody config (rateEntryFrame v u) evm (rateCallable b).body
      (.returned (rateFinalFrame v b u) evm (some [.int (rateWord (rateParams v b) u).toNat])) := by
  apply ExecFuncBody.execBlockRet
  simpa only [if_pos hvalid] using rateCallable_block v b u evm

theorem rateCallable_reverts (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (u : UInt256) (evm : EVM.State) (hvalid : ¬ RateValid (rateParams v b) u) :
    ExecFuncBody config (rateEntryFrame v u) evm (rateCallable b).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simpa only [if_neg hvalid] using rateCallable_block v b u evm

theorem rate_call_ok (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (frame : Frame) (evm : EVM.State) (u : UInt256) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hu : evalExpr? config frame evm expr = .ok (.int u.toNat))
    (hvalid : RateValid (rateParams v b) u) :
    ExecStmt config frame evm (.internalCall (rateCallableName b) [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int (rateWord (rateParams v b) u).toNat) }
        evm) := by
  exact ExecStmt.internalCallReturn (callee := rateCallable b)
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.int u.toNat])
    (by simp only [evalExprs?, hu, pure, bind, EvalResult.bind])
    (by rw [hc]; exact rateCallable_lookup b) rfl
    (by simpa only [hc, hi] using rateCallable_returns v b u evm hvalid)

theorem rate_call_revert (v : CometWithExtendedAssetListImmutables) (b : Bool)
    (frame : Frame) (evm : EVM.State) (u : UInt256) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hu : evalExpr? config frame evm expr = .ok (.int u.toNat))
    (hvalid : ¬ RateValid (rateParams v b) u) :
    ExecStmt config frame evm (.internalCall (rateCallableName b) [expr] ret) .reverted := by
  exact ExecStmt.internalCallRevert (callee := rateCallable b)
    (cfg := config) (solm := frame) (evm := evm) (args := [expr]) (argVals := [.int u.toNat])
    (by simp only [evalExprs?, hu, pure, bind, EvalResult.bind])
    (by rw [hc]; exact rateCallable_lookup b) rfl
    (by simpa only [hc, hi] using rateCallable_reverts v b u evm hvalid)

end Benchmarks.CompoundIII.Comet
