import Benchmarks.UniswapV4PoolManager.TickSqrtStageSource
import Benchmarks.UniswapV4PoolManager.TickSqrtBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickSqrtFunction : FunctionDecl := contract.functions[71]!
theorem tickSqrt_lookup : lookupCallable? contract "TickMath_getSqrtPriceAtTick" =
    some tickSqrtFunction.toCallable := rfl

def tickSqrtAbsExpr : Expr :=
  .cast (.ite (.binary .lt (.var "tick") (.intLit 0))
    (.binary .sub (.intLit 0) (.var "tick")) (.var "tick")) (.elem (.int (.uint ⟨256, by decide⟩)))

theorem tickSqrtAbsEval {f : Frame} {evm : EVM.State} {tick : Int}
    (ht : f.locals.get? "tick" = some (.int tick)) (hb : tick.natAbs < 2^256) :
    evalExpr? config f evm tickSqrtAbsExpr = .ok (.int (Int.ofNat tick.natAbs)) := by
  have hc : evalExpr? config f evm (.binary .lt (.var "tick") (.intLit 0)) =
      .ok (.bool (decide (tick < 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue ht]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  have ha : evalExpr? config f evm (.ite (.binary .lt (.var "tick") (.intLit 0))
      (.binary .sub (.intLit 0) (.var "tick")) (.var "tick")) = .ok (.int (Int.ofNat tick.natAbs)) := by
    by_cases hn : tick < 0
    · simp only [evalExpr?, hc, decide_eq_true hn, bind, EvalResult.bind, pure,
        evalLocalValue ht, evalBinaryOp?, zero_sub, Int.ofNat_eq_natCast,
        Int.ofNat_natAbs_of_nonpos (le_of_lt hn)]
    · simp only [evalExpr?, hc, decide_eq_false hn, bind, EvalResult.bind, pure,
        evalLocalValue ht, Int.ofNat_eq_natCast, Int.natAbs_of_nonneg (by omega : 0 ≤ tick)]
  have hcast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) ha
  have hn := normalizeInt_uint_eq_self ⟨256, by decide⟩ (Int.ofNat tick.natAbs)
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hb)
  simpa only [hn] using hcast

theorem tickSqrtInitialEval {f : Frame} {evm : EVM.State} {absTick : UInt256}
    (ha : f.locals.get? "absTick" = some (.int (Int.ofNat absTick.toNat))) :
    evalExpr? config f evm
      (.ite (.binary .ne (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "absTick") (.intLit 1)) (.intLit 0))
        (.intLit 340265354078544963557816517032075149313)
        (.binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1) (.intLit 128))) =
      .ok (.int (Int.ofNat (tickSqrtInitial absTick).toNat)) := by
  have hc := evalNeWords (evalWordAnd (evalLocalValue (cfg := config) (evm := evm) ha)
    (show evalExpr? config f evm (.intLit 1) = .ok (.int (Int.ofNat (UInt256.ofNat 1).toNat)) by
      simp only [evalExpr?, pure]; rfl))
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hn : UInt256.land absTick (UInt256.ofNat 1) ≠ ⟨0⟩
  · simp only [evalExpr?, hc, decide_eq_true hn, bind, EvalResult.bind, pure,
      tickSqrtInitial, if_pos hn]
    rfl
  · simp only [evalExpr?, hc, decide_eq_false hn, bind, EvalResult.bind,
      tickSqrtInitial, if_neg hn]
    rfl

set_option maxHeartbeats 1000000 in
theorem tickSqrtBody {f : Frame} {evm : EVM.State} {tick : Int}
    (ht : f.locals.get? "tick" = some (.int tick)) (hb : tick.natAbs < 2^256) :
    ∃ f', ExecFuncBody config f evm tickSqrtFunction.body
      (if tick.natAbs ≤ 887272 then .returned f' evm (some [.int (Int.ofNat (tickSqrtPrice tick).toNat)])
       else .reverted) := by
  let f1 : Frame := {f with locals := f.locals.insert "sqrtPriceX96" (.int 0)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "absTick" (.int 0)}
  let f3 : Frame := {f2 with locals := f2.locals.insert "absTick" (.int (Int.ofNat tick.natAbs))}
  have ht2 : f2.locals.get? "tick" = some (.int tick) :=
    (store_get_ne2 _ _ _ (by decide : ("sqrtPriceX96" == "tick") = false)
      (by decide : ("absTick" == "tick") = false)).trans ht
  have hpref : ExecBlock config f evm (tickSqrtFunction.body.take 3) (.ok f3 evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
        (ExecBlock.consNormal (ExecStmt.assign (tickSqrtAbsEval ht2 hb) (assignLocalValue (store_get_self _ _ _)))
          ExecBlock.nil))
  have ha3 : f3.locals.get? "absTick" = some (.int (Int.ofNat tick.natAbs)) := store_get_self _ _ _
  have hguard : evalExpr? config f3 evm
      (.binary .gt (.var "absTick") (.cast (.cast (.intLit 887272) (.elem (.int (.sint ⟨256, by decide⟩))))
        (.elem (.int (.uint ⟨256, by decide⟩))))) = .ok (.bool (decide (887272 < tick.natAbs))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue ha3]
    have hl : evalExpr? config f3 evm (.cast (.cast (.intLit 887272) (.elem (.int (.sint ⟨256, by decide⟩))))
        (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (.int 887272) := by
      simp only [evalExpr?, bind, EvalResult.bind, pure, castValue?, EvalResult.ofOption]
      rfl
    rw [hl]
    simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
    simp only [show ((tick.natAbs : Int) > 887272) ↔ 887272 < tick.natAbs by omega]
  by_cases hn : tick.natAbs ≤ 887272
  · simp only [if_pos hn]
    let f4 : Frame := {f3 with locals := f3.locals.insert "price" (.int 0)}
    let f5 : Frame := {f4 with locals := f4.locals.insert "price" (.int
      (Int.ofNat (tickSqrtInitial (UInt256.ofNat tick.natAbs)).toNat))}
    have ha4 : f4.locals.get? "absTick" = some (.int (Int.ofNat (UInt256.ofNat tick.natAbs).toNat)) := by
      rw [UInt256.toNat_ofNat_of_lt hb]
      exact (store_get_ne _ _ (by decide : ("price" == "absTick") = false)).trans ha3
    have hinit := tickSqrtInitialEval (evm := evm) ha4
    have hpre5 : ExecBlock config f3 evm ((tickSqrtFunction.body.drop 3).take 3) (.ok f5 evm) :=
      ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [decide_eq_false (by omega : ¬887272 < tick.natAbs)] using hguard) ExecBlock.nil)
        (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
          (ExecBlock.consNormal (ExecStmt.assign hinit (assignLocalValue (store_get_self _ _ _))) ExecBlock.nil))
    have ha5 : f5.locals.get? "absTick" = some (.int (Int.ofNat (UInt256.ofNat tick.natAbs).toNat)) :=
      (store_get_ne _ _ (by decide : ("price" == "absTick") = false)).trans ha4
    obtain ⟨f6, hstages, hp6, hf6⟩ := tickSqrtStagesExec (evm := evm) tickSqrtFactors ha5 (store_get_self _ _ _)
    have ht5 : f5.locals.get? "tick" = some (.int tick) :=
      (store_get_ne3 _ _ _ _ (by decide : ("absTick" == "tick") = false)
        (by decide : ("price" == "tick") = false) (by decide : ("price" == "tick") = false)).trans ht2
    have ht6 := (hf6 "tick" (by decide)).trans ht5
    have hsqrt6 : f6.locals.get? "sqrtPriceX96" = some (.int 0) :=
      (hf6 "sqrtPriceX96" (by decide)).trans
        ((store_get_ne4 _ _ _ _ _ (by decide : ("absTick" == "sqrtPriceX96") = false)
          (by decide : ("absTick" == "sqrtPriceX96") = false)
          (by decide : ("price" == "sqrtPriceX96") = false)
          (by decide : ("price" == "sqrtPriceX96") = false)).trans (store_get_self _ _ _))
    have hpos : evalExpr? config f6 evm (.binary .gt (.var "tick") (.intLit 0)) = .ok (.bool (decide (0 < tick))) := by
      rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue ht6]
      simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
    let price := tickSqrtRatio (UInt256.ofNat tick.natAbs)
    let finalPrice := if 0 < tick then UInt256.div (UInt256.ofNat (2^256-1)) price else price
    have hsuffix : ∃ f7, ExecStmt config f6 evm tickSqrtFunction.body[25]! (.ok f7 evm) ∧
        f7.locals.get? "price" = some (.int (Int.ofNat finalPrice.toNat)) ∧
        f7.locals.get? "sqrtPriceX96" = some (.int 0) := by
      by_cases hp : 0 < tick
      · let f7 : Frame := {f6 with locals := f6.locals.insert "price" (.int (Int.ofNat finalPrice.toNat))}
        have hd := evalWordDiv (cfg := config) (f := f6) (evm := evm)
          (x := UInt256.ofNat (2^256-1)) (y := price)
          (a := .intLit 115792089237316195423570985008687907853269984665640564039457584007913129639935) (b := .var "price")
          (by simp only [evalExpr?, pure]; rfl) (evalLocalValue hp6)
          (by
            intro hz
            have hnz : price.toNat ≠ 0 := Nat.ne_of_gt (tickSqrtRatio_pos hn)
            exact hnz (congrArg UInt256.toNat hz))
        refine ⟨f7, ExecStmt.iteTrue (by simpa only [decide_eq_true hp] using hpos)
          (execBlock_singleton (ExecStmt.assign ?_ (assignLocalValue hp6))), store_get_self _ _ _, ?_⟩
        · simpa only [finalPrice, if_pos hp] using hd
        · exact (store_get_ne _ _ (by decide : ("price" == "sqrtPriceX96") = false)).trans hsqrt6
      · exact ⟨f6, ExecStmt.iteFalse (by simpa only [decide_eq_false hp] using hpos) ExecBlock.nil,
          by simpa only [finalPrice, if_neg hp] using hp6, hsqrt6⟩
    obtain ⟨f7, hrecip, hp7, hs7⟩ := hsuffix
    have hround := evalWordShr (b := .intLit 32) (n := 32) (by decide)
      (evalWordAdd (evalLocalValue (cfg := config) (evm := evm) hp7)
        (show evalExpr? config f7 evm (.intLit 4294967295) =
          .ok (.int (Int.ofNat (UInt256.ofNat 4294967295).toNat)) by simp only [evalExpr?, pure]; rfl))
      (by simp only [evalExpr?, pure]; rfl)
    have hcast := evalExpr_cast_int (intType := .uint ⟨160, by decide⟩) hround
    have hclean : normalizeInt (.uint ⟨160, by decide⟩) (Int.ofNat (tickSqrtPrice tick).toNat) =
        Int.ofNat (tickSqrtPrice tick).toNat := normalizeInt_uint_eq_self _ _
      (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (tickSqrtPrice_lt_160 hn))
    change evalExpr? config f7 evm _ = .ok (.int (normalizeInt (.uint ⟨160, by decide⟩)
      (Int.ofNat (tickSqrtPrice tick).toNat))) at hcast
    rw [hclean] at hcast
    let f8 : Frame := {f7 with locals := f7.locals.insert "sqrtPriceX96" (.int (Int.ofNat (tickSqrtPrice tick).toNat))}
    have htail : ExecBlock config f6 evm (tickSqrtFunction.body.drop 25)
        (.returned f8 evm (some [.int (Int.ofNat (tickSqrtPrice tick).toNat)])) :=
      ExecBlock.consNormal hrecip (ExecBlock.consNormal (ExecStmt.assign hcast (assignLocalValue hs7))
        (ABlock.start.returns (evalLocalValue (store_get_self _ _ _))))
    exact ⟨f8, .execBlockRet (execBlock_append_ok hpref
      (execBlock_append_ok hpre5 (execBlock_append_ok hstages htail)))⟩
  · simp only [if_neg hn]
    refine ⟨f3, .execBlockRevert (execBlock_append_ok hpref ?_)⟩
    change ExecBlock config f3 evm (tickSqrtFunction.body.drop 3) .reverted
    exact ExecBlock.consRevert (ExecStmt.iteTrue
      (by simpa only [decide_eq_true (by omega : 887272 < tick.natAbs)] using hguard)
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))

theorem tickSqrtCall {f : Frame} {evm : EVM.State} {e : Expr} {tick : Int}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int tick))
    (hb : tick.natAbs < 2^256) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "TickMath_getSqrtPriceAtTick" [e] retVar)
      (if tick.natAbs ≤ 887272 then
        .ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (tickSqrtPrice tick).toNat))} evm
       else .reverted) := by
  obtain ⟨f', hbody⟩ := tickSqrtBody
    (f := {f with locals := (∅ : Store).insert "tick" (.int tick)}) (evm := evm)
    (tick := tick) (store_get_self _ _ _) hb
  have hl : lookupCallable? f.contract "TickMath_getSqrtPriceAtTick" =
      some tickSqrtFunction.toCallable := by rw [hf]; exact tickSqrt_lookup
  by_cases hn : tick.natAbs ≤ 887272
  · rw [if_pos hn] at hbody ⊢
    exact internalCallFunctionReturn (value := some [.int (Int.ofNat (tickSqrtPrice tick).toNat)])
      (evalExprs?_singleton he) hl rfl hbody
  · rw [if_neg hn] at hbody ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hl rfl hbody

end Benchmarks.UniswapV4PoolManager
