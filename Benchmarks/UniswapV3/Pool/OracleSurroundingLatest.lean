import Benchmarks.UniswapV3.Pool.OracleSurroundingModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleSurroundingLatestAfter (last : OracleObservation) (target : UInt256) (tick : Int)
    (liquidity : UInt256) : OracleObservation :=
  if last.timestamp = target then oracleZeroObservation
  else oracleTransformed last target tick liquidity

def oracleSurroundingLatestBranch : List Stmt :=
  match oracleSurroundingFunction.body[4]! with
  | .ite _ yes _ => yes
  | _ => []

theorem oracleSurroundingLatestBranchReturns (imms : Store) (evm : EVM.State)
    (time target : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) :
    let last := oracleStoredObservation index evm.accountMap evm.executionEnv
    ∃ frame, ExecBlock config
      (oracleSurroundingFirstFrame imms evm time target tick index liquidity cardinality) evm
      oracleSurroundingLatestBranch (.returned frame evm
        (some [last.value, (oracleSurroundingLatestAfter last target tick liquidity).value])) := by
  dsimp only
  let last := oracleStoredObservation index evm.accountMap evm.executionEnv
  let f := oracleSurroundingFirstFrame imms evm time target tick index liquidity cardinality
  change ∃ frame, ExecBlock config f evm oracleSurroundingLatestBranch
    (.returned frame evm
      (some [last.value, (oracleSurroundingLatestAfter last target tick liquidity).value]))
  have hb : f.locals.get? "beforeOrAt" = some last.value := by
    simp [f, last, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
      Std.HashMap.getElem_insert]
  have ha : f.locals.get? "atOrAfter" = some oracleZeroObservation.value := by
    simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
      oracleSurroundingZeroFrame, Std.HashMap.getElem_insert]
  have ht : f.locals.get? "target" = some (.int (Int.ofNat target.toNat)) := by
    simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
      oracleSurroundingZeroFrame, oracleSurroundingLocals, Std.HashMap.getElem_insert]
  have eb := evalOracleTimestamp (frame := f) (evm := evm) last hb
  have et := evalExpr_var_get (cfg := config) (evm := evm) ht
  have heq := evalExpr_word_eq eb et
  by_cases h : last.timestamp = target
  · refine ⟨f, ?_⟩
    simp only [oracleSurroundingLatestAfter, if_pos h]
    refine ExecBlock.consReturn (ExecStmt.iteTrue ?_ (ExecBlock.consReturn (ExecStmt.return ?_)))
    · simpa only [h, decide_true] using heq
    · have ebv := evalExpr_var_get (cfg := config) (evm := evm) hb
      have eav := evalExpr_var_get (cfg := config) (evm := evm) ha
      change evalExprs? config f evm [.var "beforeOrAt", .var "atOrAfter"] = _
      simp only [evalExprs?, ebv, eav, bind, EvalResult.bind, pure]
  · let result := oracleTransformed last target tick liquidity
    let ft := resumeAfterInternalCall f "__c1" (some [result.value])
    have hargs : evalExprs? config f evm
        [.var "beforeOrAt", .var "target", .var "tick", .var "liquidity"] =
        .ok [last.value, .int (Int.ofNat target.toNat), .int tick,
          .int (Int.ofNat liquidity.toNat)] := by
      have ebv := evalExpr_var_get (cfg := config) (evm := evm) hb
      have ek : evalExpr? config f evm (.var "tick") = .ok (.int tick) :=
        evalExpr_var_get (by simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
          oracleSurroundingZeroFrame, oracleSurroundingLocals, Std.HashMap.getElem_insert])
      have el : evalExpr? config f evm (.var "liquidity") =
          .ok (.int (Int.ofNat liquidity.toNat)) := evalExpr_var_get (by
        simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
          oracleSurroundingZeroFrame, oracleSurroundingLocals, Std.HashMap.getElem_insert])
      simp only [evalExprs?, ebv, et, ek, el, bind, EvalResult.bind, pure]
    have hcall := internalCallFunctionReturn (cfg := config) (caller := f) (evm := evm)
      (retVar := "__c1") (callee := oracleTransformFunction)
      hargs oracleTransformLookup (oracleTransformBind last target tick liquidity)
      (oracleTransformReturns imms evm last target tick liquidity htick)
    refine ⟨ft, ?_⟩
    simp only [oracleSurroundingLatestAfter, if_neg h]
    refine ExecBlock.consReturn (ExecStmt.iteFalse ?_ ?_)
    · simpa only [h, decide_false] using heq
    · refine ExecBlock.consNormal hcall (ExecBlock.consReturn (ExecStmt.return ?_))
      change evalExprs? config ft evm [.var "beforeOrAt", .var "__c1"] = _
      have hb' : ft.locals.get? "beforeOrAt" = some last.value := by
        have hbget := hb
        rw [Std.HashMap.get?_eq_getElem?] at hbget
        simp [ft, resumeAfterInternalCall, collapseReturns, hbget, Std.HashMap.getElem?_insert]
      have hr : ft.locals.get? "__c1" = some result.value := by
        simp [ft, resumeAfterInternalCall, collapseReturns]
      have ebv := evalExpr_var_get (cfg := config) (evm := evm) hb'
      have erv := evalExpr_var_get (cfg := config) (evm := evm) hr
      simp only [evalExprs?, ebv, erv, bind, EvalResult.bind, pure]
      rfl

theorem oracleSurroundingLatestReturns (imms : Store) (evm : EVM.State)
    (time target : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (hin : index.toNat < 65535) (ht : target.toNat < 2 ^ 32)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hfirst : oracleSurroundingFirst time target index evm.accountMap evm.executionEnv = true) :
    let last := oracleStoredObservation index evm.accountMap evm.executionEnv
    ∃ frame, ExecFuncBody config
      (oracleSurroundingFrame imms time target tick index liquidity cardinality) evm
      oracleSurroundingFunction.body (.returned frame evm
        (some [last.value, (oracleSurroundingLatestAfter last target tick liquidity).value])) := by
  obtain ⟨frame, hbranch⟩ := oracleSurroundingLatestBranchReturns imms evm time target tick index
    liquidity cardinality htick
  refine ⟨frame, ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 4 oracleSurroundingFunction.body]
  apply execBlock_append_ok
    (oracleSurroundingFirstPrefix imms evm time target tick index liquidity cardinality hin ht)
  refine ExecBlock.consReturn (ExecStmt.iteTrue ?_ hbranch)
  exact evalExpr_var_get (by simp [oracleSurroundingFirstFrame, hfirst])

end Benchmarks.UniswapV3.Pool
