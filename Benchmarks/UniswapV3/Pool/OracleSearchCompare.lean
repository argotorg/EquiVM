import Benchmarks.UniswapV3.Pool.OracleSearchRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleSearchFirst (time target cardinality left right : UInt256) (σ : AccountMap)
    (I : ExecutionEnv) : Bool :=
  oracleLte time (oracleSearchBefore left right cardinality σ I).timestamp target

def oracleSearchSecond (time target cardinality left right : UInt256) (σ : AccountMap)
    (I : ExecutionEnv) : Bool :=
  oracleLte time target (oracleSearchAfter left right cardinality σ I).timestamp

def oracleSearchPairFrame (locals imms : Store) (evm : EVM.State)
    (left right cardinality : UInt256) : Frame :=
  { (oracleSearchReadFrame locals imms evm left right cardinality) with
    locals := (oracleSearchReadFrame locals imms evm left right cardinality).locals.insert "atOrAfter"
      (oracleSearchAfter left right cardinality evm.accountMap evm.executionEnv).value }

def oracleSearchFirstFrame (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256) : Frame :=
  { (oracleSearchPairFrame locals imms evm left right cardinality) with
    locals := (oracleSearchPairFrame locals imms evm left right cardinality).locals.insert
      "targetAtOrAfter" (.bool (oracleSearchFirst time target cardinality left right
        evm.accountMap evm.executionEnv)) }

def oracleSearchConditionFrame (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256) : Frame :=
  let first := oracleSearchFirstFrame locals imms evm time target cardinality left right
  { first with locals := first.locals.insert "targetBeforeOrAt" (.bool false) }

def oracleSearchCompareFrame (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256) : Frame :=
  let base := oracleSearchConditionFrame locals imms evm time target cardinality left right
  { contract := contract
    immutables := imms
    locals := if oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv then
      (base.locals.insert "__c1" (.bool (oracleSearchSecond time target cardinality
        left right evm.accountMap evm.executionEnv))).insert "targetBeforeOrAt"
          (.bool (oracleSearchSecond time target cardinality left right evm.accountMap evm.executionEnv))
    else base.locals }

theorem oracleSearchPairBindings (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right) :
    OracleSearchBindings (oracleSearchPairFrame locals imms evm left right cardinality).locals
      time target cardinality left right :=
  (oracleSearchReadBindings locals imms evm time target cardinality left right h).insert_aux
    "atOrAfter" _ (by decide)

theorem oracleSearchPairPrefix (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16)
    (hinit : (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).initialized = true) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (oracleSearchBody.take 4)
      (.ok (oracleSearchPairFrame locals imms evm left right cardinality) evm) := by
  change ExecBlock _ _ _ (oracleSearchBody.take 2 ++ (oracleSearchBody.drop 2).take 2) _
  apply execBlock_append_ok (oracleSearchReadPrefix locals imms evm time target cardinality left right h hn hc)
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
  · simpa only [hinit, Bool.not_true] using evalOracleSearchInitialized locals imms evm left right cardinality
  have hr := oracleSearchReadBindings locals imms evm time target cardinality left right h
  have hi : evalExpr? config (oracleSearchReadFrame locals imms evm left right cardinality) evm
      (.var "i") = .ok (.int (Int.ofNat (oracleSearchMiddle left right).toNat)) :=
    evalExpr_var_get (by simp [oracleSearchReadFrame, Std.HashMap.getElem_insert])
  have hone : evalExpr? config (oracleSearchReadFrame locals imms evm left right cardinality) evm
      (.intLit 1) = .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  have he := evalExpr_word_mod (evalExpr_word_add hi hone) (evalExpr_var_get hr.cardinality) hn
  obtain ⟨oldAfter, hafter⟩ := hr.atOrAfter
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalOracleObservationExpr _ _ _ _ _ hr.base he
      (oracleSearchRemainder_lt _ cardinality hn hc)) (assignLocalVarBase_frame hafter)) ExecBlock.nil

theorem oracleSearchFirstCall (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (ht : target.toNat < 2 ^ 32) :
    ExecStmt config (oracleSearchPairFrame locals imms evm left right cardinality) evm
      oracleSearchBody[4]!
      (.ok (oracleSearchFirstFrame locals imms evm time target cardinality left right) evm) := by
  have hp := oracleSearchPairBindings locals imms evm time target cardinality left right h
  have et := evalExpr_var_get (cfg := config) (evm := evm) hp.time
  have eg := evalExpr_var_get (cfg := config) (evm := evm) hp.target
  have eb := evalOracleTimestamp (frame := oracleSearchPairFrame locals imms evm left right cardinality)
    (evm := evm) (name := "beforeOrAt")
    (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv)
    (by simp [oracleSearchPairFrame, oracleSearchReadFrame, Std.HashMap.getElem_insert])
  apply oracleLteCall
  · change evalExprs? config (oracleSearchPairFrame locals imms evm left right cardinality) evm
      [.var "time", .field (.var "beforeOrAt") "blockTimestamp", .var "target"] = _
    simp only [evalExprs?, et, eg, eb, bind, EvalResult.bind, pure]
  · exact oracleStoredTimestamp_lt _ _ _
  · exact ht

theorem oracleSearchConditionBindings (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right) :
    OracleSearchBindings (oracleSearchConditionFrame locals imms evm time target cardinality left right).locals
      time target cardinality left right :=
  ((oracleSearchPairBindings locals imms evm time target cardinality left right h).insert_aux
    "targetAtOrAfter" _ (by decide)).insert_aux "targetBeforeOrAt" _ (by decide)

theorem oracleSearchCompareTail (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (ht : target.toNat < 2 ^ 32) :
    ExecBlock config (oracleSearchFirstFrame locals imms evm time target cardinality left right) evm
      ((oracleSearchBody.drop 5).take 2)
      (.ok (oracleSearchCompareFrame locals imms evm time target cardinality left right) evm) := by
  let base := oracleSearchConditionFrame locals imms evm time target cardinality left right
  let first := oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv
  let second := oracleSearchSecond time target cardinality left right evm.accountMap evm.executionEnv
  have hbase := oracleSearchConditionBindings locals imms evm time target cardinality left right h
  have et := evalExpr_var_get (cfg := config) (frame := base) (evm := evm) hbase.time
  have eg := evalExpr_var_get (cfg := config) (frame := base) (evm := evm) hbase.target
  have ea := evalOracleTimestamp (frame := base) (evm := evm) (name := "atOrAfter")
    (oracleSearchAfter left right cardinality evm.accountMap evm.executionEnv)
    (by simp [base, oracleSearchConditionFrame, oracleSearchFirstFrame, oracleSearchPairFrame,
      Std.HashMap.getElem_insert])
  have hargs : evalExprs? config base evm
      [.var "time", .var "target", .field (.var "atOrAfter") "blockTimestamp"] =
      .ok [.int (Int.ofNat time.toNat), .int (Int.ofNat target.toNat),
        .int (Int.ofNat (oracleSearchAfter left right cardinality evm.accountMap evm.executionEnv).timestamp.toNat)] := by
    simp only [evalExprs?, et, eg, ea, bind, EvalResult.bind, pure]
  have hcall := oracleLteCall base.locals imms evm _ "__c1" time target
    (oracleSearchAfter left right cardinality evm.accountMap evm.executionEnv).timestamp
    hargs ht (oracleStoredTimestamp_lt _ _ _)
  have he : evalExpr? config base evm (.var "targetAtOrAfter") = .ok (.bool first) :=
    evalExpr_var_get (by simp [base, oracleSearchConditionFrame, oracleSearchFirstFrame,
      first, Std.HashMap.getElem_insert])
  refine ExecBlock.consNormal (solm' := base) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  by_cases hf : first = true
  · simp only [oracleSearchCompareFrame, show oracleSearchFirst time target cardinality left right
        evm.accountMap evm.executionEnv = true from hf, ↓reduceIte]
    refine ExecBlock.consNormal (ExecStmt.iteTrue (by simpa only [hf] using he) ?_) ExecBlock.nil
    refine ExecBlock.consNormal hcall ?_
    refine ExecBlock.consNormal (ExecStmt.assign (value := .bool second) ?_ ?_) ExecBlock.nil
    · exact evalExpr_var_get (by simp [second, oracleSearchSecond])
    · apply assignLocalVarBase_frame (old := .bool false)
      simp [base, oracleSearchConditionFrame, Std.HashMap.getElem_insert]
  · simp only [oracleSearchCompareFrame, show oracleSearchFirst time target cardinality left right
        evm.accountMap evm.executionEnv ≠ true from hf]
    refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
    simpa only [Bool.eq_false_iff.mpr hf] using he

theorem oracleSearchComparePrefix (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16)
    (ht : target.toNat < 2 ^ 32)
    (hinit : (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).initialized = true) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (oracleSearchBody.take 7)
      (.ok (oracleSearchCompareFrame locals imms evm time target cardinality left right) evm) := by
  change ExecBlock _ _ _ (oracleSearchBody.take 4 ++ (oracleSearchBody.drop 4).take 3) _
  apply execBlock_append_ok (oracleSearchPairPrefix locals imms evm time target cardinality left right h hn hc hinit)
  exact ExecBlock.consNormal (oracleSearchFirstCall locals imms evm time target cardinality left right h ht)
    (oracleSearchCompareTail locals imms evm time target cardinality left right h ht)

end Benchmarks.UniswapV3.Pool
