import Benchmarks.UniswapV3.Pool.OracleSearchCompare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSearchCompareBindings (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right) :
    OracleSearchBindings (oracleSearchCompareFrame locals imms evm time target cardinality left right).locals
      time target cardinality left right := by
  have hb := oracleSearchConditionBindings locals imms evm time target cardinality left right h
  unfold oracleSearchCompareFrame
  split
  · exact (hb.insert_aux "__c1" _ (by decide)).insert_aux "targetBeforeOrAt" _ (by decide)
  · exact hb

theorem oracleSearchCompareGets (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256) :
    let frame := oracleSearchCompareFrame locals imms evm time target cardinality left right
    frame.locals.get? "targetAtOrAfter" =
        some (.bool (oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv)) ∧
      frame.locals.get? "targetBeforeOrAt" = some (.bool
        (oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv &&
         oracleSearchSecond time target cardinality left right evm.accountMap evm.executionEnv)) ∧
      frame.locals.get? "i" = some (.int (Int.ofNat (oracleSearchMiddle left right).toNat)) ∧
      frame.locals.get? "beforeOrAt" =
        some (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).value ∧
      frame.locals.get? "atOrAfter" =
        some (oracleSearchAfter left right cardinality evm.accountMap evm.executionEnv).value := by
  cases hf : oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv <;>
    simp [oracleSearchCompareFrame, oracleSearchConditionFrame, oracleSearchFirstFrame,
      oracleSearchPairFrame, oracleSearchReadFrame, Std.HashMap.getElem_insert, hf]

theorem oracleSearchFound (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16)
    (ht : target.toNat < 2 ^ 32)
    (hinit : (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).initialized = true)
    (hfound : (oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv &&
      oracleSearchSecond time target cardinality left right evm.accountMap evm.executionEnv) = true) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      oracleSearchBody
      (.break (oracleSearchCompareFrame locals imms evm time target cardinality left right) evm) := by
  rw [← List.take_append_drop 7 oracleSearchBody]
  apply execBlock_append_ok
    (oracleSearchComparePrefix locals imms evm time target cardinality left right h hn hc ht hinit)
  refine ExecBlock.consBreak (ExecStmt.iteTrue ?_ (ExecBlock.consBreak ExecStmt.break))
  simpa only [hfound] using evalExpr_var_get (cfg := config) (evm := evm)
    (frame := oracleSearchCompareFrame locals imms evm time target cardinality left right)
    (oracleSearchCompareGets locals imms evm time target cardinality left right).2.1

theorem oracleSearchAdvance (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16)
    (ht : target.toNat < 2 ^ 32)
    (hinit : (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).initialized = true)
    (hfound : (oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv &&
      oracleSearchSecond time target cardinality left right evm.accountMap evm.executionEnv) = false) :
    let first := oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv
    ∃ locals', ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      oracleSearchBody (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
      OracleSearchBindings locals' time target cardinality
        (if first then oracleSearchMiddle left right + ⟨1⟩ else left)
        (if first then right else UInt256.sub (oracleSearchMiddle left right) ⟨1⟩) := by
  dsimp only
  let frame := oracleSearchCompareFrame locals imms evm time target cardinality left right
  have hframe := oracleSearchCompareBindings locals imms evm time target cardinality left right h
  have hg := oracleSearchCompareGets locals imms evm time target cardinality left right
  have efirst := evalExpr_var_get (cfg := config) (frame := frame) (evm := evm) hg.1
  have efound := evalExpr_var_get (cfg := config) (frame := frame) (evm := evm) hg.2.1
  have ei := evalExpr_var_get (cfg := config) (frame := frame) (evm := evm) hg.2.2.1
  have eone : evalExpr? config frame evm (.intLit 1) =
      .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) := by simp only [evalExpr?, pure]; rfl
  have eprefix := oracleSearchComparePrefix locals imms evm time target cardinality left right h hn hc ht hinit
  cases hf : oracleSearchFirst time target cardinality left right evm.accountMap evm.executionEnv
  · let next := UInt256.sub (oracleSearchMiddle left right) ⟨1⟩
    refine ⟨frame.locals.insert "r" (.int (Int.ofNat next.toNat)), ?_, ?_⟩
    · rw [← List.take_append_drop 7 oracleSearchBody]
      apply execBlock_append_ok eprefix
      refine ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hfound] using efound) ExecBlock.nil) ?_
      refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
      · change evalExpr? config frame evm (.unary .not (.var "targetAtOrAfter")) = _
        rw [evalExpr?, efirst]
        simp only [hf, bind, EvalResult.bind, evalUnaryOp?]
        rfl
      · exact ExecBlock.consNormal
          (ExecStmt.assign (evalExpr_word_sub ei eone) (assignLocalVarBase_frame hframe.right)) ExecBlock.nil
    · exact hframe.set_right next
  · let next := oracleSearchMiddle left right + ⟨1⟩
    refine ⟨frame.locals.insert "l" (.int (Int.ofNat next.toNat)), ?_, ?_⟩
    · rw [← List.take_append_drop 7 oracleSearchBody]
      apply execBlock_append_ok eprefix
      refine ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hfound] using efound) ExecBlock.nil) ?_
      refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ?_) ExecBlock.nil
      · change evalExpr? config frame evm (.unary .not (.var "targetAtOrAfter")) = _
        rw [evalExpr?, efirst]
        simp only [hf, bind, EvalResult.bind, evalUnaryOp?]
        rfl
      · exact ExecBlock.consNormal
          (ExecStmt.assign (evalExpr_word_add ei eone) (assignLocalVarBase_frame hframe.left)) ExecBlock.nil
    · exact hframe.set_left next

end Benchmarks.UniswapV3.Pool
