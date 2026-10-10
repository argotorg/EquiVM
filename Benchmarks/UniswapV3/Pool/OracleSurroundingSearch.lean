import Benchmarks.UniswapV3.Pool.OracleSurroundingCompare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingOldReverts (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (hin : index.toNat < 65535)
    (ht : target.toNat < 2 ^ 32) (hn : cardinality.toNat ≠ 0)
    (hc : cardinality.toNat < 2 ^ 16)
    (hf : oracleSurroundingFirst time target index evm.accountMap evm.executionEnv = false)
    (ho : oracleSurroundingOldEnough time target index cardinality
      evm.accountMap evm.executionEnv = false) :
    ExecFuncBody config (oracleSurroundingFrame imms time target tick index liquidity cardinality)
      evm oracleSurroundingFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 8 oracleSurroundingFunction.body]
  apply execBlock_append_ok
    (oracleSurroundingComparePrefix imms evm time target tick index liquidity cardinality
      hin ht hn hc hf)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  exact evalExpr_var_get (by simp [oracleSurroundingCompareFrame, ho])

theorem oracleSurroundingSearchReturns (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (before after : OracleObservation)
    (hin : index.toNat < 65535) (ht : target.toNat < 2 ^ 32) (hn : cardinality.toNat ≠ 0)
    (hc : cardinality.toNat < 2 ^ 16)
    (hf : oracleSurroundingFirst time target index evm.accountMap evm.executionEnv = false)
    (ho : oracleSurroundingOldEnough time target index cardinality
      evm.accountMap evm.executionEnv = true)
    (hrun : OracleSearchRun time target cardinality evm.accountMap evm.executionEnv
      (oracleSearchLeft index cardinality) (oracleSearchRight index cardinality) before after) :
    ∃ frame, ExecFuncBody config
      (oracleSurroundingFrame imms time target tick index liquidity cardinality)
      evm oracleSurroundingFunction.body
        (.returned frame evm (some [before.value, after.value])) := by
  let f := oracleSurroundingCompareFrame imms evm time target tick index liquidity cardinality
  have hg := oracleSurroundingCompareGets imms evm time target tick index liquidity cardinality
  have hargs : evalExprs? config f evm
      [.var "time", .var "target", .var "index", .var "cardinality"] =
      .ok [.int (Int.ofNat time.toNat), .int (Int.ofNat target.toNat),
        .int (Int.ofNat index.toNat), .int (Int.ofNat cardinality.toNat)] := by
    have et := evalExpr_var_get (cfg := config) (evm := evm) (frame := f) hg.1
    have eg := evalExpr_var_get (cfg := config) (evm := evm) (frame := f) hg.2.1
    have ei := evalExpr_var_get (cfg := config) (evm := evm) (frame := f) hg.2.2.1
    have ec := evalExpr_var_get (cfg := config) (evm := evm) (frame := f) hg.2.2.2
    simp only [evalExprs?, et, eg, ei, ec, bind, EvalResult.bind, pure]
  obtain ⟨calleeFrame, hbody⟩ := oracleSearchReturns imms evm time target index cardinality
    before after hn hc ht hrun
  have hcall := internalCallFunctionReturn (cfg := config) (caller := f) (evm := evm)
    (callee := oracleSearchFunction) (calleeSolm := calleeFrame)
    (retVar := "__c3") (value := some [before.value, after.value])
    hargs oracleSearchLookup (oracleSearchBind time target index cardinality) hbody
  let ft := resumeAfterInternalCall f "__c3" (some [before.value, after.value])
  refine ⟨ft, ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 8 oracleSurroundingFunction.body]
  apply execBlock_append_ok
    (oracleSurroundingComparePrefix imms evm time target tick index liquidity cardinality
      hin ht hn hc hf)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalExpr_var_get (by simp [oracleSurroundingCompareFrame, ho])
  refine ExecBlock.consNormal hcall (ExecBlock.consReturn (ExecStmt.return ?_))
  change evalExprs? config ft evm [.tupleGet (.var "__c3") 0, .tupleGet (.var "__c3") 1] = _
  have er : evalExpr? config ft evm (.var "__c3") =
      .ok (.tuple [before.value, after.value]) := evalExpr_var_get (by
    simp [ft, resumeAfterInternalCall, collapseReturns])
  simp only [evalExprs?, evalExpr?, er, bind, EvalResult.bind, tupleGetValue?, pure]
  rfl

end Benchmarks.UniswapV3.Pool
