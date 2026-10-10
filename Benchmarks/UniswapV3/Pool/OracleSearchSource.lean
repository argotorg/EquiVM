import Benchmarks.UniswapV3.Pool.OracleSearchStep

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

inductive OracleSearchRun (time target cardinality : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 → UInt256 → OracleObservation → OracleObservation → Prop where
  | found {left right} :
      (oracleSearchBefore left right cardinality σ I).initialized = true →
      (oracleSearchFirst time target cardinality left right σ I &&
        oracleSearchSecond time target cardinality left right σ I) = true →
      OracleSearchRun time target cardinality σ I left right
        (oracleSearchBefore left right cardinality σ I) (oracleSearchAfter left right cardinality σ I)
  | uninitialized {left right beforeOrAt atOrAfter} :
      (oracleSearchBefore left right cardinality σ I).initialized = false →
      OracleSearchRun time target cardinality σ I (oracleSearchMiddle left right + ⟨1⟩) right
        beforeOrAt atOrAfter →
      OracleSearchRun time target cardinality σ I left right beforeOrAt atOrAfter
  | advance {left right beforeOrAt atOrAfter} :
      (oracleSearchBefore left right cardinality σ I).initialized = true →
      (oracleSearchFirst time target cardinality left right σ I &&
        oracleSearchSecond time target cardinality left right σ I) = false →
      OracleSearchRun time target cardinality σ I
        (if oracleSearchFirst time target cardinality left right σ I then
          oracleSearchMiddle left right + ⟨1⟩ else left)
        (if oracleSearchFirst time target cardinality left right σ I then
          right else UInt256.sub (oracleSearchMiddle left right) ⟨1⟩)
        beforeOrAt atOrAfter →
      OracleSearchRun time target cardinality σ I left right beforeOrAt atOrAfter

theorem oracleSearchLoopOfRun (imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256) (beforeOrAt atOrAfter : OracleObservation)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16)
    (ht : target.toNat < 2 ^ 32)
    (hrun : OracleSearchRun time target cardinality evm.accountMap evm.executionEnv
      left right beforeOrAt atOrAfter) :
    ∀ locals, OracleSearchBindings locals time target cardinality left right →
      ∃ locals', ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
        (.while (.boolLit true) oracleSearchBody)
        (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
        locals'.get? "beforeOrAt" = some beforeOrAt.value ∧
        locals'.get? "atOrAfter" = some atOrAfter.value := by
  induction hrun with
  | @found left right hinit hfound =>
      intro locals h
      have hs := oracleSearchFound locals imms evm time target cardinality left right h hn hc ht hinit hfound
      have hg := oracleSearchCompareGets locals imms evm time target cardinality left right
      exact ⟨_, ExecStmt.whileBreak (by simp only [evalExpr?, pure]) hs, hg.2.2.2⟩
  | @uninitialized left right beforeOrAt atOrAfter hinit hrun ih =>
      intro locals h
      obtain ⟨locals1, hs, h1⟩ := oracleSearchUninitialized locals imms evm time target cardinality
        left right h hn hc hinit
      obtain ⟨locals2, hloop, hbefore, hafter⟩ := ih locals1 h1
      exact ⟨locals2, ExecStmt.whileContinue (by simp only [evalExpr?, pure]) hs hloop, hbefore, hafter⟩
  | @advance left right beforeOrAt atOrAfter hinit hfound hrun ih =>
      intro locals h
      obtain ⟨locals1, hs, h1⟩ := oracleSearchAdvance locals imms evm time target cardinality
        left right h hn hc ht hinit hfound
      obtain ⟨locals2, hloop, hbefore, hafter⟩ := ih locals1 h1
      exact ⟨locals2, ExecStmt.whileTrue (by simp only [evalExpr?, pure]) hs hloop, hbefore, hafter⟩

theorem oracleSearchReturns (imms : Store) (evm : EVM.State)
    (time target index cardinality : UInt256) (beforeOrAt atOrAfter : OracleObservation)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16)
    (ht : target.toNat < 2 ^ 32)
    (hrun : OracleSearchRun time target cardinality evm.accountMap evm.executionEnv
      (oracleSearchLeft index cardinality) (oracleSearchRight index cardinality) beforeOrAt atOrAfter) :
    ∃ frame, ExecFuncBody config (oracleSearchFrame imms time target index cardinality) evm
      oracleSearchFunction.body (.returned frame evm (some [beforeOrAt.value, atOrAfter.value])) := by
  obtain ⟨locals, hloop, hb, ha⟩ := oracleSearchLoopOfRun imms evm time target cardinality
    _ _ beforeOrAt atOrAfter hn hc ht hrun _ (oracleSearchReadyBindings imms time target index cardinality)
  refine ⟨{contract := contract, locals := locals, immutables := imms}, ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 5 oracleSearchFunction.body]
  apply execBlock_append_ok (oracleSearchPrefix imms evm time target index cardinality hn)
  refine ExecBlock.consNormal hloop (ExecBlock.consReturn (ExecStmt.return ?_))
  have eb := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hb
  have ea := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) ha
  simp only [evalExprs?, eb, ea, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
