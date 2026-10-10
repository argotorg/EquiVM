import Benchmarks.UniswapV3.Pool.OracleSearchBindings

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleStoredTimestamp_lt (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (oracleStoredObservation index σ I).timestamp.toNat < 2 ^ 32 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

def oracleSearchBefore (left right cardinality : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    OracleObservation :=
  oracleStoredObservation (UInt256.mod (oracleSearchMiddle left right) cardinality) σ I

def oracleSearchAfter (left right cardinality : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    OracleObservation :=
  oracleStoredObservation (UInt256.mod (oracleSearchMiddle left right + ⟨1⟩) cardinality) σ I

def oracleSearchReadFrame (locals imms : Store) (evm : EVM.State)
    (left right cardinality : UInt256) : Frame :=
  {contract := contract, immutables := imms,
   locals := (locals.insert "i" (.int (Int.ofNat (oracleSearchMiddle left right).toNat))).insert
    "beforeOrAt" (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).value}

theorem oracleSearchReadBindings (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right) :
    OracleSearchBindings (oracleSearchReadFrame locals imms evm left right cardinality).locals
      time target cardinality left right :=
  (h.insert_aux "i" _ (by decide)).insert_aux "beforeOrAt" _ (by decide)

theorem oracleSearchReadPrefix (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (oracleSearchBody.take 2)
      (.ok (oracleSearchReadFrame locals imms evm left right cardinality) evm) := by
  let mid := oracleSearchMiddle left right
  let fm : Frame :=
    { contract := contract
      immutables := imms
      locals := locals.insert "i" (.int (Int.ofNat mid.toNat)) }
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.binary .div (.cast (.binary .add (.var "l") (.var "r"))
        (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 2)) =
      .ok (.int (Int.ofNat mid.toNat)) := by
    exact evalExpr_word_div (evalExpr_word_add (evalExpr_var_get h.left) (evalExpr_var_get h.right))
      (b := ⟨2⟩) (by simp only [evalExpr?, pure]; rfl) (by decide)
  obtain ⟨oldI, hi⟩ := h.index
  refine ExecBlock.consNormal (solm' := fm) (evm' := evm)
    (ExecStmt.assign he (assignLocalVarBase_frame hi)) ?_
  have hfm := h.insert_aux "i" (.int (Int.ofNat mid.toNat)) (by decide)
  have hr : evalExpr? config fm evm (.binary .mod (.var "i") (.var "cardinality")) =
      .ok (.int (Int.ofNat (UInt256.mod mid cardinality).toNat)) :=
    evalExpr_word_mod (evalExpr_var_get (by simp [fm]))
      (evalExpr_var_get hfm.cardinality) hn
  obtain ⟨oldBefore, hbefore⟩ := hfm.beforeOrAt
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalOracleObservationExpr _ _ _ _ _ hfm.base hr
      (oracleSearchRemainder_lt mid cardinality hn hc)) (assignLocalVarBase_frame hbefore))
    ExecBlock.nil

theorem evalOracleSearchInitialized (locals imms : Store) (evm : EVM.State)
    (left right cardinality : UInt256) :
    evalExpr? config (oracleSearchReadFrame locals imms evm left right cardinality) evm
      (.unary .not (.field (.var "beforeOrAt") "initialized")) =
      .ok (.bool (!(oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).initialized)) := by
  simp [evalExpr?, oracleSearchReadFrame, OracleObservation.value, evalUnaryOp?,
    EvalResult.ofOption, lookupField?, lookupAssoc, bind, EvalResult.bind]

theorem oracleSearchUninitialized (locals imms : Store) (evm : EVM.State)
    (time target cardinality left right : UInt256)
    (h : OracleSearchBindings locals time target cardinality left right)
    (hn : cardinality.toNat ≠ 0) (hc : cardinality.toNat < 2 ^ 16)
    (hinit : (oracleSearchBefore left right cardinality evm.accountMap evm.executionEnv).initialized = false) :
    ∃ locals', ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      oracleSearchBody (.continue {contract := contract, locals := locals', immutables := imms} evm) ∧
      OracleSearchBindings locals' time target cardinality (oracleSearchMiddle left right + ⟨1⟩) right := by
  let fr := oracleSearchReadFrame locals imms evm left right cardinality
  let next := oracleSearchMiddle left right + ⟨1⟩
  let final := fr.locals.insert "l" (.int (Int.ofNat next.toNat))
  have hfr := oracleSearchReadBindings locals imms evm time target cardinality left right h
  refine ⟨final, ?_, hfr.set_left next⟩
  rw [← List.take_append_drop 2 oracleSearchBody]
  apply execBlock_append_ok (oracleSearchReadPrefix locals imms evm time target cardinality left right h hn hc)
  refine ExecBlock.consContinue (ExecStmt.iteTrue ?_ ?_)
  · simpa only [hinit, Bool.not_false] using evalOracleSearchInitialized locals imms evm left right cardinality
  · refine ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat next.toNat))
      ?_ (assignLocalVarBase_frame hfr.left)) ?_
    · exact evalExpr_word_add (b := ⟨1⟩)
        (evalExpr_var_get (by simp [oracleSearchReadFrame, Std.HashMap.getElem_insert]))
        (by simp only [evalExpr?, pure]; rfl)
    · exact ExecBlock.consContinue ExecStmt.continue

end Benchmarks.UniswapV3.Pool
