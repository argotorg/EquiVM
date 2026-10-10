import Benchmarks.UniswapV3.Pool.OracleTransformSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleAdjusted (time value : UInt256) : Nat :=
  if time.toNat < value.toNat then value.toNat else value.toNat + 2 ^ 32

def oracleLte (time a b : UInt256) : Bool :=
  if a.toNat ≤ time.toNat ∧ b.toNat ≤ time.toNat then decide (a.toNat ≤ b.toNat)
  else decide (oracleAdjusted time a ≤ oracleAdjusted time b)

def oracleLteFunction : FunctionDecl := contract.functions[40]!

theorem oracleLteLookup :
    lookupCallable? contract "Oracle_lte" = some oracleLteFunction.toCallable := rfl

def oracleLteLocals (time a b : UInt256) : Store :=
  (((∅ : Store).insert "b" (.int (Int.ofNat b.toNat))).insert "a"
    (.int (Int.ofNat a.toNat))).insert "time" (.int (Int.ofNat time.toNat))

def oracleLteFrame (imms : Store) (time a b : UInt256) : Frame :=
  {contract := contract, locals := oracleLteLocals time a b, immutables := imms}

theorem oracleLteBind (time a b : UInt256) :
    bindParams? oracleLteFunction.params
      [.int (Int.ofNat time.toNat), .int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat)] =
      some (oracleLteLocals time a b) := rfl

def oracleAdjustedExpr (name : Ident) : Expr :=
  .ite (.binary .gt (.var name) (.var "time")) (.var name)
    (.cast (.binary .add (.var name) (.intLit 4294967296))
      (.elem (.int (.uint ⟨40, by decide⟩))))

theorem evalOracleAdjusted {frame : Frame} {evm : EVM.State} {name : Ident}
    (time value : UInt256)
    (ht : frame.locals.get? "time" = some (.int (Int.ofNat time.toNat)))
    (hv : frame.locals.get? name = some (.int (Int.ofNat value.toNat)))
    (hb : value.toNat < 2 ^ 32) :
    evalExpr? config frame evm (oracleAdjustedExpr name) =
      .ok (.int (Int.ofNat (oracleAdjusted time value))) := by
  have hc : normalizeInt (.uint ⟨40, by decide⟩)
      (Int.ofNat value.toNat + 4294967296) = Int.ofNat value.toNat + 4294967296 :=
    normalizeInt_uint_eq_self ⟨40, by decide⟩ _ (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [EVM.twoPow, Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat]
          omega)
  rw [Std.HashMap.get?_eq_getElem?] at ht hv
  simp only [Int.ofNat_eq_natCast] at hc
  by_cases h : time.toNat < value.toNat
  · simp [oracleAdjustedExpr, evalExpr?, ht, hv, EvalResult.ofOption, evalBinaryOp?,
      bind, EvalResult.bind, castValue?, oracleAdjusted, h, hc]
  · simp [oracleAdjustedExpr, evalExpr?, ht, hv, EvalResult.ofOption, evalBinaryOp?,
      bind, EvalResult.bind, castValue?, oracleAdjusted, h, hc]

theorem evalOracleLteCondition (imms : Store) (evm : EVM.State) (time a b : UInt256) :
    evalExpr? config (oracleLteFrame imms time a b) evm
      (.binary .and (.binary .le (.var "a") (.var "time"))
        (.binary .le (.var "b") (.var "time"))) =
      .ok (.bool (decide (a.toNat ≤ time.toNat ∧ b.toNat ≤ time.toNat))) := by
  rw [Bool.decide_and]
  apply evalExpr_bool_and <;>
    simp [evalExpr?, oracleLteFrame, oracleLteLocals, Std.HashMap.getElem_insert,
      EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem oracleLteReturns (imms : Store) (evm : EVM.State) (time a b : UInt256)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    ∃ frame, ExecFuncBody config (oracleLteFrame imms time a b) evm oracleLteFunction.body
      (.returned frame evm (some [.bool (oracleLte time a b)])) := by
  by_cases h : a.toNat ≤ time.toNat ∧ b.toNat ≤ time.toNat
  · refine ⟨oracleLteFrame imms time a b, ExecFuncBody.execBlockRet ?_⟩
    refine ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
    · simpa only [h, decide_true] using evalOracleLteCondition imms evm time a b
    · apply ExecBlock.consReturn
      apply ExecStmt.return
      simp [evalExprs?, evalExpr?, oracleLteFrame, oracleLteLocals,
        Std.HashMap.getElem_insert, EvalResult.ofOption, evalBinaryOp?, bind,
        EvalResult.bind, pure, oracleLte, h]
  · let fa := { (oracleLteFrame imms time a b) with
        locals := (oracleLteLocals time a b).insert "aAdjusted"
          (.int (Int.ofNat (oracleAdjusted time a)))}
    let fb := { fa with
      locals := fa.locals.insert "bAdjusted" (.int (Int.ofNat (oracleAdjusted time b))) }
    refine ⟨fb, ExecFuncBody.execBlockRet ?_⟩
    refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
    · simpa only [h, decide_false] using evalOracleLteCondition imms evm time a b
    refine ExecBlock.consNormal (solm' := fa) (evm' := evm) (ExecStmt.letDecl ?_) ?_
    · exact evalOracleAdjusted time a
        (by simp [oracleLteFrame, oracleLteLocals])
        (by simp [oracleLteFrame, oracleLteLocals, Std.HashMap.getElem_insert]) ha
    refine ExecBlock.consNormal (solm' := fb) (evm' := evm) (ExecStmt.letDecl ?_) ?_
    · exact evalOracleAdjusted time b
        (by simp [fa, oracleLteLocals, Std.HashMap.getElem_insert])
        (by simp [fa, oracleLteLocals, Std.HashMap.getElem_insert]) hb
    apply ExecBlock.consReturn
    apply ExecStmt.return
    simp [evalExprs?, evalExpr?, fb, fa, Std.HashMap.getElem_insert,
      EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind, pure, oracleLte, h]

theorem oracleLteCall (locals imms : Store) (evm : EVM.State) (args : List Expr) (name : Ident)
    (time a b : UInt256)
    (hargs : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.int (Int.ofNat time.toNat), .int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat)])
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "Oracle_lte" args name)
      (.ok
        { contract := contract
          locals := locals.insert name (.bool (oracleLte time a b))
          immutables := imms } evm) := by
  obtain ⟨frame, hbody⟩ := oracleLteReturns imms evm time a b ha hb
  exact internalCallFunctionReturn (callee := oracleLteFunction) (calleeSolm := frame)
    (value := some [.bool (oracleLte time a b)]) hargs oracleLteLookup (oracleLteBind time a b) hbody

end Benchmarks.UniswapV3.Pool
