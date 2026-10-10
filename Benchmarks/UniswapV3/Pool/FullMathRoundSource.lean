import Benchmarks.UniswapV3.Pool.FullMathSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def fullMathRoundValid (a b d : UInt256) : Prop :=
  fullMathValid a b d ∧
    (0 < fullMathProduct a b % d.toNat → (fullMathResult a b d).toNat < UInt256.size - 1)

noncomputable def fullMathRoundResult (a b d : UInt256) : UInt256 :=
  if 0 < fullMathProduct a b % d.toNat then fullMathResult a b d + ⟨1⟩
  else fullMathResult a b d

def fullMathRoundFunction : FunctionDecl := contract.functions[26]!

theorem fullMathRoundLookup :
    lookupCallable? contract "FullMath_mulDivRoundingUp" = some fullMathRoundFunction.toCallable := rfl

theorem fullMathRoundBind (a b d : UInt256) :
    bindParams? fullMathRoundFunction.params [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat),
      .int (Int.ofNat d.toNat)] = some (fullMathLocals a b d) := rfl

def fullMathRoundZeroFrame (imms : Store) (a b d : UInt256) : Frame :=
  {fullMathFrame imms a b d with locals := (fullMathLocals a b d).insert "result" (.int 0)}

def fullMathRoundCallFrame (imms : Store) (a b d : UInt256) : Frame :=
  {fullMathRoundZeroFrame imms a b d with
    locals := (fullMathRoundZeroFrame imms a b d).locals.insert "__c0"
      (.int (Int.ofNat (fullMathResult a b d).toNat))}

def fullMathRoundResultFrame (imms : Store) (a b d result : UInt256) : Frame :=
  {fullMathRoundCallFrame imms a b d with
    locals := (fullMathRoundCallFrame imms a b d).locals.insert "result"
      (.int (Int.ofNat result.toNat))}

def fullMathRoundIncrementFrame (imms : Store) (a b d : UInt256) : Frame :=
  {fullMathRoundResultFrame imms a b d (fullMathResult a b d) with
    locals := (fullMathRoundResultFrame imms a b d (fullMathResult a b d)).locals.insert "result"
      (.int (Int.ofNat (fullMathResult a b d + ⟨1⟩).toNat))}

noncomputable def fullMathRoundFinalFrame (imms : Store) (a b d : UInt256) : Frame :=
  if 0 < fullMathProduct a b % d.toNat then fullMathRoundIncrementFrame imms a b d
  else fullMathRoundResultFrame imms a b d (fullMathResult a b d)

theorem evalFullMathRoundArgs (imms : Store) (evm : EVM.State) (a b d : UInt256) :
    evalExprs? config (fullMathRoundZeroFrame imms a b d) evm
      [.var "a", .var "b", .var "denominator"] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int (Int.ofNat d.toNat)] := by
  simp [evalExprs?, evalExpr?, fullMathRoundZeroFrame, fullMathFrame, fullMathLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem fullMathRoundPrefix (imms : Store) (evm : EVM.State) (a b d : UInt256)
    (hv : fullMathValid a b d) :
    ExecBlock config (fullMathFrame imms a b d) evm (fullMathRoundFunction.body.take 3)
      (.ok (fullMathRoundResultFrame imms a b d (fullMathResult a b d)) evm) := by
  refine ExecBlock.consNormal (solm' := fullMathRoundZeroFrame imms a b d) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := fullMathRoundCallFrame imms a b d) (evm' := evm) ?_ ?_
  · exact internalCallFunctionReturn (callee := fullMathFunction)
      (caller := fullMathRoundZeroFrame imms a b d) (calleeEvm := evm)
      (calleeSolm := fullMathProductFrame imms a b d)
      (value := some [.int (Int.ofNat (fullMathResult a b d).toNat)])
      (evalFullMathRoundArgs imms evm a b d) fullMathLookup (fullMathBind a b d)
      (fullMathReturns imms evm a b d hv)
  refine ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat (fullMathResult a b d).toNat))
    ?_ ?_) ExecBlock.nil
  · exact evalExpr_var_get (by simp [fullMathRoundCallFrame])
  · exact assignLocalVarBase_frame (old := .int 0) (by
      simp [fullMathRoundCallFrame, fullMathRoundZeroFrame, Std.HashMap.getElem_insert])

theorem evalFullMathRoundCondition (imms : Store) (evm : EVM.State) (a b d : UInt256)
    (hd : 0 < d.toNat) :
    evalExpr? config (fullMathRoundResultFrame imms a b d (fullMathResult a b d)) evm
      (.binary .gt (.binary .mod (.binary .mul (.var "a") (.var "b")) (.var "denominator"))
        (.intLit 0)) = .ok (.bool (decide (0 < fullMathProduct a b % d.toNat))) := by
  simp [evalExpr?, fullMathRoundResultFrame, fullMathRoundCallFrame, fullMathRoundZeroFrame,
    fullMathFrame, fullMathLocals, fullMathProduct, Std.HashMap.getElem_insert, EvalResult.ofOption,
    evalBinaryOp?, bind, EvalResult.bind, Nat.ne_of_gt hd]
  rw [← Int.natCast_mul, ← Int.natCast_emod]
  exact Int.ofNat_lt

theorem evalFullMathRoundGuard (imms : Store) (evm : EVM.State) (a b d : UInt256) :
    evalExpr? config (fullMathRoundResultFrame imms a b d (fullMathResult a b d)) evm
      (.binary .lt (.var "result") (.intLit (Int.ofNat (UInt256.size - 1)))) =
      .ok (.bool (decide ((fullMathResult a b d).toNat < UInt256.size - 1))) := by
  simp [evalExpr?, fullMathRoundResultFrame, EvalResult.ofOption,
    evalBinaryOp?, bind, EvalResult.bind]

theorem fullMathRoundIncrement (imms : Store) (evm : EVM.State) (a b d : UInt256) :
    ExecStmt config (fullMathRoundResultFrame imms a b d (fullMathResult a b d)) evm
      (.assign .localVar ⟨"result", []⟩
        (.cast (.binary .add (.var "result") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩)))))
      (.ok (fullMathRoundIncrementFrame imms a b d) evm) := by
  apply ExecStmt.assign (value := .int (Int.ofNat (fullMathResult a b d + ⟨1⟩).toNat))
  · exact evalExpr_word_add (a := fullMathResult a b d) (b := ⟨1⟩)
      (frame := fullMathRoundResultFrame imms a b d (fullMathResult a b d)) (evm := evm)
      (evalExpr_var_get (by simp [fullMathRoundResultFrame]))
      (by simp only [evalExpr?, pure]; rfl)
  · have hs := assignLocalVarBase_frame (cfg := config) (name := "result")
        (frame := fullMathRoundResultFrame imms a b d (fullMathResult a b d))
        (evm := evm) (value := .int (Int.ofNat (fullMathResult a b d + ⟨1⟩).toNat))
        (old := .int (Int.ofNat (fullMathResult a b d).toNat))
        (by simp [fullMathRoundResultFrame])
    simpa only [fullMathRoundIncrementFrame] using hs

theorem fullMathRoundReturns (imms : Store) (evm : EVM.State) (a b d : UInt256)
    (hv : fullMathRoundValid a b d) :
    ExecFuncBody config (fullMathFrame imms a b d) evm fullMathRoundFunction.body
      (.returned (fullMathRoundFinalFrame imms a b d) evm
        (some [.int (Int.ofNat (fullMathRoundResult a b d).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 3 fullMathRoundFunction.body]
  apply execBlock_append_ok (fullMathRoundPrefix imms evm a b d hv.1)
  by_cases hr : 0 < fullMathProduct a b % d.toNat
  · simp only [fullMathRoundResult, fullMathRoundFinalFrame, if_pos hr]
    refine ExecBlock.consNormal
      (solm' := fullMathRoundIncrementFrame imms a b d)
      (evm' := evm) (ExecStmt.iteTrue ?_ ?_) ?_
    · simpa only [hr, decide_true] using evalFullMathRoundCondition imms evm a b d
        (fullMath_denominator_pos hv.1)
    · refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
        (ExecBlock.consNormal (fullMathRoundIncrement imms evm a b d) ExecBlock.nil)
      simpa only [hv.2 hr, decide_true] using evalFullMathRoundGuard imms evm a b d
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp [evalExprs?, evalExpr?, fullMathRoundIncrementFrame, fullMathRoundResultFrame, EvalResult.ofOption,
        bind, EvalResult.bind, pure]
  · simp only [fullMathRoundResult, fullMathRoundFinalFrame, if_neg hr]
    refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
    · simpa only [hr, decide_false] using evalFullMathRoundCondition imms evm a b d
        (fullMath_denominator_pos hv.1)
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp [evalExprs?, evalExpr?, fullMathRoundResultFrame, EvalResult.ofOption,
        bind, EvalResult.bind, pure]

theorem fullMathRoundReverts (imms : Store) (evm : EVM.State) (a b d : UInt256)
    (hv : ¬ fullMathRoundValid a b d) :
    ExecFuncBody config (fullMathFrame imms a b d) evm fullMathRoundFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hbase : fullMathValid a b d
  · rw [← List.take_append_drop 3 fullMathRoundFunction.body]
    apply execBlock_append_ok (fullMathRoundPrefix imms evm a b d hbase)
    have hr : 0 < fullMathProduct a b % d.toNat := by
      by_contra h
      exact hv ⟨hbase, fun hr ↦ False.elim (h hr)⟩
    have hmax : ¬ (fullMathResult a b d).toNat < UInt256.size - 1 :=
      fun h ↦ hv ⟨hbase, fun _ ↦ h⟩
    apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
    · simpa only [hr, decide_true] using evalFullMathRoundCondition imms evm a b d
        (fullMath_denominator_pos hbase)
    · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      simpa only [hmax, decide_false] using evalFullMathRoundGuard imms evm a b d
  · refine ExecBlock.consNormal (solm' := fullMathRoundZeroFrame imms a b d) (evm' := evm)
      (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
    apply ExecBlock.consRevert
    exact internalCallFunctionRevert (callee := fullMathFunction)
      (evalFullMathRoundArgs imms evm a b d) fullMathLookup (fullMathBind a b d)
      (fullMathReverts imms evm a b d hbase)

end Benchmarks.UniswapV3.Pool
