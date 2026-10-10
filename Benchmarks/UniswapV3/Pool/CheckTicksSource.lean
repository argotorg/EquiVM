import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def checkTicksFunction : FunctionDecl := contract.functions[2]!

theorem checkTicksLookup :
    lookupCallable? contract "checkTicks" = some checkTicksFunction.toCallable := rfl

def checkTicksLocals (lower upper : Int) : Store :=
  ((∅ : Store).insert "tickUpper" (.int upper)).insert "tickLower" (.int lower)

def checkTicksFrame (imms : Store) (lower upper : Int) : Frame :=
  { contract := contract, locals := checkTicksLocals lower upper, immutables := imms }

def validTicks (lower upper : Int) : Prop := lower < upper ∧ -887272 ≤ lower ∧ upper ≤ 887272

theorem checkTicksBind (lower upper : Int) :
    bindParams? checkTicksFunction.params [.int lower, .int upper] = some (checkTicksLocals lower upper) := rfl

theorem evalCheckTicksOrder (imms : Store) (evm : EVM.State) (lower upper : Int) :
    evalExpr? config (checkTicksFrame imms lower upper) evm
      (.binary .lt (.var "tickLower") (.var "tickUpper")) = .ok (.bool (decide (lower < upper))) := by
  simp [evalExpr?, checkTicksFrame, checkTicksLocals, Std.HashMap.getElem_insert,
    EvalResult.ofOption, evalBinaryOp?, EvalResult.bind, bind]

theorem evalCheckTicksLower (imms : Store) (evm : EVM.State) (lower upper : Int) :
    evalExpr? config (checkTicksFrame imms lower upper) evm
      (.binary .ge (.var "tickLower") (.unary .neg (.intLit 887272))) =
      .ok (.bool (decide (-887272 ≤ lower))) := by
  simp [evalExpr?, checkTicksFrame, checkTicksLocals, Std.HashMap.getElem_insert,
    EvalResult.ofOption, evalBinaryOp?, evalUnaryOp?, EvalResult.bind, bind, pure]

theorem evalCheckTicksUpper (imms : Store) (evm : EVM.State) (lower upper : Int) :
    evalExpr? config (checkTicksFrame imms lower upper) evm
      (.binary .le (.var "tickUpper")
        (.cast (.binary .sub (.intLit 0) (.unary .neg (.intLit 887272)))
          (.elem (.int (.sint ⟨24, by decide⟩))))) =
      .ok (.bool (decide (upper ≤ 887272))) := by
  simp [evalExpr?, checkTicksFrame, checkTicksLocals, Std.HashMap.getElem_insert,
    EvalResult.ofOption, evalBinaryOp?, evalUnaryOp?, castValue?, normalizeInt,
    EVM.twoPow, EvalResult.bind, bind, pure]

theorem checkTicksReturns (imms : Store) (evm : EVM.State) (lower upper : Int)
    (h : validTicks lower upper) :
    ExecFuncBody config (checkTicksFrame imms lower upper) evm checkTicksFunction.body
      (.returned (checkTicksFrame imms lower upper) evm none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [h.1, decide_true] using evalCheckTicksOrder imms evm lower upper
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [h.2.1, decide_true] using evalCheckTicksLower imms evm lower upper
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [h.2.2, decide_true] using evalCheckTicksUpper imms evm lower upper

theorem checkTicksReverts (imms : Store) (evm : EVM.State) (lower upper : Int)
    (h : ¬ validTicks lower upper) :
    ExecFuncBody config (checkTicksFrame imms lower upper) evm checkTicksFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases ho : lower < upper
  · refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [ho, decide_true] using evalCheckTicksOrder imms evm lower upper
    by_cases hl : -887272 ≤ lower
    · refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · simpa only [hl, decide_true] using evalCheckTicksLower imms evm lower upper
      refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      have hu : ¬ upper ≤ 887272 := fun hu => h ⟨ho, hl, hu⟩
      simpa only [hu, decide_false] using evalCheckTicksUpper imms evm lower upper
    · refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      simpa only [hl, decide_false] using evalCheckTicksLower imms evm lower upper
  · refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    simpa only [ho, decide_false] using evalCheckTicksOrder imms evm lower upper

end Benchmarks.UniswapV3.Pool
