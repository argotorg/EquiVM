import Benchmarks.UniswapV3.Pool.NextPriceCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextPriceChoiceReturns (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (ha : a.Fits) (hv : nextPriceCalleeValid input a) :
    ExecStmt config (nextPriceReadyFrame imms input a) evm (nextPriceFunction input).body[4]!
      (.ok (nextPriceResultFrame imms input a) evm) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (nextPriceReadyGet imms input a).2.2.2.1
  have hc := nextPriceCallReturns imms evm input a ha hv
  have hs := nextPriceCallAssign imms evm input a
  cases hz : a.zeroForOne
  · cases input <;> apply ExecStmt.iteFalse (by simpa only [hz] using he)
    all_goals
      exact ExecBlock.consNormal
        (by simpa only [nextPriceOne, nextSqrtName, nextPriceCallName, nextPriceCallArgs,
          nextPriceAmountName, hz, Bool.not_false, Bool.false_eq_true, if_false, if_true] using hc)
        (ExecBlock.consNormal (by simpa only [nextPriceCallName, hz,
          Bool.false_eq_true, if_false] using hs) ExecBlock.nil)
  · cases input <;> apply ExecStmt.iteTrue (by simpa only [hz] using he)
    all_goals
      exact ExecBlock.consNormal
        (by simpa only [nextPriceOne, nextSqrtName, nextPriceCallName, nextPriceCallArgs,
          nextPriceAmountName, hz, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hc)
        (ExecBlock.consNormal (by simpa only [nextPriceCallName, hz, if_true] using hs)
          ExecBlock.nil)

theorem nextPriceChoiceReverts (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (hv : ¬nextPriceCalleeValid input a) :
    ExecStmt config (nextPriceReadyFrame imms input a) evm (nextPriceFunction input).body[4]!
      .reverted := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (nextPriceReadyGet imms input a).2.2.2.1
  have hc := nextPriceCallReverts imms evm input a hv
  cases hz : a.zeroForOne
  · cases input <;> apply ExecStmt.iteFalse (by simpa only [hz] using he)
    all_goals
      apply ExecBlock.consRevert
      simpa only [nextPriceOne, nextSqrtName, nextPriceCallName, nextPriceCallArgs,
        nextPriceAmountName, hz, Bool.not_false, Bool.false_eq_true, if_false, if_true] using hc
  · cases input <;> apply ExecStmt.iteTrue (by simpa only [hz] using he)
    all_goals
      apply ExecBlock.consRevert
      simpa only [nextPriceOne, nextSqrtName, nextPriceCallName, nextPriceCallArgs,
        nextPriceAmountName, hz, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hc

theorem nextPriceReturns (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (ha : a.Fits) (hv : nextPriceValid input a) :
    ExecFuncBody config (nextPriceFrame imms input a) evm (nextPriceFunction input).body
      (.returned (nextPriceResultFrame imms input a) evm
        (some [.int (Int.ofNat (nextPriceResult input a).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 4 (nextPriceFunction input).body]
  apply execBlock_append_ok (nextPricePrefixSource imms evm input a hv.1)
  have hc := nextPriceChoiceReturns imms evm input a ha hv.2
  have he : evalExpr? config (nextPriceResultFrame imms input a) evm (.var "__cond2") =
      .ok (.int (Int.ofNat (nextPriceResult input a).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  cases input
  all_goals
    exact ExecBlock.consNormal hc (ExecBlock.consReturn (ExecStmt.return
      (by simp only [evalExprs?, he, bind, EvalResult.bind, pure])))

theorem nextPriceReverts (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (hv : ¬nextPriceValid input a) :
    ExecFuncBody config (nextPriceFrame imms input a) evm (nextPriceFunction input).body
      .reverted := by
  by_cases hg : nextPriceGuard a
  · apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 4 (nextPriceFunction input).body]
    apply execBlock_append_ok (nextPricePrefixSource imms evm input a hg)
    have hc := nextPriceChoiceReverts imms evm input a (fun h ↦ hv ⟨hg, h⟩)
    cases input <;> exact ExecBlock.consRevert hc
  · exact nextPriceGuardReverts imms evm input a hg

end Benchmarks.UniswapV3.Pool
