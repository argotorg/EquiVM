import Benchmarks.UniswapV3.Pool.SignedAmountDeltaCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem signedAmountDeltaChoiceSource (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) (hv : signedAmountDeltaValid second a) :
    ExecStmt config (signedAmountDeltaReadyFrame imms second a) evm
      (signedAmountDeltaFunction second).body[2]!
      (.ok (signedAmountDeltaReturnFrame imms second a) evm) := by
  have hg := evalSignedAmountDeltaGuard imms evm second a
  have hc := signedAmountDeltaCallSource imms evm second a hfit hv
  have hs := signedAmountDeltaCastSource imms evm second a hfit hv
  have ha := signedAmountDeltaAssignSource imms evm second a hfit hv
  have hb := ExecBlock.consNormal hc (ExecBlock.consNormal hs (ExecBlock.consNormal ha ExecBlock.nil))
  by_cases hn : a.liquidity < 0
  · have hp : ¬0 ≤ a.liquidity := by omega
    rw [decide_eq_true hn] at hg
    cases second <;> apply ExecStmt.iteTrue hg
    all_goals
      simpa only [signedAmountDeltaCallArgs, signedAmountDeltaCallName, signedAmountDeltaCastName,
        signedAmountDeltaAssignExpr, if_pos hn, decide_eq_false hp, amountDeltaName,
        Bool.false_eq_true, if_false, if_true] using hb
  · have hp : 0 ≤ a.liquidity := by omega
    rw [decide_eq_false hn] at hg
    cases second <;> apply ExecStmt.iteFalse hg
    all_goals
      simpa only [signedAmountDeltaCallArgs, signedAmountDeltaCallName, signedAmountDeltaCastName,
        signedAmountDeltaAssignExpr, if_neg hn, decide_eq_true hp, amountDeltaName,
        Bool.false_eq_true, if_false, if_true] using hb

theorem signedAmountDeltaReturns (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) (hv : signedAmountDeltaValid second a) :
    ExecFuncBody config (signedAmountDeltaFrame imms a) evm (signedAmountDeltaFunction second).body
      (.returned (signedAmountDeltaReturnFrame imms second a) evm
        (some [.int (signedAmountDeltaResult second a)])) := by
  have ht : (signedAmountDeltaFunction second).body.drop 2 =
      [(signedAmountDeltaFunction second).body[2]!, .return [.var "__cond4"]] := by
    cases second <;> rfl
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 2 (signedAmountDeltaFunction second).body, ht]
  apply execBlock_append_ok (signedAmountDeltaPrefixSource imms evm second a)
  refine ExecBlock.consNormal (signedAmountDeltaChoiceSource imms evm second a hfit hv) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have he : evalExpr? config (signedAmountDeltaReturnFrame imms second a) evm (.var "__cond4") =
      .ok (.int (signedAmountDeltaResult second a)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem signedAmountDeltaReverts (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) (hv : ¬signedAmountDeltaValid second a) :
    ExecFuncBody config (signedAmountDeltaFrame imms a) evm
      (signedAmountDeltaFunction second).body .reverted := by
  have ht : (signedAmountDeltaFunction second).body.drop 2 =
      [(signedAmountDeltaFunction second).body[2]!, .return [.var "__cond4"]] := by
    cases second <;> rfl
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 (signedAmountDeltaFunction second).body, ht]
  apply execBlock_append_ok (signedAmountDeltaPrefixSource imms evm second a)
  apply ExecBlock.consRevert
  have hg := evalSignedAmountDeltaGuard imms evm second a
  have hc := signedAmountDeltaCallReverts imms evm second a hfit hv
  by_cases hn : a.liquidity < 0
  · have hp : ¬0 ≤ a.liquidity := by omega
    rw [decide_eq_true hn] at hg
    cases second <;> apply ExecStmt.iteTrue hg <;> apply ExecBlock.consRevert
    all_goals
      simpa only [signedAmountDeltaCallArgs, signedAmountDeltaCallName, if_pos hn,
        decide_eq_false hp, amountDeltaName, Bool.false_eq_true, if_false, if_true] using hc
  · have hp : 0 ≤ a.liquidity := by omega
    rw [decide_eq_false hn] at hg
    cases second <;> apply ExecStmt.iteFalse hg <;> apply ExecBlock.consRevert
    all_goals
      simpa only [signedAmountDeltaCallArgs, signedAmountDeltaCallName, if_neg hn,
        decide_eq_true hp, amountDeltaName, Bool.false_eq_true, if_false, if_true] using hc

end Benchmarks.UniswapV3.Pool
