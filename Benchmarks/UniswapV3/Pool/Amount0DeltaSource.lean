import Benchmarks.UniswapV3.Pool.Amount0DeltaCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem amount0DeltaAssignSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hv : amountDeltaValid false a) :
    ExecStmt config (amount0DeltaComputedFrame imms a) evm
      (.assign .localVar ⟨"__cond5", []⟩
        (if a.roundUp then .var "__c3" else .binary .div (.var "__c4") (.var "sqrtRatioAX96")))
      (.ok (amount0DeltaReturnFrame imms a) evm) := by
  have hc : (amount0DeltaComputedFrame imms a).locals.get? "__cond5" = some (.int 0) := by
    cases hr : a.roundUp <;>
      simp only [amount0DeltaComputedFrame, amount0DeltaRoundFrame, amount0DeltaCallFrame,
        amount0DeltaCallName, amount0DeltaZeroFrame, hr, Bool.false_eq_true, if_false, if_true,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    all_goals rfl
  apply ExecStmt.assign (value := .int (Int.ofNat (amountDeltaResult false a).toNat)) ?_
    (assignLocalVarBase_frame hc)
  cases hr : a.roundUp
  · have hx : evalExpr? config (amount0DeltaCallFrame imms a) evm (.var "__c4") =
        .ok (.int (Int.ofNat (amountDeltaMulResult false a).toNat)) := evalExpr_var_get (by
          simp only [amount0DeltaCallFrame, amount0DeltaCallName, hr, Bool.false_eq_true, if_false,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self])
    have hy := evalExpr_var_get (cfg := config) (evm := evm) (amount0DeltaCallLower imms a)
    have hn : (amountDeltaLower a).toNat ≠ 0 := Nat.ne_of_gt (hv.resolve_left (by decide))
    simpa only [amount0DeltaComputedFrame, amountDeltaResult, hr, Bool.false_eq_true, if_false]
      using evalExpr_word_div hx hy hn
  · simp only [amount0DeltaComputedFrame, amountDeltaResult, hr, Bool.false_eq_true, if_false, if_true]
    exact evalExpr_var_get Std.HashMap.getElem?_insert_self

theorem amount0DeltaChoiceSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid false a) :
    ExecStmt config (amount0DeltaZeroFrame imms a) evm (amountDeltaFunction false).body[6]!
      (.ok (amount0DeltaReturnFrame imms a) evm) := by
  have hg : evalExpr? config (amount0DeltaZeroFrame imms a) evm (.var "roundUp") =
      .ok (.bool a.roundUp) := evalExpr_var_get (by
        simpa only [amount0DeltaZeroFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] using (amount0DeltaInputsGet imms a).2.2.2.2)
  have hc := amount0DeltaCallSource imms evm a hfit hv
  have ha := amount0DeltaAssignSource imms evm a hv
  cases hr : a.roundUp
  · apply ExecStmt.iteFalse (by simpa only [hr] using hg)
    exact ExecBlock.consNormal
      (by simpa only [amount0DeltaCallName, hr, Bool.false_eq_true, if_false] using hc)
      (ExecBlock.consNormal (by simpa only [amount0DeltaComputedFrame, hr,
        Bool.false_eq_true, if_false] using ha) ExecBlock.nil)
  · apply ExecStmt.iteTrue (by simpa only [hr] using hg)
    exact ExecBlock.consNormal
      (by simpa only [amount0DeltaCallName, hr, if_true] using hc)
      (ExecBlock.consNormal (amount0DeltaRoundSource imms evm a hr)
        (ExecBlock.consNormal (by simpa only [amount0DeltaComputedFrame, hr, if_true] using ha)
          ExecBlock.nil))

theorem amount0DeltaReturns (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid false a) :
    ExecFuncBody config (amountDeltaFrame imms a) evm (amountDeltaFunction false).body
      (.returned (amount0DeltaReturnFrame imms a) evm
        (some [.int (Int.ofNat (amountDeltaResult false a).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 6 (amountDeltaFunction false).body]
  apply execBlock_append_ok (amount0DeltaZeroSource imms evm a hfit hv)
  refine ExecBlock.consNormal (amount0DeltaChoiceSource imms evm a hfit hv) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have he : evalExpr? config (amount0DeltaReturnFrame imms a) evm (.var "__cond5") =
      .ok (.int (Int.ofNat (amountDeltaResult false a).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
