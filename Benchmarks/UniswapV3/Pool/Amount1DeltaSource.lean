import Benchmarks.UniswapV3.Pool.Amount1DeltaPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem amount1DeltaCallSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) :
    ExecStmt config (amount1DeltaZeroFrame imms a) evm
      (.internalCall (if a.roundUp then "FullMath_mulDivRoundingUp" else "FullMath_mulDiv")
        amount1DeltaArgs (amount1DeltaCallName a.roundUp))
      (.ok (amount1DeltaCallFrame imms a) evm) := by
  have hv : fullMathRoundValid a.liquidity (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96)) :=
    amountDeltaMulValid true a hfit (Or.inl rfl)
  have hbind : bindParams? fullMathFunction.params
      [.int (Int.ofNat a.liquidity.toNat), .int (Int.ofNat (amountDeltaDifference a).toNat),
        .int (Int.ofNat (UInt256.ofNat (2 ^ 96)).toNat)] =
      some (fullMathLocals a.liquidity (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96))) := rfl
  cases hr : a.roundUp
  · have hc := internalCallFunctionReturn (callee := fullMathFunction) (retVar := "__c3")
      (calleeSolm := fullMathProductFrame imms a.liquidity (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96)))
      (locals := fullMathLocals a.liquidity (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96)))
      (value := some [.int (Int.ofNat (fullMathResult a.liquidity
        (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96))).toNat)])
      (evalAmount1DeltaArgs imms evm a)
      (by rw [amount1DeltaZeroFrame_eq]; exact fullMathLookup) hbind
      (by rw [amount1DeltaZeroFrame_eq]; exact fullMathReturns imms evm _ _ _ hv.1)
    simpa only [amount1DeltaCallFrame, amount1DeltaCallName, amountDeltaMulResult,
      amountDeltaFactor, amountDeltaDenominator, hr, Bool.false_eq_true, if_false, if_true] using hc
  · have hc := internalCallFunctionReturn (callee := fullMathRoundFunction) (retVar := "__c2")
      (calleeSolm := fullMathRoundFinalFrame imms a.liquidity (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96)))
      (locals := fullMathLocals a.liquidity (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96)))
      (value := some [.int (Int.ofNat (fullMathRoundResult a.liquidity
        (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96))).toNat)])
      (evalAmount1DeltaArgs imms evm a)
      (by rw [amount1DeltaZeroFrame_eq]; exact fullMathRoundLookup) hbind
      (by rw [amount1DeltaZeroFrame_eq]; exact fullMathRoundReturns imms evm _ _ _ hv)
    simpa only [amount1DeltaCallFrame, amount1DeltaCallName, amountDeltaMulResult,
      amountDeltaFactor, amountDeltaDenominator, hr, if_true] using hc

theorem amount1DeltaAssignSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs) :
    ExecStmt config (amount1DeltaCallFrame imms a) evm
      (.assign .localVar ⟨"__cond4", []⟩ (.var (amount1DeltaCallName a.roundUp)))
      (.ok (amount1DeltaReturnFrame imms a) evm) := by
  have hc : (amount1DeltaCallFrame imms a).locals.get? "__cond4" = some (.int 0) := by
    cases hr : a.roundUp <;>
      simp only [amount1DeltaCallFrame, amount1DeltaCallName, amount1DeltaZeroFrame, hr,
        Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    all_goals rfl
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame hc)

theorem amount1DeltaChoiceSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) :
    ExecStmt config (amount1DeltaZeroFrame imms a) evm ((amountDeltaFunction true).body[3]!)
      (.ok (amount1DeltaReturnFrame imms a) evm) := by
  have hg : evalExpr? config (amount1DeltaZeroFrame imms a) evm (.var "roundUp") =
      .ok (.bool a.roundUp) := evalExpr_var_get (by
        simpa only [amount1DeltaZeroFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] using (amountDeltaSortedGet imms true a).2.2.2)
  have hc := amount1DeltaCallSource imms evm a hfit
  have ha := amount1DeltaAssignSource imms evm a
  cases hr : a.roundUp
  · apply ExecStmt.iteFalse (by simpa only [hr] using hg)
    exact ExecBlock.consNormal
      (by simpa only [amount1DeltaCallName, hr, Bool.false_eq_true, if_false] using hc)
      (ExecBlock.consNormal (by simpa only [amount1DeltaCallName, hr, Bool.false_eq_true, if_false]
        using ha) ExecBlock.nil)
  · apply ExecStmt.iteTrue (by simpa only [hr] using hg)
    exact ExecBlock.consNormal
      (by simpa only [amount1DeltaCallName, hr, if_true] using hc)
      (ExecBlock.consNormal (by simpa only [amount1DeltaCallName, hr, if_true] using ha) ExecBlock.nil)

theorem amount1DeltaReturns (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) :
    ExecFuncBody config (amountDeltaFrame imms a) evm (amountDeltaFunction true).body
      (.returned (amount1DeltaReturnFrame imms a) evm
        (some [.int (Int.ofNat (amountDeltaResult true a).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 3 (amountDeltaFunction true).body]
  apply execBlock_append_ok (amount1DeltaZeroSource imms evm a)
  refine ExecBlock.consNormal (amount1DeltaChoiceSource imms evm a hfit) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have he : evalExpr? config (amount1DeltaReturnFrame imms a) evm (.var "__cond4") =
      .ok (.int (Int.ofNat (amountDeltaMulResult true a).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure, amountDeltaResult, if_true]

end Benchmarks.UniswapV3.Pool
