import Benchmarks.UniswapV3.Pool.Amount0DeltaPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def amount0DeltaCallName (roundUp : Bool) : Ident := if roundUp then "__c2" else "__c4"

noncomputable def amount0DeltaCallFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amount0DeltaZeroFrame imms a).locals.insert (amount0DeltaCallName a.roundUp)
    (.int (Int.ofNat (amountDeltaMulResult false a).toNat))
  {amount0DeltaZeroFrame imms a with locals := locals}

noncomputable def amount0DeltaRoundFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amount0DeltaCallFrame imms a).locals.insert "__c3"
    (.int (Int.ofNat (unsafeDivRoundResult
      (amountDeltaMulResult false a) (amountDeltaLower a)).toNat))
  {amount0DeltaCallFrame imms a with locals := locals}

noncomputable def amount0DeltaComputedFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  if a.roundUp then amount0DeltaRoundFrame imms a else amount0DeltaCallFrame imms a

noncomputable def amount0DeltaReturnFrame (imms : Store) (a : AmountDeltaArgs) : Frame :=
  let locals := (amount0DeltaComputedFrame imms a).locals.insert "__cond5"
    (.int (Int.ofNat (amountDeltaResult false a).toNat))
  {amount0DeltaComputedFrame imms a with locals := locals}

theorem amount0DeltaCallFrame_eq (imms : Store) (a : AmountDeltaArgs) :
    amount0DeltaCallFrame imms a =
      {contract := contract, locals := (amount0DeltaCallFrame imms a).locals, immutables := imms} := by
  unfold amount0DeltaCallFrame
  rw [amount0DeltaZeroFrame_eq]

def amount0DeltaArgs : List Expr :=
  [.var "numerator1", .var "numerator2", .var "sqrtRatioBX96"]

theorem evalAmount0DeltaArgs (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs) :
    evalExprs? config (amount0DeltaZeroFrame imms a) evm amount0DeltaArgs =
      .ok [.int (Int.ofNat (amountDeltaNumerator a).toNat),
        .int (Int.ofNat (amountDeltaDifference a).toNat),
        .int (Int.ofNat (amountDeltaUpper a).toNat)] := by
  obtain ⟨_, hb, hn, hd, _⟩ := amount0DeltaInputsGet imms a
  have he (name : Ident) (value : Value) (hname : name ≠ "__cond5")
      (hget : (amount0DeltaInputsFrame imms a).locals.get? name = some value) :
      evalExpr? config (amount0DeltaZeroFrame imms a) evm (.var name) = .ok value :=
    evalExpr_var_get (by simpa only [amount0DeltaZeroFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hname, if_false] using hget)
  simp only [amount0DeltaArgs, evalExprs?, he _ _ (by decide) hn, he _ _ (by decide) hd,
    he _ _ (by decide) hb, bind, EvalResult.bind, pure]

theorem amount0DeltaCallSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid false a) :
    ExecStmt config (amount0DeltaZeroFrame imms a) evm
      (.internalCall (if a.roundUp then "FullMath_mulDivRoundingUp" else "FullMath_mulDiv")
        amount0DeltaArgs (amount0DeltaCallName a.roundUp))
      (.ok (amount0DeltaCallFrame imms a) evm) := by
  have hm : fullMathRoundValid (amountDeltaNumerator a) (amountDeltaDifference a)
      (amountDeltaUpper a) := amountDeltaMulValid false a hfit hv
  have hbind := fullMathBind (amountDeltaNumerator a) (amountDeltaDifference a) (amountDeltaUpper a)
  cases hr : a.roundUp
  · have hc := internalCallFunctionReturn (callee := fullMathFunction) (retVar := "__c4")
      (calleeSolm := fullMathProductFrame imms (amountDeltaNumerator a)
        (amountDeltaDifference a) (amountDeltaUpper a))
      (locals := fullMathLocals (amountDeltaNumerator a) (amountDeltaDifference a) (amountDeltaUpper a))
      (value := some [.int (Int.ofNat (fullMathResult (amountDeltaNumerator a)
        (amountDeltaDifference a) (amountDeltaUpper a)).toNat)])
      (evalAmount0DeltaArgs imms evm a)
      (by rw [amount0DeltaZeroFrame_eq]; exact fullMathLookup) hbind
      (by rw [amount0DeltaZeroFrame_eq]; exact fullMathReturns imms evm _ _ _ hm.1)
    simpa only [amount0DeltaCallFrame, amount0DeltaCallName, amountDeltaMulResult,
      amountDeltaFactor, amountDeltaDenominator, hr, Bool.false_eq_true, if_false] using hc
  · have hc := internalCallFunctionReturn (callee := fullMathRoundFunction) (retVar := "__c2")
      (calleeSolm := fullMathRoundFinalFrame imms (amountDeltaNumerator a)
        (amountDeltaDifference a) (amountDeltaUpper a))
      (locals := fullMathLocals (amountDeltaNumerator a) (amountDeltaDifference a) (amountDeltaUpper a))
      (value := some [.int (Int.ofNat (fullMathRoundResult (amountDeltaNumerator a)
        (amountDeltaDifference a) (amountDeltaUpper a)).toNat)])
      (evalAmount0DeltaArgs imms evm a)
      (by rw [amount0DeltaZeroFrame_eq]; exact fullMathRoundLookup) hbind
      (by rw [amount0DeltaZeroFrame_eq]; exact fullMathRoundReturns imms evm _ _ _ hm)
    simpa only [amount0DeltaCallFrame, amount0DeltaCallName, amountDeltaMulResult,
      amountDeltaFactor, amountDeltaDenominator, hr, Bool.false_eq_true, if_false, if_true] using hc

theorem amount0DeltaCallLower (imms : Store) (a : AmountDeltaArgs) :
    (amount0DeltaCallFrame imms a).locals.get? "sqrtRatioAX96" =
      some (.int (Int.ofNat (amountDeltaLower a).toNat)) := by
  cases hr : a.roundUp <;>
    simpa only [amount0DeltaCallFrame, amount0DeltaCallName, amount0DeltaZeroFrame, hr,
      Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using (amount0DeltaInputsGet imms a).1

theorem amount0DeltaRoundSource (imms : Store) (evm : EVM.State) (a : AmountDeltaArgs)
    (hr : a.roundUp = true) :
    ExecStmt config (amount0DeltaCallFrame imms a) evm
      (.internalCall "UnsafeMath_divRoundingUp" [.var "__c2", .var "sqrtRatioAX96"] "__c3")
      (.ok (amount0DeltaRoundFrame imms a) evm) := by
  have hx : evalExpr? config (amount0DeltaCallFrame imms a) evm (.var "__c2") =
      .ok (.int (Int.ofNat (amountDeltaMulResult false a).toNat)) := evalExpr_var_get (by
        simp only [amount0DeltaCallFrame, amount0DeltaCallName, hr, if_true,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self])
  have hy := evalExpr_var_get (cfg := config) (evm := evm) (amount0DeltaCallLower imms a)
  exact internalCallFunctionReturn (callee := unsafeDivRoundFunction) (retVar := "__c3")
    (calleeSolm := unsafeDivRoundFrame imms (amountDeltaMulResult false a) (amountDeltaLower a))
    (locals := unsafeDivRoundLocals (amountDeltaMulResult false a) (amountDeltaLower a))
    (value := some [.int (Int.ofNat (unsafeDivRoundResult
      (amountDeltaMulResult false a) (amountDeltaLower a)).toNat)])
    (by simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure])
    (by rw [amount0DeltaCallFrame_eq]; exact unsafeDivRoundLookup) (unsafeDivRoundBind _ _)
    (by rw [amount0DeltaCallFrame_eq]; exact unsafeDivRoundReturns imms evm _ _)

end Benchmarks.UniswapV3.Pool
