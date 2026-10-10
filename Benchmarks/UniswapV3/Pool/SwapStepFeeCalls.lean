import Benchmarks.UniswapV3.Pool.SwapStepCapSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepFeeTest : Expr :=
  .binary .and (.var "exactIn")
    (.binary .ne (.var "sqrtRatioNextX96") (.var "sqrtRatioTargetX96"))

def swapStepFeeArgs : List Expr :=
  [.var "amountIn", .var "feePips", swapStepComplementExpr]

theorem evalSwapStepFeeTest (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    evalExpr? config (swapStepCapFrame imms a) evm swapStepFeeTest =
      .ok (.bool (swapStepUnusedFee a)) := by
  have hi := evalExpr_var_get (cfg := config) (evm := evm) (swapStepCapCalcGet imms a).exactIn
  have hp := evalExpr_var_get (cfg := config) (evm := evm) (swapStepCapCalcGet imms a).price
  have ht := evalExpr_var_get (cfg := config) (evm := evm) (swapStepCapExtraGet imms a).2.2.1
  have he : (Value.int (Int.ofNat (swapStepPrice a).toNat) ==
      Value.int (Int.ofNat a.target.toNat)) = swapStepMax a := by
    apply Bool.eq_iff_iff.mpr
    simp only [swapStepMax, beq_iff_eq, Value.int.injEq, decide_eq_true_eq, Int.ofNat_eq_natCast]
    omega
  have hn : evalExpr? config (swapStepCapFrame imms a) evm
      (.binary .ne (.var "sqrtRatioNextX96") (.var "sqrtRatioTargetX96")) =
      .ok (.bool (!swapStepMax a)) := by
    simp only [evalExpr?, hp, ht, evalBinaryOp?, bind, EvalResult.bind, he]
  cases hx : swapStepExactIn a <;>
    simp only [swapStepFeeTest, evalExpr?, hi, hn, hx, bind, EvalResult.bind, pure,
      swapStepUnusedFee, Bool.false_and, Bool.true_and]

theorem evalSwapStepFeeArgs (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    evalExprs? config (swapStepCapFrame imms a) evm swapStepFeeArgs =
      .ok [.int (Int.ofNat (swapStepAmount a true).toNat), .int (Int.ofNat a.fee.toNat),
        .int (Int.ofNat (swapStepComplement a).toNat)] := by
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (swapStepCapAmountsGet imms a).1
  have hf := evalExpr_var_get (cfg := config) (evm := evm) (swapStepCapExtraGet imms a).2.1
  have hc := evalSwapStepComplement (swapStepCapFrame imms a) evm a
    (swapStepCapExtraGet imms a).2.1
  simp only [swapStepFeeArgs, evalExprs?, ha, hf, hc, bind, EvalResult.bind, pure]

theorem swapStepFeeCallReturns (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hv : fullMathRoundValid (swapStepAmount a true) a.fee (swapStepComplement a)) :
    ExecStmt config (swapStepCapFrame imms a) evm
      (.internalCall "FullMath_mulDivRoundingUp" swapStepFeeArgs "__c17")
      (.ok (swapStepFeeCallFrame imms a) evm) := by
  exact internalCallFunctionReturn (callee := fullMathRoundFunction)
    (calleeSolm := fullMathRoundFinalFrame imms (swapStepAmount a true) a.fee
      (swapStepComplement a))
    (locals := fullMathLocals (swapStepAmount a true) a.fee (swapStepComplement a))
    (value := some [.int (Int.ofNat (fullMathRoundResult (swapStepAmount a true) a.fee
      (swapStepComplement a)).toNat)])
    (evalSwapStepFeeArgs imms evm a) fullMathRoundLookup (fullMathRoundBind _ _ _)
    (fullMathRoundReturns imms evm _ _ _ hv)

theorem swapStepFeeCallReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hv : ¬fullMathRoundValid (swapStepAmount a true) a.fee (swapStepComplement a)) :
    ExecStmt config (swapStepCapFrame imms a) evm
      (.internalCall "FullMath_mulDivRoundingUp" swapStepFeeArgs "__c17") .reverted := by
  exact internalCallFunctionRevert (callee := fullMathRoundFunction)
    (locals := fullMathLocals (swapStepAmount a true) a.fee (swapStepComplement a))
    (evalSwapStepFeeArgs imms evm a) fullMathRoundLookup (fullMathRoundBind _ _ _)
    (fullMathRoundReverts imms evm _ _ _ hv)

end Benchmarks.UniswapV3.Pool
