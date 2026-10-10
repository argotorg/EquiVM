import Benchmarks.UniswapV3.Pool.NextPricePrefix
import Benchmarks.UniswapV3.Pool.NextSqrt0Source
import Benchmarks.UniswapV3.Pool.NextSqrt1Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextPriceCallArgs (input : Bool) : List Expr :=
  [.var "sqrtPX96", .var "liquidity", .var (nextPriceAmountName input), .boolLit input]

def nextPriceCallName (a : NextPriceArgs) : String := if a.zeroForOne then "__c0" else "__c1"

noncomputable def nextPriceCallFrame (imms : Store) (input : Bool) (a : NextPriceArgs) : Frame :=
  {nextPriceReadyFrame imms input a with
    locals := (nextPriceReadyFrame imms input a).locals.insert (nextPriceCallName a)
      (.int (Int.ofNat (nextPriceResult input a).toNat))}

noncomputable def nextPriceResultFrame (imms : Store) (input : Bool) (a : NextPriceArgs) : Frame :=
  {nextPriceCallFrame imms input a with
    locals := (nextPriceCallFrame imms input a).locals.insert "__cond2"
      (.int (Int.ofNat (nextPriceResult input a).toNat))}

theorem evalNextPriceCallArgs (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) :
    evalExprs? config (nextPriceReadyFrame imms input a) evm (nextPriceCallArgs input) =
      .ok (a.sqrtArgs input).values := by
  obtain ⟨hp, hl, hm, _, _⟩ := nextPriceReadyGet imms input a
  have ep := evalExpr_var_get (cfg := config) (evm := evm) hp
  have el := evalExpr_var_get (cfg := config) (evm := evm) hl
  have em := evalExpr_var_get (cfg := config) (evm := evm) hm
  simp only [nextPriceCallArgs, evalExprs?, evalExpr?, ep, el, em, NextPriceArgs.sqrtArgs,
    NextSqrtArgs.values, bind, EvalResult.bind, pure]

theorem nextPriceCallReturns (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (ha : a.Fits) (hv : nextPriceCalleeValid input a) :
    ExecStmt config (nextPriceReadyFrame imms input a) evm
      (.internalCall (nextSqrtName (nextPriceOne input a)) (nextPriceCallArgs input)
        (nextPriceCallName a)) (.ok (nextPriceCallFrame imms input a) evm) := by
  cases ho : nextPriceOne input a
  · have hh : nextSqrt0Valid (a.sqrtArgs input) := by
      simpa only [nextPriceCalleeValid, ho, Bool.false_eq_true, if_false] using hv
    have hc := internalCallFunctionReturn (callee := nextSqrtFunction false)
      (retVar := nextPriceCallName a) (locals := nextSqrtLocals (a.sqrtArgs input))
      (calleeSolm := nextSqrt0FinalFrame imms (a.sqrtArgs input))
      (value := some [.int (Int.ofNat (nextSqrt0Result (a.sqrtArgs input)).toNat)])
      (evalNextPriceCallArgs imms evm input a) (nextSqrtLookup false)
      (nextSqrtBind false _) (nextSqrt0Returns imms evm _ hh)
    simpa only [nextPriceCallFrame, nextPriceResult, ho, Bool.false_eq_true, if_false] using hc
  · have hh : nextSqrt1Valid (a.sqrtArgs input) := by
      simpa only [nextPriceCalleeValid, ho, if_true] using hv
    have hc := internalCallFunctionReturn (callee := nextSqrtFunction true)
      (retVar := nextPriceCallName a) (locals := nextSqrtLocals (a.sqrtArgs input))
      (calleeSolm := nextSqrt1OutputFrame imms (a.sqrtArgs input))
      (value := some [.int (Int.ofNat (nextSqrt1Result (a.sqrtArgs input)).toNat)])
      (evalNextPriceCallArgs imms evm input a) (nextSqrtLookup true)
      (nextSqrtBind true _) (nextSqrt1Returns imms evm _ ha hh)
    simpa only [nextPriceCallFrame, nextPriceResult, ho, if_true] using hc

theorem nextPriceCallReverts (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) (hv : ¬nextPriceCalleeValid input a) :
    ExecStmt config (nextPriceReadyFrame imms input a) evm
      (.internalCall (nextSqrtName (nextPriceOne input a)) (nextPriceCallArgs input)
        (nextPriceCallName a)) .reverted := by
  cases ho : nextPriceOne input a
  · have hh : ¬nextSqrt0Valid (a.sqrtArgs input) := by
      simpa only [nextPriceCalleeValid, ho, Bool.false_eq_true, if_false] using hv
    exact internalCallFunctionRevert (callee := nextSqrtFunction false)
      (evalNextPriceCallArgs imms evm input a) (nextSqrtLookup false)
      (nextSqrtBind false _) (nextSqrt0Reverts imms evm _ hh)
  · have hh : ¬nextSqrt1Valid (a.sqrtArgs input) := by
      simpa only [nextPriceCalleeValid, ho, if_true] using hv
    exact internalCallFunctionRevert (callee := nextSqrtFunction true)
      (evalNextPriceCallArgs imms evm input a) (nextSqrtLookup true)
      (nextSqrtBind true _) (nextSqrt1Reverts imms evm _ hh)

theorem nextPriceCallAssign (imms : Store) (evm : EVM.State) (input : Bool)
    (a : NextPriceArgs) :
    ExecStmt config (nextPriceCallFrame imms input a) evm
      (.assign .localVar ⟨"__cond2", []⟩ (.var (nextPriceCallName a)))
      (.ok (nextPriceResultFrame imms input a) evm) := by
  apply ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
  apply assignLocalVarBase_frame (old := .int 0)
  cases hz : a.zeroForOne <;>
    simp only [nextPriceCallFrame, nextPriceCallName, hz, Bool.false_eq_true,
      if_false, if_true, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;>
    exact (nextPriceReadyGet imms input a).2.2.2.2

end Benchmarks.UniswapV3.Pool
