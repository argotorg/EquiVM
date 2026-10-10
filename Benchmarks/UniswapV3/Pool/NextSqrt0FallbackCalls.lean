import Benchmarks.UniswapV3.Pool.NextSqrt0Denominator
import Benchmarks.UniswapV3.Pool.LowGasSafeAdd

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt0FallbackFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0ProductFrame imms a with
    locals := if nextSqrt0ProductExact a then (nextSqrt0DenominatorFrame imms a).locals
      else (nextSqrt0ProductFrame imms a).locals}

def nextSqrt0FallbackAddFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0FallbackFrame imms a with
    locals := (nextSqrt0FallbackFrame imms a).locals.insert "__c1"
      (.int (Int.ofNat (nextSqrt0FallbackSum a).toNat))}

def nextSqrt0FallbackDivFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0FallbackAddFrame imms a with
    locals := (nextSqrt0FallbackAddFrame imms a).locals.insert "__c2"
      (.int (Int.ofNat (unsafeDivRoundResult
        (nextSqrt0Numerator a) (nextSqrt0FallbackSum a)).toNat))}

theorem nextSqrt0FallbackGet (imms : Store) (a : NextSqrtArgs) :
    (nextSqrt0FallbackFrame imms a).locals.get? "sqrtPX96" =
        some (.int (Int.ofNat a.price.toNat)) ∧
      (nextSqrt0FallbackFrame imms a).locals.get? "amount" =
        some (.int (Int.ofNat a.amount.toNat)) ∧
      (nextSqrt0FallbackFrame imms a).locals.get? "numerator1" =
        some (.int (Int.ofNat (nextSqrt0Numerator a).toNat)) := by
  by_cases he : nextSqrt0ProductExact a
  · obtain ⟨hp, hm, hn, _⟩ := nextSqrt0DenominatorGet imms a
    simpa only [nextSqrt0FallbackFrame, if_pos he] using And.intro hp (And.intro hm hn)
  · obtain ⟨hp, hm, _, hn, _⟩ := nextSqrt0ProductGet imms a
    simpa only [nextSqrt0FallbackFrame, if_neg he] using And.intro hp (And.intro hm hn)

def nextSqrt0FallbackArgs : List Expr :=
  [.binary .div (.var "numerator1") (.var "sqrtPX96"), .var "amount"]

theorem evalNextSqrt0FallbackArgs (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hn : a.price.toNat ≠ 0) :
    evalExprs? config (nextSqrt0FallbackFrame imms a) evm nextSqrt0FallbackArgs =
      .ok [.int (Int.ofNat (nextSqrt0FallbackQuotient a).toNat),
        .int (Int.ofNat a.amount.toNat)] := by
  obtain ⟨hp, hm, hnum⟩ := nextSqrt0FallbackGet imms a
  have ep := evalExpr_var_get (cfg := config) (evm := evm) hp
  have en := evalExpr_var_get (cfg := config) (evm := evm) hnum
  have em := evalExpr_var_get (cfg := config) (evm := evm) hm
  have ed := evalExpr_word_div en ep hn
  simp only [nextSqrt0FallbackArgs, evalExprs?, ed, em, bind, EvalResult.bind, pure]
  rfl

theorem nextSqrt0FallbackAddReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : nextSqrt0FallbackValid a) :
    ExecStmt config (nextSqrt0FallbackFrame imms a) evm
      (.internalCall "LowGasSafeMath_add" nextSqrt0FallbackArgs "__c1")
      (.ok (nextSqrt0FallbackAddFrame imms a) evm) :=
  internalCallFunctionReturn (callee := safeAddFunction)
    (locals := safeAddLocals (nextSqrt0FallbackQuotient a) a.amount)
    (calleeSolm := safeAddResultFrame imms (nextSqrt0FallbackQuotient a) a.amount)
    (value := some [.int (Int.ofNat (nextSqrt0FallbackSum a).toNat)])
    (evalNextSqrt0FallbackArgs imms evm a hv.1) safeAddLookup (safeAddBind _ _)
    (safeAddReturns imms evm _ _ hv.2)

theorem nextSqrt0FallbackAddReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬nextSqrt0FallbackValid a) :
    ExecStmt config (nextSqrt0FallbackFrame imms a) evm
      (.internalCall "LowGasSafeMath_add" nextSqrt0FallbackArgs "__c1") .reverted := by
  by_cases hn : a.price.toNat = 0
  · obtain ⟨hp, _, hnum⟩ := nextSqrt0FallbackGet imms a
    have ep := evalExpr_var_get (cfg := config) (evm := evm) hp
    have en := evalExpr_var_get (cfg := config) (evm := evm) hnum
    have ed : evalExpr? config (nextSqrt0FallbackFrame imms a) evm
        (.binary .div (.var "numerator1") (.var "sqrtPX96")) = .revert := by
      simp only [evalExpr?, en, ep, hn, evalBinaryOp?, bind, EvalResult.bind]
      rfl
    apply ExecStmt.internalCallArgsRevert
    simp only [nextSqrt0FallbackArgs, evalExprs?, ed, bind, EvalResult.bind]
  · exact internalCallFunctionRevert (callee := safeAddFunction)
      (locals := safeAddLocals (nextSqrt0FallbackQuotient a) a.amount)
      (evalNextSqrt0FallbackArgs imms evm a hn) safeAddLookup (safeAddBind _ _)
      (safeAddReverts imms evm _ _ (fun h ↦ hv ⟨hn, h⟩))

theorem nextSqrt0FallbackDivReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    ExecStmt config (nextSqrt0FallbackAddFrame imms a) evm
      (.internalCall "UnsafeMath_divRoundingUp" [.var "numerator1", .var "__c1"] "__c2")
      (.ok (nextSqrt0FallbackDivFrame imms a) evm) := by
  have en : evalExpr? config (nextSqrt0FallbackAddFrame imms a) evm (.var "numerator1") =
      .ok (.int (Int.ofNat (nextSqrt0Numerator a).toNat)) :=
    evalExpr_var_get (by
      simpa only [nextSqrt0FallbackAddFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using (nextSqrt0FallbackGet imms a).2.2)
  have ec : evalExpr? config (nextSqrt0FallbackAddFrame imms a) evm (.var "__c1") =
      .ok (.int (Int.ofNat (nextSqrt0FallbackSum a).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  apply internalCallFunctionReturn (callee := unsafeDivRoundFunction)
    (locals := unsafeDivRoundLocals (nextSqrt0Numerator a) (nextSqrt0FallbackSum a))
    (calleeSolm := unsafeDivRoundFrame imms (nextSqrt0Numerator a) (nextSqrt0FallbackSum a))
    (value := some [.int (Int.ofNat
      (unsafeDivRoundResult (nextSqrt0Numerator a) (nextSqrt0FallbackSum a)).toNat)])
    _ unsafeDivRoundLookup (unsafeDivRoundBind _ _) (unsafeDivRoundReturns imms evm _ _)
  simp only [evalExprs?, en, ec, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
