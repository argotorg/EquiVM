import Benchmarks.UniswapV3.Pool.NextSqrt0Prefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt0DenominatorFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0ProductFrame imms a with
    locals := (nextSqrt0ProductFrame imms a).locals.insert "denominator"
      (.int (Int.ofNat (nextSqrt0Denominator a).toNat))}

def nextSqrt0DenominatorExpr (add : Bool) : Expr :=
  .cast (.binary (if add then .add else .sub) (.var "numerator1") (.var "product"))
    (.elem (.int (.uint ⟨256, by decide⟩)))

theorem nextSqrt0DenominatorSource (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    ExecStmt config (nextSqrt0ProductFrame imms a) evm
      (.letDecl "denominator" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (nextSqrt0DenominatorExpr a.add))
      (.ok (nextSqrt0DenominatorFrame imms a) evm) := by
  have hn := evalExpr_var_get (cfg := config) (evm := evm)
    (nextSqrt0ProductGet imms a).2.2.2.1
  have hp := evalExpr_var_get (cfg := config) (evm := evm)
    (nextSqrt0ProductGet imms a).2.2.2.2
  apply ExecStmt.letDecl
  cases ha : a.add
  · simpa only [nextSqrt0DenominatorExpr, nextSqrt0Denominator, ha,
      Bool.false_eq_true, if_false] using evalExpr_word_sub hn hp
  · simpa only [nextSqrt0DenominatorExpr, nextSqrt0Denominator, ha, if_true]
      using evalExpr_word_add hn hp

theorem nextSqrt0DenominatorGet (imms : Store) (a : NextSqrtArgs) :
    (nextSqrt0DenominatorFrame imms a).locals.get? "sqrtPX96" =
        some (.int (Int.ofNat a.price.toNat)) ∧
      (nextSqrt0DenominatorFrame imms a).locals.get? "amount" =
        some (.int (Int.ofNat a.amount.toNat)) ∧
      (nextSqrt0DenominatorFrame imms a).locals.get? "numerator1" =
        some (.int (Int.ofNat (nextSqrt0Numerator a).toNat)) ∧
      (nextSqrt0DenominatorFrame imms a).locals.get? "denominator" =
        some (.int (Int.ofNat (nextSqrt0Denominator a).toNat)) := by
  obtain ⟨hp, hm, _, hn, _⟩ := nextSqrt0ProductGet imms a
  simp only [nextSqrt0DenominatorFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert]
  exact ⟨hp, hm, hn, rfl⟩

theorem evalNextSqrt0DenominatorGuard (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExpr? config (nextSqrt0DenominatorFrame imms a) evm
      (.binary .ge (.var "denominator") (.var "numerator1")) =
      .ok (.bool (decide ((nextSqrt0Numerator a).toNat ≤ (nextSqrt0Denominator a).toNat))) := by
  have hd := evalExpr_var_get (cfg := config) (evm := evm)
    (nextSqrt0DenominatorGet imms a).2.2.2
  have hn := evalExpr_var_get (cfg := config) (evm := evm)
    (nextSqrt0DenominatorGet imms a).2.2.1
  simp only [evalExpr?, hd, hn, evalBinaryOp?, bind, EvalResult.bind]
  apply congrArg (fun b : Bool ↦ (EvalResult.ok (Value.bool b) : EvalResult Value))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact Int.ofNat_le

def nextSqrt0FullCallName (add : Bool) : String := if add then "__c0" else "__c3"

noncomputable def nextSqrt0FullFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0DenominatorFrame imms a with
    locals := (nextSqrt0DenominatorFrame imms a).locals.insert (nextSqrt0FullCallName a.add)
      (.int (Int.ofNat (nextSqrt0FullResult a).toNat))}

def nextSqrt0FullArgs : List Expr := [.var "numerator1", .var "sqrtPX96", .var "denominator"]

theorem evalNextSqrt0FullArgs (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExprs? config (nextSqrt0DenominatorFrame imms a) evm nextSqrt0FullArgs =
      .ok [.int (Int.ofNat (nextSqrt0Numerator a).toNat), .int (Int.ofNat a.price.toNat),
        .int (Int.ofNat (nextSqrt0Denominator a).toNat)] := by
  obtain ⟨hp, _, hn, hd⟩ := nextSqrt0DenominatorGet imms a
  have ep := evalExpr_var_get (cfg := config) (evm := evm) hp
  have en := evalExpr_var_get (cfg := config) (evm := evm) hn
  have ed := evalExpr_var_get (cfg := config) (evm := evm) hd
  simp only [nextSqrt0FullArgs, evalExprs?, ep, en, ed, bind, EvalResult.bind, pure]

theorem nextSqrt0FullReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : nextSqrt0FullValid a) :
    ExecStmt config (nextSqrt0DenominatorFrame imms a) evm
      (.internalCall "FullMath_mulDivRoundingUp" nextSqrt0FullArgs (nextSqrt0FullCallName a.add))
      (.ok (nextSqrt0FullFrame imms a) evm) :=
  internalCallFunctionReturn (callee := fullMathRoundFunction)
    (locals := fullMathLocals (nextSqrt0Numerator a) a.price (nextSqrt0Denominator a))
    (calleeSolm := fullMathRoundFinalFrame imms (nextSqrt0Numerator a) a.price
      (nextSqrt0Denominator a))
    (value := some [.int (Int.ofNat (nextSqrt0FullResult a).toNat)])
    (evalNextSqrt0FullArgs imms evm a) fullMathRoundLookup (fullMathRoundBind _ _ _)
    (fullMathRoundReturns imms evm _ _ _ hv)

theorem nextSqrt0FullReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬nextSqrt0FullValid a) :
    ExecStmt config (nextSqrt0DenominatorFrame imms a) evm
      (.internalCall "FullMath_mulDivRoundingUp" nextSqrt0FullArgs (nextSqrt0FullCallName a.add))
      .reverted :=
  internalCallFunctionRevert (callee := fullMathRoundFunction)
    (locals := fullMathLocals (nextSqrt0Numerator a) a.price (nextSqrt0Denominator a))
    (evalNextSqrt0FullArgs imms evm a) fullMathRoundLookup (fullMathRoundBind _ _ _)
    (fullMathRoundReverts imms evm _ _ _ hv)

end Benchmarks.UniswapV3.Pool
