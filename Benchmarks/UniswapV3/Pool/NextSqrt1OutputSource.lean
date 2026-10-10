import Benchmarks.UniswapV3.Pool.NextSqrt1OutputCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

noncomputable def nextSqrt1OutputFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  if a.add then nextSqrt1CastFrame imms a else nextSqrt1QuotientFrame imms a

theorem evalNextSqrt1SubtractGuard (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExpr? config (nextSqrt1QuotientFrame imms a) evm
      (.binary .gt (.var "sqrtPX96") (.var "quotient")) =
      .ok (.bool (decide ((nextSqrt1Quotient a).toNat < a.price.toNat))) :=
  evalExpr_word_gt (evalExpr_var_get (nextSqrt1QuotientGet imms a).1)
    (evalExpr_var_get (nextSqrt1QuotientGet imms a).2)

theorem evalNextSqrt1Subtract (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hfit : a.Fits) (ha : a.add = false) (hv : nextSqrt1OutputValid a) :
    evalExpr? config (nextSqrt1QuotientFrame imms a) evm
      (.cast (.cast (.binary .sub (.var "sqrtPX96") (.var "quotient"))
        (.elem (.int (.uint ⟨256, by decide⟩)))) (.elem (.int (.uint ⟨160, by decide⟩)))) =
      .ok (.int (Int.ofNat (nextSqrt1Result a).toNat)) := by
  have ep := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1QuotientGet imms a).1
  have eq := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1QuotientGet imms a).2
  have he := evalExpr_intCast (.uint ⟨160, by decide⟩) (evalExpr_word_sub ep eq)
  have hn := (safeCast160Valid_iff (nextSqrt1Result a)).mpr (nextSqrt1Result_fits a hfit hv)
  simp only [nextSqrt1Result, ha, Bool.false_eq_true, if_false] at hn ⊢
  rw [hn] at he
  exact he

theorem nextSqrt1OutputReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hfit : a.Fits) (hv : nextSqrt1OutputValid a) :
    ExecBlock config (nextSqrt1QuotientFrame imms a) evm ((nextSqrt1Branch a.add).drop 3)
      (.returned (nextSqrt1OutputFrame imms a) evm
        (some [.int (Int.ofNat (nextSqrt1Result a).toNat)])) := by
  cases ha : a.add
  · have hguard : (nextSqrt1Quotient a).toNat < a.price.toNat := by
      simpa only [nextSqrt1OutputValid, ha, Bool.false_eq_true, if_false] using hv
    simp only [nextSqrt1OutputFrame, ha, Bool.false_eq_true, if_false]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [hguard, decide_true] using evalNextSqrt1SubtractGuard imms evm a
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    have he := evalNextSqrt1Subtract imms evm a hfit ha hv
    simp only [evalExprs?, he, bind, EvalResult.bind, pure]
  · have hh : a.price.toNat ≤ (a.price + nextSqrt1Quotient a).toNat ∧
        safeCast160Valid (a.price + nextSqrt1Quotient a) := by
      simpa only [nextSqrt1OutputValid, ha, if_true] using hv
    simp only [nextSqrt1OutputFrame, ha, if_true]
    refine ExecBlock.consNormal (nextSqrt1AddReturns imms evm a hh.1)
      (ExecBlock.consNormal (nextSqrt1CastReturns imms evm a hh.2) ?_)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    have he : evalExpr? config (nextSqrt1CastFrame imms a) evm (.var "__c3") =
        .ok (.int (Int.ofNat (a.price + nextSqrt1Quotient a).toNat)) :=
      evalExpr_var_get Std.HashMap.getElem?_insert_self
    simp only [evalExprs?, he, nextSqrt1Result, ha, if_true, bind, EvalResult.bind, pure]

theorem nextSqrt1OutputReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬nextSqrt1OutputValid a) :
    ExecBlock config (nextSqrt1QuotientFrame imms a) evm ((nextSqrt1Branch a.add).drop 3)
      .reverted := by
  cases ha : a.add
  · have hguard : ¬(nextSqrt1Quotient a).toNat < a.price.toNat := by
      simpa only [nextSqrt1OutputValid, ha, Bool.false_eq_true, if_false] using hv
    apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    simpa only [hguard, decide_false] using evalNextSqrt1SubtractGuard imms evm a
  · by_cases hadd : a.price.toNat ≤ (a.price + nextSqrt1Quotient a).toNat
    · have hcast : ¬safeCast160Valid (a.price + nextSqrt1Quotient a) := by
        intro hc
        exact hv (by simpa only [nextSqrt1OutputValid, ha, if_true] using And.intro hadd hc)
      exact ExecBlock.consNormal (nextSqrt1AddReturns imms evm a hadd)
        (ExecBlock.consRevert (nextSqrt1CastReverts imms evm a hcast))
    · exact ExecBlock.consRevert (nextSqrt1AddReverts imms evm a hadd)

end Benchmarks.UniswapV3.Pool
