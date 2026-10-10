import Benchmarks.UniswapV3.Pool.NextSqrt1Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt1Direct (a : NextSqrtArgs) : Prop := nextSqrt1Small a ∧ a.add = true

instance (a : NextSqrtArgs) : Decidable (nextSqrt1Direct a) :=
  inferInstanceAs (Decidable (_ ∧ _))

noncomputable def nextSqrt1ChosenFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt1ZeroFrame imms a with
    locals := (if nextSqrt1Direct a then (nextSqrt1ZeroFrame imms a).locals
      else (nextSqrt1CallFrame imms a).locals).insert (nextSqrt1CondName a.add)
        (.int (Int.ofNat (nextSqrt1Quotient a).toNat))}

noncomputable def nextSqrt1QuotientFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt1ChosenFrame imms a with
    locals := (nextSqrt1ChosenFrame imms a).locals.insert "quotient"
      (.int (Int.ofNat (nextSqrt1Quotient a).toNat))}

theorem nextSqrt1CallAssign (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hn : ¬nextSqrt1Direct a) :
    ExecStmt config (nextSqrt1CallFrame imms a) evm
      (.assign .localVar ⟨nextSqrt1CondName a.add, []⟩ (.var (nextSqrt1CallName a)))
      (.ok (nextSqrt1ChosenFrame imms a) evm) := by
  have hc : (nextSqrt1CallFrame imms a).locals.get? (nextSqrt1CondName a.add) = some (.int 0) := by
    cases ha : a.add <;> by_cases hsmall : nextSqrt1Small a <;>
      simp only [nextSqrt1CallFrame, nextSqrt1CallName, nextSqrt1ZeroFrame,
        nextSqrt1CondName, ha, Bool.false_eq_true, hsmall, ↓reduceIte,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  simp only [nextSqrt1ChosenFrame, if_neg hn]
  exact ExecStmt.assign (evalExpr_var_get Std.HashMap.getElem?_insert_self)
    (assignLocalVarBase_frame hc)

theorem nextSqrt1DirectAssign (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hd : nextSqrt1Direct a) (hv : nextSqrt1QuotientValid a) :
    ExecStmt config (nextSqrt1ZeroFrame imms a) evm
      (.assign .localVar ⟨nextSqrt1CondName a.add, []⟩
        (.binary .div nextSqrt1ScaledExpr (.var "liquidity")))
      (.ok (nextSqrt1ChosenFrame imms a) evm) := by
  have hn : a.liquidity.toNat ≠ 0 := by
    simpa only [nextSqrt1QuotientValid, if_pos hd.1, hd.2, true_implies] using hv
  have he := evalExpr_word_div (evalNextSqrt1Scaled imms evm a)
    (evalExpr_var_get (nextSqrt1ZeroGet imms a).2.1) hn
  simp only [nextSqrt1ChosenFrame, if_pos hd]
  apply ExecStmt.assign _ (assignLocalVarBase_frame (nextSqrt1ZeroGet imms a).2.2.2.2)
  simpa only [nextSqrt1Quotient, if_pos hd.1, hd.2, if_true] using he

theorem nextSqrt1ChoiceSource (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : nextSqrt1QuotientValid a) :
    ExecStmt config (nextSqrt1ZeroFrame imms a) evm (nextSqrt1Branch a.add)[1]!
      (.ok (nextSqrt1ChosenFrame imms a) evm) := by
  have hg := evalNextSqrt1Small imms evm a
  by_cases hsmall : nextSqrt1Small a
  · have hgt : evalExpr? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1SmallExpr =
        .ok (.bool true) := by simpa only [hsmall, decide_true] using hg
    cases ha : a.add
    · have hn : ¬nextSqrt1Direct a := fun h ↦ Bool.noConfusion (ha.symm.trans h.2)
      have hc := nextSqrt1UnsafeReturns imms evm a hsmall ha
      have has := nextSqrt1CallAssign imms evm a hn
      apply ExecStmt.iteTrue hgt
      refine ExecBlock.consNormal hc (ExecBlock.consNormal ?_ ExecBlock.nil)
      simpa only [nextSqrt1CallName, if_pos hsmall, nextSqrt1CondName,
        ha, Bool.false_eq_true, if_false] using has
    · have has := nextSqrt1DirectAssign imms evm a ⟨hsmall, ha⟩ hv
      apply ExecStmt.iteTrue hgt
      exact ExecBlock.consNormal
        (by simpa only [nextSqrt1CondName, ha, if_true] using has) ExecBlock.nil
  · have hgf : evalExpr? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1SmallExpr =
        .ok (.bool false) := by simpa only [hsmall, decide_false] using hg
    have hn : ¬nextSqrt1Direct a := fun h ↦ hsmall h.1
    have hc := nextSqrt1FullReturns imms evm a hsmall hv
    have has := nextSqrt1CallAssign imms evm a hn
    cases ha : a.add <;> apply ExecStmt.iteFalse hgf
    all_goals
      exact ExecBlock.consNormal
        (by simpa only [nextSqrt1FullCall, nextSqrt1CallName, if_neg hsmall,
          nextSqrt1CondName, ha, Bool.false_eq_true, if_false, if_true] using hc)
        (ExecBlock.consNormal
          (by simpa only [nextSqrt1CallName, if_neg hsmall, nextSqrt1CondName,
            ha, Bool.false_eq_true, if_false, if_true] using has) ExecBlock.nil)

theorem nextSqrt1QuotientSource (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : nextSqrt1QuotientValid a) :
    ExecBlock config (nextSqrtFrame imms a) evm ((nextSqrt1Branch a.add).take 3)
      (.ok (nextSqrt1QuotientFrame imms a) evm) := by
  have hz := nextSqrt1ZeroSource imms evm a
  have hc := nextSqrt1ChoiceSource imms evm a hv
  have he : evalExpr? config (nextSqrt1ChosenFrame imms a) evm
      (.var (nextSqrt1CondName a.add)) = .ok (.int (Int.ofNat (nextSqrt1Quotient a).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  cases ha : a.add <;> simp only [ha] at hz hc ⊢
  all_goals exact ExecBlock.consNormal hz (ExecBlock.consNormal hc
    (ExecBlock.consNormal (ExecStmt.letDecl
      (by simpa only [nextSqrt1CondName, ha, Bool.false_eq_true, if_false, if_true] using he))
      ExecBlock.nil))

theorem nextSqrt1ChoiceReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬nextSqrt1QuotientValid a) :
    ExecStmt config (nextSqrt1ZeroFrame imms a) evm (nextSqrt1Branch a.add)[1]!
      .reverted := by
  have hg := evalNextSqrt1Small imms evm a
  by_cases hs : nextSqrt1Small a
  · have hgt : evalExpr? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1SmallExpr =
        .ok (.bool true) := by simpa only [hs, decide_true] using hg
    cases ha : a.add
    · exact False.elim (hv (by simp only [nextSqrt1QuotientValid, if_pos hs,
        ha, Bool.false_eq_true, false_implies]))
    · have hz : a.liquidity.toNat = 0 := by
        by_contra hn
        exact hv (by simpa only [nextSqrt1QuotientValid, if_pos hs, ha, true_implies] using hn)
      apply ExecStmt.iteTrue hgt
      apply ExecBlock.consRevert (ExecStmt.assignExprRevert ?_)
      have es := evalNextSqrt1Scaled imms evm a
      dsimp only [nextSqrt1ScaledExpr] at es
      have el := evalExpr_var_get (cfg := config) (evm := evm)
        (nextSqrt1ZeroGet imms a).2.1
      simp only [evalExpr?, es, el, hz, evalBinaryOp?, bind, EvalResult.bind]
      rfl
  · have hgf : evalExpr? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1SmallExpr =
        .ok (.bool false) := by simpa only [hs, decide_false] using hg
    have hc := nextSqrt1FullReverts imms evm a hs hv
    cases ha : a.add <;> apply ExecStmt.iteFalse hgf <;> apply ExecBlock.consRevert
    all_goals simpa only [nextSqrt1FullCall, nextSqrt1CallName, if_neg hs,
      ha, Bool.false_eq_true, if_false, if_true] using hc

theorem nextSqrt1QuotientReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬nextSqrt1QuotientValid a) :
    ExecBlock config (nextSqrtFrame imms a) evm ((nextSqrt1Branch a.add).take 3)
      .reverted := by
  have hz := nextSqrt1ZeroSource imms evm a
  have hc := nextSqrt1ChoiceReverts imms evm a hv
  cases ha : a.add <;> simp only [ha] at hz hc ⊢
  all_goals exact ExecBlock.consNormal hz (ExecBlock.consRevert hc)

end Benchmarks.UniswapV3.Pool
