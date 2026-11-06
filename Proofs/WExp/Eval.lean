import Examples.WExp.Spec
import Proofs.WExp.Model
import Reasoning.SteleBody

/-!
# `wExp` spec-model correspondence

Every derivation of the spec's `wExp` body on input `x` in `[-maxInput, maxInput]` returns
`.int (specWExp x)` — `evalExpr?` is functional and every operation succeeds on this range,
so the result is forced for every derivation.
-/

open Stele ABI Reasoning.Theory

namespace WExp

/-! ## Locals plumbing -/

theorem eval_var {fr : Frame} {evm : EVM.State} {name : Ident} {v : Value}
    (h : fr.locals.get? name = some v) :
    evalExpr? wexpConfig fr evm (.var name) = .ok v := by
  simp only [evalExpr?, h, EvalResult.ofOption]

theorem get_insert_same (m : Store) (k : Ident) (v : Value) :
    (m.insert k v).get? k = some v := Std.HashMap.getElem?_insert_self

theorem get_insert_ne (m : Store) {k k' : Ident} {v w : Value}
    (hne : k' ≠ k) (h : m.get? k = some w) : (m.insert k' v).get? k = some w := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rw [Std.HashMap.get?_eq_getElem?] at h
  simp [hne]
  exact h

/-! ## Expression evaluation -/

theorem eval_cond {x : Int} {fr : Frame} {evm : EVM.State}
    (hx : fr.locals.get? "x" = some (.int x)) :
    evalExpr? wexpConfig fr evm wExpCond = .ok (.bool (x < 0)) := by
  simp only [wExpCond, evalExpr?, eval_var hx, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem eval_cond_false {x : Int} {fr : Frame} {evm : EVM.State}
    (hx : fr.locals.get? "x" = some (.int x)) (h : 0 ≤ x) :
    evalExpr? wexpConfig fr evm wExpCond = .ok (.bool false) := by
  rw [eval_cond hx]; simp only [show (decide (x < 0)) = false from decide_eq_false (by omega)]

theorem eval_cond_true {x : Int} {fr : Frame} {evm : EVM.State}
    (hx : fr.locals.get? "x" = some (.int x)) (h : x < 0) :
    evalExpr? wexpConfig fr evm wExpCond = .ok (.bool true) := by
  rw [eval_cond hx]; simp only [show (decide (x < 0)) = true from decide_eq_true h]

theorem eval_q {x : Int} {fr : Frame} {evm : EVM.State}
    (hx : fr.locals.get? "x" = some (.int x)) :
    evalExpr? wexpConfig fr evm
      (.binary .sdiv (.binary .add (.var "x") (.intLit 322611214989459870))
        (.intLit 693147180559945309)) = .ok (.int (qOf x)) := by
  simp [qOf, LN2, OFFSET, evalExpr?, eval_var hx, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem eval_r {x : Int} {fr : Frame} {evm : EVM.State}
    (hx : fr.locals.get? "x" = some (.int x))
    (hq : fr.locals.get? "q" = some (.int (qOf x))) :
    evalExpr? wexpConfig fr evm
      (.binary .sub (.var "x") (.binary .mul (.var "q") (.intLit 693147180559945309)))
        = .ok (.int (rOf x)) := by
  simp [rOf, LN2, evalExpr?, eval_var hx, eval_var hq, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem eval_second {x : Int} {fr : Frame} {evm : EVM.State}
    (hr : fr.locals.get? "r" = some (.int (rOf x))) :
    evalExpr? wexpConfig fr evm
      (.binary .sdiv (.binary .mul (.var "r") (.var "r")) (.intLit 2000000000000000000))
        = .ok (.int (sOf (rOf x))) := by
  simp [sOf, WAD, evalExpr?, eval_var hr, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem eval_third {x : Int} {fr : Frame} {evm : EVM.State}
    (hs : fr.locals.get? "secondTerm" = some (.int (sOf (rOf x))))
    (hr : fr.locals.get? "r" = some (.int (rOf x))) :
    evalExpr? wexpConfig fr evm
      (.binary .sdiv (.binary .mul (.var "secondTerm") (.var "r")) (.intLit 3000000000000000000))
        = .ok (.int (tOf (rOf x))) := by
  simp [tOf, WAD, evalExpr?, eval_var hs, eval_var hr, evalBinaryOp?, EvalResult.bind, bind, pure]

theorem eval_expR {x : Int} {fr : Frame} {evm : EVM.State}
    (hr : fr.locals.get? "r" = some (.int (rOf x)))
    (hs : fr.locals.get? "secondTerm" = some (.int (sOf (rOf x))))
    (ht : fr.locals.get? "thirdTerm" = some (.int (tOf (rOf x)))) :
    evalExpr? wexpConfig fr evm
      (.binary .add (.binary .add (.binary .add (.intLit 1000000000000000000) (.var "r"))
        (.var "secondTerm")) (.var "thirdTerm"))
        = .ok (.int (poly (rOf x))) := by
  simp [poly_eq, WAD, evalExpr?, eval_var hr, eval_var hs, eval_var ht, evalBinaryOp?,
    EvalResult.bind, bind, pure]

theorem poly_mono {a b : Int} (ha : -OFFSET ≤ a) (hab : a ≤ b) : poly a ≤ poly b := by
  have key : ∀ d : Nat, a + d ≤ b → poly a ≤ poly (a + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := poly_step (r := a + k) (by omega)
      have : (a : Int) + (k + 1 : Nat) = a + k + 1 := by grind
      rw [this]
      exact Int.le_trans h1 h2
  have e : (a : Int) + ((b - a).toNat : Nat) = b := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  have hle := key ((b - a).toNat) (by rw [e])
  rwa [e] at hle

/-- The return expression `uint256(expR) << uint256(q)` evaluates to `specWExpPos x`
    whenever `0 ≤ x ≤ MAXINPUT` (casts are then identity and `q < 256`). -/
theorem eval_ret {x : Int} {fr : Frame} {evm : EVM.State}
    (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT)
    (he : fr.locals.get? "expR" = some (.int (poly (rOf x))))
    (hq : fr.locals.get? "q" = some (.int (qOf x))) :
    evalExpr? wexpConfig fr evm
      (.binary (.shl (.uint ⟨256, by decide⟩)) (.cast (.var "expR") uint256)
        (.cast (.var "q") uint256)) = .ok (.int (specWExpPos x)) := by
  have hq0 : 0 ≤ qOf x := qOf_nonneg hx0
  have hpp : 0 < poly (rOf x) := poly_pos (rOf_bounds hx0).1
  have hphi : poly (rOf x) ≤ poly (LN2 - OFFSET - 1) :=
    poly_mono (rOf_bounds hx0).1 (by have h2 := (rOf_bounds hx0).2; omega)
  have hbound : poly (rOf x) < Int.ofNat (EVM.twoPow 256) := by
    have htop : poly (LN2 - OFFSET - 1) = 1447663323139670138 := by native_decide
    have h2 : (Int.ofNat (EVM.twoPow 256) : Int) =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      native_decide
    omega
  have hqhi : qOf x < 256 := by
    rw [qOf_eq x hx0]
    have h1 : (x + OFFSET) / LN2 ≤ (MAXINPUT + OFFSET) / LN2 :=
      Int.ediv_le_ediv (by unfold LN2; omega) (by omega)
    have h2 : (MAXINPUT + OFFSET) / LN2 = 24 := by native_decide
    omega
  have hcast : castValue? (.int (poly (rOf x))) (StorageType.ofABI uint256) =
      some (.int (poly (rOf x))) := by
    rw [show StorageType.ofABI uint256 = .elem (.int (.uint ⟨256, by decide⟩)) from rfl,
      castValue_int, normalizeInt_uint_eq_self _ _ (Int.le_of_lt hpp) hbound]
  have hcastq : castValue? (.int (qOf x)) (StorageType.ofABI uint256) =
      some (.int (qOf x)) := by
    rw [show StorageType.ofABI uint256 = .elem (.int (.uint ⟨256, by decide⟩)) from rfl,
      castValue_int, normalizeInt_uint_eq_self _ _ hq0]
    show qOf x < Int.ofNat (EVM.twoPow 256)
    have h2 : (256 : Int) ≤ Int.ofNat (EVM.twoPow 256) := by native_decide
    omega
  have hn1 : ¬(qOf x < 0) := by omega
  have hn2 : ¬((IntType.uint ⟨256, by decide⟩).bitWidth.val ≤ (qOf x).toNat) := by
    show ¬(256 ≤ (qOf x).toNat); omega
  simp [evalExpr?, eval_var he, eval_var hq, EvalResult.bind, bind, hcast, hcastq,
    evalBinaryOp?, EvalResult.ofOption, hn1, hn2]
  rw [specWExpPos, wExpPos_eq]
  rfl

theorem eval_arg_neg {x : Int} {fr : Frame} {evm : EVM.State}
    (hx : fr.locals.get? "x" = some (.int x)) :
    evalExprs? wexpConfig fr evm [.unary .neg (.var "x")] = .ok [.int (-x)] := by
  simp only [evalExprs?, evalExpr?, eval_var hx, evalUnaryOp?, EvalResult.bind, bind, pure,
    EvalResult.ofOption]

theorem eval_div {y : Int} {fr : Frame} {evm : EVM.State}
    (hp : fr.locals.get? "__pos" = some (.int y)) (hy : y ≠ 0) :
    evalExprs? wexpConfig fr evm
      [.binary .div (.intLit 1000000000000000000000000000000000000) (.var "__pos")]
        = .ok [.int (1000000000000000000000000000000000000 / y)] := by
  simp [evalExprs?, evalExpr?, eval_var hp, evalBinaryOp?, EvalResult.bind, bind, pure,
    hy]

/-! ## Statement-level inversions for `ite` and `internalCall` -/

theorem execBlock_ite {cfg : Config} {stele : Frame} {evm : EVM.State} {c : Expr}
    {tb eb rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.ite c tb eb :: rest) r) :
    (evalExpr? cfg stele evm c = .revert ∧ r = .reverted) ∨
      (evalExpr? cfg stele evm c = .ok (.bool true) ∧
        ExecBlock cfg stele evm (tb ++ rest) r) ∨
      (evalExpr? cfg stele evm c = .ok (.bool false) ∧
        ExecBlock cfg stele evm (eb ++ rest) r) := by
  cases h with
  | consNormal hst hrest =>
      cases hst with
      | iteTrue hc hb => exact Or.inr (Or.inl ⟨hc, execBlock_append hb hrest⟩)
      | iteFalse hc hb => exact Or.inr (Or.inr ⟨hc, execBlock_append hb hrest⟩)
  | consReturn hst =>
      cases hst with
      | iteTrue hc hb =>
          exact Or.inr (Or.inl
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
      | iteFalse hc hb =>
          exact Or.inr (Or.inr
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
  | consRevert hst =>
      cases hst with
      | iteCondRevert hc => exact Or.inl ⟨hc, rfl⟩
      | iteTrue hc hb =>
          exact Or.inr (Or.inl
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
      | iteFalse hc hb =>
          exact Or.inr (Or.inr
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
  | consBreak hst =>
      cases hst with
      | iteTrue hc hb =>
          exact Or.inr (Or.inl
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
      | iteFalse hc hb =>
          exact Or.inr (Or.inr
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
  | consContinue hst =>
      cases hst with
      | iteTrue hc hb =>
          exact Or.inr (Or.inl
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
      | iteFalse hc hb =>
          exact Or.inr (Or.inr
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
  | consStatic hst =>
      cases hst with
      | iteTrue hc hb =>
          exact Or.inr (Or.inl
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)
      | iteFalse hc hb =>
          exact Or.inr (Or.inr
            ⟨hc, execBlock_append_term hb (fun _ _ h => ExecResult.noConfusion h)⟩)

theorem execBlock_internalCall {cfg : Config} {stele : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.internalCall name args retVar :: rest) r) :
    (∃ vals callee locals fr' evm' v,
        evalExprs? cfg stele evm args = .ok vals ∧
        lookupCallable? stele.contract name = some callee ∧
        bindParams? callee.params vals = some locals ∧
        ExecFuncBody cfg { stele with locals := locals } evm callee.body (.returned fr' evm' v) ∧
        ExecBlock cfg (resumeAfterInternalCall stele retVar v) evm' rest r) ∨
    (∃ vals callee locals,
        evalExprs? cfg stele evm args = .ok vals ∧
        lookupCallable? stele.contract name = some callee ∧
        bindParams? callee.params vals = some locals ∧
        ExecFuncBody cfg { stele with locals := locals } evm callee.body .reverted ∧
        r = .reverted) ∨
    (evalExprs? cfg stele evm args = .revert ∧ r = .reverted) ∨
    (∃ vals callee locals,
        evalExprs? cfg stele evm args = .ok vals ∧
        lookupCallable? stele.contract name = some callee ∧
        bindParams? callee.params vals = some locals ∧
        ExecFuncBody cfg { stele with locals := locals } evm callee.body .staticViolation ∧
        r = .staticViolation) := by
  cases h with
  | consNormal hst hrest =>
      cases hst with
      | internalCallReturn hargs hcallee hbind hbody =>
          exact Or.inl ⟨_, _, _, _, _, _, hargs, hcallee, hbind, hbody, hrest⟩
  | consReturn hst => cases hst
  | consRevert hst =>
      cases hst with
      | internalCallRevert hargs hcallee hbind hbody =>
          exact Or.inr (Or.inl ⟨_, _, _, hargs, hcallee, hbind, hbody, rfl⟩)
      | internalCallArgsRevert hargs => exact Or.inr (Or.inr (Or.inl ⟨hargs, rfl⟩))
  | consBreak hst => cases hst
  | consContinue hst => cases hst
  | consStatic hst =>
      cases hst with
      | internalCallStatic hargs hcallee hbind hbody =>
          exact Or.inr (Or.inr (Or.inr ⟨_, _, _, hargs, hcallee, hbind, hbody, rfl⟩))

/-- Inversion for `letDecl` that exposes the evaluation result. -/
theorem execBlock_letDecl {cfg : Config} {stele : Frame} {evm : EVM.State} {name : Ident}
    {ty : Option ABIType} {e : Expr} {rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.letDecl name ty e :: rest) r) :
    (evalExpr? cfg stele evm e = .revert ∧ r = .reverted) ∨
      ∃ v, evalExpr? cfg stele evm e = .ok v ∧
        ExecBlock cfg { stele with locals := stele.locals.insert name v } evm rest r := by
  cases h with
  | consNormal hst hrest => cases hst with | letDecl hv => exact Or.inr ⟨_, hv, hrest⟩
  | consReturn hst => cases hst
  | consRevert hst => cases hst with | letDeclRevert hv => exact Or.inl ⟨hv, rfl⟩
  | consBreak hst => cases hst
  | consContinue hst => cases hst
  | consStatic hst => cases hst

/-- Inversion for `return` that exposes the evaluation result. -/
theorem execBlock_return {cfg : Config} {stele : Frame} {evm : EVM.State} {es : List Expr}
    {rest : List Stmt} {r : ExecResult}
    (h : ExecBlock cfg stele evm (.return es :: rest) r) :
    (evalExprs? cfg stele evm es = .revert ∧ r = .reverted) ∨
      ∃ vs, evalExprs? cfg stele evm es = .ok vs ∧ r = .returned stele evm (some vs) := by
  cases h with
  | consNormal hst _ => cases hst
  | consReturn hst => cases hst with | «return» hvs => exact Or.inr ⟨_, hvs, rfl⟩
  | consRevert hst => cases hst with | returnRevert hv => exact Or.inl ⟨hv, rfl⟩
  | consBreak hst => cases hst
  | consContinue hst => cases hst
  | consStatic hst => cases hst

/-! ## The `x ≥ 0` branch -/

theorem wExp_else_result {x : Int} (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x))
    (h : ExecBlock wexpConfig stele evm wExpElseBody r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int (specWExpPos x)]) := by
  unfold wExpElseBody at h
  -- q
  rcases execBlock_letDecl h with ⟨hv, -⟩ | ⟨v0, hv0, hb⟩
  · rw [eval_q hl] at hv; cases hv
  rw [eval_q hl] at hv0; cases hv0
  -- r
  rcases execBlock_letDecl hb with ⟨hv, -⟩ | ⟨v1, hv1, hb⟩
  · rw [eval_r (fr := {stele with locals := stele.locals.insert "q" (.int (qOf x))})
      (get_insert_ne _ (by decide) hl) (get_insert_same _ _ _)] at hv; cases hv
  rw [eval_r (fr := {stele with locals := stele.locals.insert "q" (.int (qOf x))})
      (get_insert_ne _ (by decide) hl) (get_insert_same _ _ _)] at hv1; cases hv1
  -- secondTerm
  rcases execBlock_letDecl hb with ⟨hv, -⟩ | ⟨v2, hv2, hb⟩
  · rw [eval_second (fr := {stele with locals := (stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))}) (get_insert_same _ _ _)] at hv; cases hv
  rw [eval_second (fr := {stele with locals := (stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))}) (get_insert_same _ _ _)] at hv2; cases hv2
  -- thirdTerm
  rcases execBlock_letDecl hb with ⟨hv, -⟩ | ⟨v3, hv3, hb⟩
  · rw [eval_third (fr := {stele with locals := ((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))})
      (get_insert_same _ _ _) (get_insert_ne _ (by decide) (get_insert_same _ _ _))]
      at hv; cases hv
  rw [eval_third (fr := {stele with locals := ((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))})
      (get_insert_same _ _ _) (get_insert_ne _ (by decide) (get_insert_same _ _ _))]
    at hv3; cases hv3
  -- expR
  rcases execBlock_letDecl hb with ⟨hv, -⟩ | ⟨v4, hv4, hb⟩
  · rw [eval_expR (fr := {stele with locals := (((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))).insert "thirdTerm" (.int (tOf (rOf x)))})
      (get_insert_ne _ (by decide) (get_insert_ne _ (by decide) (get_insert_same _ _ _)))
      (get_insert_ne _ (by decide) (get_insert_same _ _ _)) (get_insert_same _ _ _)] at hv; cases hv
  rw [eval_expR (fr := {stele with locals := (((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))).insert "thirdTerm" (.int (tOf (rOf x)))})
      (get_insert_ne _ (by decide) (get_insert_ne _ (by decide) (get_insert_same _ _ _)))
      (get_insert_ne _ (by decide) (get_insert_same _ _ _)) (get_insert_same _ _ _)]
    at hv4; cases hv4
  -- return
  rcases execBlock_return hb with ⟨hv, -⟩ | ⟨vs, hvs, hr⟩
  · have hret : evalExprs? wexpConfig {stele with locals := ((((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))).insert "thirdTerm" (.int (tOf (rOf x)))).insert "expR" (.int (poly (rOf x)))} evm
        [.binary (.shl (.uint ⟨256, by decide⟩)) (.cast (.var "expR") uint256)
          (.cast (.var "q") uint256)] = .ok [.int (specWExpPos x)] := by
      simp only [evalExprs?, EvalResult.bind, bind, pure,
        eval_ret (fr := {stele with locals := ((((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))).insert "thirdTerm" (.int (tOf (rOf x)))).insert "expR" (.int (poly (rOf x)))})
          hx0 hxm (get_insert_same _ _ _)
          (get_insert_ne _ (by decide) (get_insert_ne _ (by decide) (get_insert_ne _ (by decide)
            (get_insert_ne _ (by decide) (get_insert_same _ _ _)))))]
    rw [hret] at hv; cases hv
  · have hret : evalExprs? wexpConfig {stele with locals := ((((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))).insert "thirdTerm" (.int (tOf (rOf x)))).insert "expR" (.int (poly (rOf x)))} evm
        [.binary (.shl (.uint ⟨256, by decide⟩)) (.cast (.var "expR") uint256)
          (.cast (.var "q") uint256)] = .ok [.int (specWExpPos x)] := by
      simp only [evalExprs?, EvalResult.bind, bind, pure,
        eval_ret (fr := {stele with locals := ((((stele.locals.insert "q" (.int (qOf x))).insert "r" (.int (rOf x))).insert "secondTerm" (.int (sOf (rOf x)))).insert "thirdTerm" (.int (tOf (rOf x)))).insert "expR" (.int (poly (rOf x)))})
          hx0 hxm (get_insert_same _ _ _)
          (get_insert_ne _ (by decide) (get_insert_ne _ (by decide) (get_insert_ne _ (by decide)
            (get_insert_ne _ (by decide) (get_insert_same _ _ _)))))]
    rw [hret] at hvs; cases hvs
    exact ⟨_, _, hr⟩

theorem wExp_block_nonneg {x : Int} (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x))
    (h : ExecBlock wexpConfig stele evm wExpFunction.body r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int (specWExpPos x)]) := by
  rw [show wExpFunction.body = [.ite wExpCond wExpThenBody wExpElseBody] from rfl] at h
  rcases execBlock_ite h with ⟨hc, -⟩ | ⟨hc, hb⟩ | ⟨-, hb⟩
  · rw [eval_cond_false hl hx0] at hc; cases hc
  · rw [eval_cond_false hl hx0] at hc; cases hc
  · rw [List.append_nil] at hb; exact wExp_else_result hx0 hxm hl hb

theorem wExp_funcbody_nonneg {x : Int} (hx0 : 0 ≤ x) (hxm : x ≤ MAXINPUT)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x))
    (h : ExecFuncBody wexpConfig stele evm wExpFunction.body r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int (specWExpPos x)]) := by
  cases h with
  | execBlockOK hb => obtain ⟨_, _, hr⟩ := wExp_block_nonneg hx0 hxm hl hb; cases hr
  | execBlockRet hb => obtain ⟨_, _, hr⟩ := wExp_block_nonneg hx0 hxm hl hb; exact ⟨_, _, hr⟩
  | execBlockRevert hb => obtain ⟨_, _, hr⟩ := wExp_block_nonneg hx0 hxm hl hb; cases hr
  | execBlockBreak hb => obtain ⟨_, _, hr⟩ := wExp_block_nonneg hx0 hxm hl hb; cases hr
  | execBlockContinue hb => obtain ⟨_, _, hr⟩ := wExp_block_nonneg hx0 hxm hl hb; cases hr
  | execBlockStatic hb => obtain ⟨_, _, hr⟩ := wExp_block_nonneg hx0 hxm hl hb; cases hr

/-! ## The `x < 0` branch -/

theorem wExp_then_result {x : Int} (hxm : -MAXINPUT ≤ x) (hx : x < 0)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x)) (hc : stele.contract = wexpContract)
    (h : ExecBlock wexpConfig stele evm wExpThenBody r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int ((10 ^ 36 : Int) / specWExpPos (-x))]) := by
  unfold wExpThenBody at h
  rcases execBlock_internalCall h with ⟨vals, callee, locals, fr0, evm0, v0,
      hargs, hcall, hbind, hbody, hb⟩ | ⟨vals, callee, locals, hargs, hcall, hbind, hbody, hrr⟩
      | ⟨hargs, hrr⟩ | ⟨vals, callee, locals, hargs, hcall, hbind, hbody, hrr⟩
  · -- success: the callee returns specWExpPos(-x), then `return 1e36 / __pos`
    rw [eval_arg_neg hl] at hargs; cases hargs
    have hcf : lookupCallable? wexpContract "wExp" = some wExpFunction.toCallable := by rfl
    rw [hc] at hcall; rw [hcf] at hcall; cases hcall
    have hb2 : bindParams? wExpFunction.toCallable.params [.int (-x)] =
        some ((∅ : Store).insert "x" (.int (-x))) := by rfl
    rw [hb2] at hbind; cases hbind
    have hx0 : 0 ≤ -x := by omega
    have hxm2 : -x ≤ MAXINPUT := by omega
    have hbody' : ExecFuncBody wexpConfig
        {stele with locals := (∅ : Store).insert "x" (.int (-x))} evm wExpFunction.body
        (.returned fr0 evm0 v0) := hbody
    obtain ⟨_, _, hres⟩ := wExp_funcbody_nonneg hx0 hxm2
      (get_insert_same (∅ : Store) "x" (.int (-x))) hbody'
    cases hres
    rcases execBlock_return hb with ⟨hv, -⟩ | ⟨vs, hvs, hr⟩
    · have hpos : specWExpPos (-x) ≠ 0 := ne_of_gt (specWExpPos_pos hx0 hxm2)
      have hget : (resumeAfterInternalCall stele "__pos" (some [Value.int (specWExpPos (-x))])).locals.get? "__pos" = some (.int (specWExpPos (-x))) := by
        simp only [resumeAfterInternalCall, collapseReturns, get_insert_same]
      rw [eval_div hget hpos] at hv; cases hv
    · have hpos : specWExpPos (-x) ≠ 0 := ne_of_gt (specWExpPos_pos hx0 hxm2)
      have hget : (resumeAfterInternalCall stele "__pos" (some [Value.int (specWExpPos (-x))])).locals.get? "__pos" = some (.int (specWExpPos (-x))) := by
        simp only [resumeAfterInternalCall, collapseReturns, get_insert_same]
      rw [eval_div hget hpos] at hvs; cases hvs
      exact ⟨_, _, hr⟩
  · -- the callee cannot revert: the non-negative branch always returns
    rw [eval_arg_neg hl] at hargs; cases hargs
    have hcf : lookupCallable? wexpContract "wExp" = some wExpFunction.toCallable := by rfl
    rw [hc] at hcall; rw [hcf] at hcall; cases hcall
    have hb2 : bindParams? wExpFunction.toCallable.params [.int (-x)] =
        some ((∅ : Store).insert "x" (.int (-x))) := by rfl
    rw [hb2] at hbind; cases hbind
    have hbody' : ExecFuncBody wexpConfig
        {stele with locals := (∅ : Store).insert "x" (.int (-x))} evm wExpFunction.body
        .reverted := hbody
    obtain ⟨_, _, hres⟩ := wExp_funcbody_nonneg (x := -x) (by omega) (by omega)
      (get_insert_same (∅ : Store) "x" (.int (-x))) hbody'
    cases hres
  · -- argument evaluation cannot revert
    rw [eval_arg_neg hl] at hargs; cases hargs
  · -- the callee cannot static-violate either
    rw [eval_arg_neg hl] at hargs; cases hargs
    have hcf : lookupCallable? wexpContract "wExp" = some wExpFunction.toCallable := by rfl
    rw [hc] at hcall; rw [hcf] at hcall; cases hcall
    have hb2 : bindParams? wExpFunction.toCallable.params [.int (-x)] =
        some ((∅ : Store).insert "x" (.int (-x))) := by rfl
    rw [hb2] at hbind; cases hbind
    have hbody' : ExecFuncBody wexpConfig
        {stele with locals := (∅ : Store).insert "x" (.int (-x))} evm wExpFunction.body
        .staticViolation := hbody
    obtain ⟨_, _, hres⟩ := wExp_funcbody_nonneg (x := -x) (by omega) (by omega)
      (get_insert_same (∅ : Store) "x" (.int (-x))) hbody'
    cases hres

/-! ## Unified result over `[-maxInput, maxInput]` -/

theorem wExp_block_result {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x)) (hc : stele.contract = wexpContract)
    (h : ExecBlock wexpConfig stele evm wExpFunction.body r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int (specWExp x)]) := by
  rw [show wExpFunction.body = [.ite wExpCond wExpThenBody wExpElseBody] from rfl] at h
  rcases execBlock_ite h with ⟨hc0, hrr⟩ | ⟨hc0, hb⟩ | ⟨hc0, hb⟩
  · rw [eval_cond hl] at hc0; cases hc0
  · rw [eval_cond hl] at hc0; simp only [EvalResult.ok.injEq, Value.bool.injEq,
      decide_eq_true_eq] at hc0
    rw [List.append_nil] at hb
    unfold specWExp; rw [if_pos hc0]
    exact wExp_then_result hlo hc0 hl hc hb
  · rw [eval_cond hl] at hc0; simp only [EvalResult.ok.injEq, Value.bool.injEq] at hc0
    have hx0 : 0 ≤ x := by simp at hc0; omega
    rw [List.append_nil] at hb
    unfold specWExp; rw [if_neg (by omega)]
    exact wExp_else_result hx0 hhi hl hb

theorem wExp_result {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x)) (hc : stele.contract = wexpContract)
    (h : ExecFuncBody wexpConfig stele evm wExpFunction.body r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int (specWExp x)]) := by
  cases h with
  | execBlockOK hb => obtain ⟨_, _, hr⟩ := wExp_block_result hlo hhi hl hc hb; cases hr
  | execBlockRet hb => obtain ⟨_, _, hr⟩ := wExp_block_result hlo hhi hl hc hb; exact ⟨_, _, hr⟩
  | execBlockRevert hb => obtain ⟨_, _, hr⟩ := wExp_block_result hlo hhi hl hc hb; cases hr
  | execBlockBreak hb => obtain ⟨_, _, hr⟩ := wExp_block_result hlo hhi hl hc hb; cases hr
  | execBlockContinue hb => obtain ⟨_, _, hr⟩ := wExp_block_result hlo hhi hl hc hb; cases hr
  | execBlockStatic hb => obtain ⟨_, _, hr⟩ := wExp_block_result hlo hhi hl hc hb; cases hr

/-! ## External wrapper transition -/

theorem wExpExternal_block {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x)) (hc : stele.contract = wexpContract)
    (h : ExecBlock wexpConfig stele evm wExpExternal.body r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int (specWExp x)]) := by
  rw [show wExpExternal.body = [.internalCall "wExp" [.var "x"] "__w",
      .return [.var "__w"]] from rfl] at h
  rcases execBlock_internalCall h with ⟨vals, callee, locals, fr0, evm0, v0,
      hargs, hcall, hbind, hbody, hb⟩ | ⟨vals, callee, locals, hargs, hcall, hbind, hbody, hrr⟩
      | ⟨hargs, hrr⟩ | ⟨vals, callee, locals, hargs, hcall, hbind, hbody, hrr⟩
  · have hargs' : evalExprs? wexpConfig stele evm [.var "x"] = .ok [.int x] := by
      simp only [evalExprs?, eval_var hl, EvalResult.bind, bind, pure]
    rw [hargs'] at hargs; cases hargs
    have hcf : lookupCallable? wexpContract "wExp" = some wExpFunction.toCallable := by rfl
    rw [hc] at hcall; rw [hcf] at hcall; cases hcall
    have hpb : bindParams? wExpFunction.toCallable.params [.int x] =
        some ((∅ : Store).insert "x" (.int x)) := by rfl
    rw [hpb] at hbind; cases hbind
    have hbody' : ExecFuncBody wexpConfig
        {stele with locals := (∅ : Store).insert "x" (.int x)} evm wExpFunction.body
        (.returned fr0 evm0 v0) := hbody
    have hcc : ({stele with locals := (∅ : Store).insert "x" (.int x)} : Frame).contract =
        wexpContract := hc
    obtain ⟨_, _, hres⟩ := wExp_result hlo hhi
      (get_insert_same (∅ : Store) "x" (.int x)) hcc hbody'
    cases hres
    rcases execBlock_return hb with ⟨hv, -⟩ | ⟨vs, hvs, hr⟩
    · have hget : (resumeAfterInternalCall stele "__w" (some [.int (specWExp x)])).locals.get? "__w" = some (.int (specWExp x)) := by
        simp only [resumeAfterInternalCall, collapseReturns, get_insert_same]
      have hret : evalExprs? wexpConfig
          (resumeAfterInternalCall stele "__w" (some [.int (specWExp x)])) evm0 [.var "__w"]
          = .ok [.int (specWExp x)] := by
        simp only [evalExprs?, eval_var hget, EvalResult.bind, bind, pure]
      rw [hret] at hv; cases hv
    · have hget : (resumeAfterInternalCall stele "__w" (some [.int (specWExp x)])).locals.get? "__w" = some (.int (specWExp x)) := by
        simp only [resumeAfterInternalCall, collapseReturns, get_insert_same]
      have hret : evalExprs? wexpConfig
          (resumeAfterInternalCall stele "__w" (some [.int (specWExp x)])) evm0 [.var "__w"]
          = .ok [.int (specWExp x)] := by
        simp only [evalExprs?, eval_var hget, EvalResult.bind, bind, pure]
      rw [hret] at hvs; cases hvs
      exact ⟨_, _, hr⟩
  · have hargs' : evalExprs? wexpConfig stele evm [.var "x"] = .ok [.int x] := by
      simp only [evalExprs?, eval_var hl, EvalResult.bind, bind, pure]
    rw [hargs'] at hargs; cases hargs
    have hcf : lookupCallable? wexpContract "wExp" = some wExpFunction.toCallable := by rfl
    rw [hc] at hcall; rw [hcf] at hcall; cases hcall
    have hpb : bindParams? wExpFunction.toCallable.params [.int x] =
        some ((∅ : Store).insert "x" (.int x)) := by rfl
    rw [hpb] at hbind; cases hbind
    have hbody' : ExecFuncBody wexpConfig
        {stele with locals := (∅ : Store).insert "x" (.int x)} evm wExpFunction.body
        .reverted := hbody
    have hcc : ({stele with locals := (∅ : Store).insert "x" (.int x)} : Frame).contract =
        wexpContract := hc
    obtain ⟨_, _, hres⟩ := wExp_result hlo hhi
      (get_insert_same (∅ : Store) "x" (.int x)) hcc hbody'
    cases hres
  · have hargs' : evalExprs? wexpConfig stele evm [.var "x"] = .ok [.int x] := by
      simp only [evalExprs?, eval_var hl, EvalResult.bind, bind, pure]
    rw [hargs'] at hargs; cases hargs
  · have hargs' : evalExprs? wexpConfig stele evm [.var "x"] = .ok [.int x] := by
      simp only [evalExprs?, eval_var hl, EvalResult.bind, bind, pure]
    rw [hargs'] at hargs; cases hargs
    have hcf : lookupCallable? wexpContract "wExp" = some wExpFunction.toCallable := by rfl
    rw [hc] at hcall; rw [hcf] at hcall; cases hcall
    have hpb : bindParams? wExpFunction.toCallable.params [.int x] =
        some ((∅ : Store).insert "x" (.int x)) := by rfl
    rw [hpb] at hbind; cases hbind
    have hbody' : ExecFuncBody wexpConfig
        {stele with locals := (∅ : Store).insert "x" (.int x)} evm wExpFunction.body
        .staticViolation := hbody
    have hcc : ({stele with locals := (∅ : Store).insert "x" (.int x)} : Frame).contract =
        wexpContract := hc
    obtain ⟨_, _, hres⟩ := wExp_result hlo hhi
      (get_insert_same (∅ : Store) "x" (.int x)) hcc hbody'
    cases hres

theorem wExpExternal_result {x : Int} (hlo : -MAXINPUT ≤ x) (hhi : x ≤ MAXINPUT)
    {stele : Frame} {evm : EVM.State} {r : ExecResult}
    (hl : stele.locals.get? "x" = some (.int x)) (hc : stele.contract = wexpContract)
    (h : ExecFuncBody wexpConfig stele evm wExpExternal.body r) :
    ∃ fr' evm', r = .returned fr' evm' (some [.int (specWExp x)]) := by
  cases h with
  | execBlockOK hb => obtain ⟨_, _, hr⟩ := wExpExternal_block hlo hhi hl hc hb; cases hr
  | execBlockRet hb => obtain ⟨_, _, hr⟩ := wExpExternal_block hlo hhi hl hc hb; exact ⟨_, _, hr⟩
  | execBlockRevert hb => obtain ⟨_, _, hr⟩ := wExpExternal_block hlo hhi hl hc hb; cases hr
  | execBlockBreak hb => obtain ⟨_, _, hr⟩ := wExpExternal_block hlo hhi hl hc hb; cases hr
  | execBlockContinue hb => obtain ⟨_, _, hr⟩ := wExpExternal_block hlo hhi hl hc hb; cases hr
  | execBlockStatic hb => obtain ⟨_, _, hr⟩ := wExpExternal_block hlo hhi hl hc hb; cases hr

end WExp
