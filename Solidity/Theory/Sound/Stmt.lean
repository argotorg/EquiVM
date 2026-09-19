import Solidity.Theory.InterpLemmas

/-! # Soundness steps: statements and loops. -/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

theorem execLoopBody_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m c post body fr1 m1 r, EvalCond cfg o fc fr m c (.ok true fr1 m1) →
      (execLoopBody cfg o fc (n+1) fr1 m1 c post body).run = some r →
      ExecLoop cfg o fc fr m c post body (execOf r) := by
  intro fr m c post body fr1 m1 r hc h
  simp only [execLoopBody] at h
  rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩
  · exact .bodyRevert hc (ih.stmt _ _ _ _ hd)
  · have hs := ih.stmt _ _ _ _ hr
    cases r' with
    | reverted d => rw [IM.throw_some h]; exact .bodyRevert hc hs
    | «break» fr2 m2 => rw [IM.pure_some h]; exact .breakOut hc hs
    | returned fr2 m2 => rw [IM.pure_some h]; exact .returnOut hc hs
    | normal fr2 m2 =>
      rcases post with _ | pe
      · dsimp only at h
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨y, hp, h⟩ <;> try dsimp only at h
        · cases (IM.pure_some hd)
        · cases (IM.pure_some hp)
          exact .iterate hc hs .none (ih.loop _ _ _ _ _ _ h)
      · dsimp only at h
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr3, m3⟩, hv, h⟩ <;> try dsimp only at h
        · exact .postRevert hc hs (.revert (ih.expr _ _ _ _ hd))
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨y, hp, h⟩ <;> try dsimp only at h
          · cases (IM.pure_some hd)
          · cases (IM.pure_some hp)
            exact .iterate hc hs (.some (ih.expr _ _ _ _ hv)) (ih.loop _ _ _ _ _ _ h)
    | «continue» fr2 m2 =>
      rcases post with _ | pe
      · dsimp only at h
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨y, hp, h⟩ <;> try dsimp only at h
        · cases (IM.pure_some hd)
        · cases (IM.pure_some hp)
          exact .iterateContinue hc hs .none (ih.loop _ _ _ _ _ _ h)
      · dsimp only at h
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr3, m3⟩, hv, h⟩ <;> try dsimp only at h
        · exact .postRevertContinue hc hs (.revert (ih.expr _ _ _ _ hd))
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨y, hp, h⟩ <;> try dsimp only at h
          · cases (IM.pure_some hd)
          · cases (IM.pure_some hp)
            exact .iterateContinue hc hs (.some (ih.expr _ _ _ _ hv)) (ih.loop _ _ _ _ _ _ h)

theorem execLoop_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m c post body r, (execLoop cfg o fc (n+1) fr m c post body).run = some r →
      ExecLoop cfg o fc fr m c post body (execOf r) := by
  intro fr m c post body r h
  simp only [execLoop] at h
  -- `h` after the condition: `let y ← pure (b, fr1, m1); if !y.1 then ... else execLoopBody ...`
  have tail : ∀ (b : Bool) fr1 m1, EvalCond cfg o fc fr m c (.ok b fr1 m1) →
      (b = false → c ≠ none) →
      ((pure (b, fr1, m1) : IM (Bool × Frame × Machine)) >>= fun y =>
        if (!y.1) = true then pure (.normal y.2.1 y.2.2)
        else (pure PUnit.unit : IM PUnit) >>= fun _ => execLoopBody cfg o fc n y.2.1 y.2.2 c post body).run = some r →
      ExecLoop cfg o fc fr m c post body (execOf r) := by
    intro b fr1 m1 hc hne h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨y, hy, h⟩
    · cases (IM.pure_some hd)
    · cases (IM.pure_some hy)
      cases b
      · simp only [Bool.not_false, ite_true] at h
        rw [IM.pure_some h]
        cases hc with
        | some hce => exact .condFalse hce
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u, hu, h⟩ <;> try dsimp only at h
        · cases (IM.pure_some hd)
        · exact ih.loopBody _ _ _ _ _ _ _ _ hc h
  rcases c with _ | ce
  · dsimp only at h
    exact tail true fr m .none (fun h => by cases h) h
  · dsimp only at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨cv, fr1, m1⟩, hcv, h⟩ <;> try dsimp only at h
    · exact .condRevert (ih.expr _ _ _ _ hd)
    · split at h
      · rename_i b
        exact tail b fr1 m1 (.some (ih.expr _ _ _ _ hcv)) (fun _ h => by cases h) h
      · simp at h

theorem execStmt_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m s r, (execStmt cfg o fc (n+1) fr m s).run = some r → ExecStmt cfg o fc fr m s (execOf r) := by
  intro fr m s r h
  cases s with
  | block ss =>
    simp only [execStmt] at h
    exact .block (ih.block _ _ _ _ h)
  | varDecl ty loc x init =>
    cases init with
    | none =>
      simp only [execStmt] at h
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr', m'⟩, hdecl, h⟩ <;> try dsimp only at h
      · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
        exact .varDeclNonePanic hp
      · rw [IM.pure_some h]; exact .varDeclNone (liftOp_ok hdecl)
    | some e =>
      simp only [execStmt] at h
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
      · exact .varDeclRevert (ih.expr _ _ _ _ hd)
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, hdecl, h⟩ <;> try dsimp only at h
        · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
          exact .varDeclPanic (ih.expr _ _ _ _ hv) hp
        · rw [IM.pure_some h]; exact .varDecl (ih.expr _ _ _ _ hv) (liftOp_ok hdecl)
  | tupleDecl binders rhs =>
    simp only [execStmt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .tupleDeclRevert (ih.expr _ _ _ _ hd)
    · split at h
      · rename_i vs
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, hdt, h⟩ <;> try dsimp only at h
        · exact .tupleDeclPanic (ih.expr _ _ _ _ hv) (ih.declareTuple _ _ _ _ _ hd)
        · rw [IM.pure_some h]; exact .tupleDecl (ih.expr _ _ _ _ hv) (ih.declareTuple _ _ _ _ _ hdt)
      · simp at h
  | exprStmt e =>
    simp only [execStmt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .exprStmtRevert (ih.expr _ _ _ _ hd)
    · rw [IM.pure_some h]; exact .exprStmt (ih.expr _ _ _ _ hv)
  | ite c t e =>
    simp only [execStmt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨cv, fr1, m1⟩, hcv, h⟩ <;> try dsimp only at h
    · exact .iteRevert (ih.expr _ _ _ _ hd)
    · split at h
      · exact .iteT (ih.expr _ _ _ _ hcv) (ih.stmt _ _ _ _ h)
      · rename_i s
        exact .iteF (ih.expr _ _ _ _ hcv) (ih.stmt _ _ _ _ h)
      · rw [IM.pure_some h]; exact .iteFNone (ih.expr _ _ _ _ hcv)
      · simp at h
  | «while» c body =>
    simp only [execStmt] at h
    exact .while (ih.loop _ _ _ _ _ _ h)
  | doWhile body c =>
    simp only [execStmt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩
    · exact .doWhileRevert (ih.stmt _ _ _ _ hd)
    · have hs := ih.stmt _ _ _ _ hr
      cases r' with
      | normal fr1 m1 => exact .doWhile hs (ih.loop _ _ _ _ _ _ h)
      | «continue» fr1 m1 => exact .doWhileContinue hs (ih.loop _ _ _ _ _ _ h)
      | «break» fr1 m1 => rw [IM.pure_some h]; exact .doWhileBreak hs
      | returned fr1 m1 => rw [IM.pure_some h]; exact .doWhileReturn hs
      | reverted d => rw [IM.throw_some h]; exact .doWhileRevert hs
  | «for» init c post body =>
    cases init with
    | none =>
      simp only [execStmt] at h
      exact .forNoInit (ih.loop _ _ _ _ _ _ h)
    | some s =>
      simp only [execStmt] at h
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩
      · exact .forInitRevert (ih.stmt _ _ _ _ hd)
      · have hs := ih.stmt _ _ _ _ hr
        cases r' with
        | normal fr1 m1 => exact .forInit hs (ih.loop _ _ _ _ _ _ h)
        | reverted d => rw [IM.throw_some h]; exact .forInitRevert hs
        | _ => simp at h
  | «break» => simp only [execStmt] at h; rw [IM.pure_some h]; exact .break
  | «continue» => simp only [execStmt] at h; rw [IM.pure_some h]; exact .continue
  | «return» e =>
    cases e with
    | none => simp only [execStmt] at h; rw [IM.pure_some h]; exact .returnNone
    | some e =>
      simp only [execStmt] at h
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
      · exact .returnRevert (ih.expr _ _ _ _ hd)
      · split at h
        · rename_i rv hrv
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, ha, h⟩ <;> try dsimp only at h
          · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
            exact .returnSinglePanic hrv (ih.expr _ _ _ _ hv) hp
          · rw [IM.pure_some h]; exact .returnSingle hrv (ih.expr _ _ _ _ hv) (liftOp_ok ha)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u, hu, h⟩ <;> try dsimp only at h
          · exact (guard'_error hd).elim
          · have hlen : fr.retVars.length ≥ 2 := of_decide_eq_true (guard'_ok hu)
            split at h
            · rename_i vs
              rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, hat, h⟩ <;> try dsimp only at h
              · exact .returnMultiRevert hlen (ih.expr _ _ _ _ hv) (ih.assignTuple _ _ _ _ _ hd)
              · rw [IM.pure_some h]
                exact .returnMulti hlen (ih.expr _ _ _ _ hv) (ih.assignTuple _ _ _ _ _ hat)
            · simp at h
  | emit ev args =>
    cases ev
    case ident evn =>
      simp only [execStmt] at h
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨ei, hei, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
          · exact .emitRevert (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m2⟩, hsvs, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              exact .emitPanic (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) hp
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨le, hle, h⟩ <;> try dsimp only at h
              · exact (liftOpt_error hd).elim
              · rw [IM.pure_some h]
                exact .emit (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hsvs) (liftOpt_ok hle)
    all_goals simp [execStmt] at h
  | revert err args =>
    cases err
    case ident errn =>
      simp only [execStmt] at h
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨ei, hei, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
          · exact .revertErrorArgsRevert (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m2⟩, hsvs, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              exact .revertErrorPanic (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) hp
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨dd, hdd, h⟩ <;> try dsimp only at h
              · exact (liftOpt_error hd).elim
              · rw [IM.throw_some h]
                exact .revertError (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hsvs) (liftOpt_ok hdd)
    all_goals simp [execStmt] at h
  | unchecked ss =>
    simp only [execStmt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩
    · exact .unchecked (ih.block _ _ _ _ hd)
    · rw [IM.pure_some h]; exact .unchecked (ih.block _ _ _ _ hr)
  | placeholder =>
    simp only [execStmt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩
    · exact .placeholder (ih.chain _ _ _ _ _ hd) rfl
    · obtain ⟨a, ha, rfl⟩ := liftOpt_some h
      exact .placeholder (ih.chain _ _ _ _ _ hr) ha
  | tryCatch _ _ _ _ => simp [execStmt] at h

end Solidity
