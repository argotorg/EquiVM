import Solidity.Theory.InterpLemmas

/-! # Soundness steps: the small members of the interpreter. -/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

theorem evalValueOpt_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m e r, (evalValueOpt cfg o fc (n+1) fr m e).run = some r → EvalValueOpt cfg o fc fr m e (resOf r) := by
  intro fr m e r h
  cases e with
  | none =>
    simp only [evalValueOpt] at h
    rw [IM.pure_some h]; exact .none
  | some e =>
    simp only [evalValueOpt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .revert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨k, hk, h⟩
      · exact (liftOpt_error hd).elim
      · rw [IM.pure_some h]
        exact .some (ih.expr _ _ _ _ hv) (liftOpt_ok hk)

theorem evalSaltOpt_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m e r, (evalSaltOpt cfg o fc (n+1) fr m e).run = some r → EvalSaltOpt cfg o fc fr m e (resOf r) := by
  intro fr m e r h
  cases e with
  | none =>
    simp only [evalSaltOpt] at h
    rw [IM.pure_some h]; exact .none
  | some e =>
    simp only [evalSaltOpt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .revert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨s, hs, h⟩
      · exact (liftOpt_error hd).elim
      · rw [IM.pure_some h]
        exact .some (ih.expr _ _ _ _ hv) (liftOpt_ok hs)

theorem evalGasOpt_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m e r, (evalGasOpt cfg o fc (n+1) fr m e).run = some r → EvalGasOpt cfg o fc fr m e (resOf r) := by
  intro fr m e r h
  cases e with
  | none =>
    simp only [evalGasOpt] at h
    rw [IM.pure_some h]; exact .none
  | some e =>
    simp only [evalGasOpt] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .revert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨k, hk, h⟩
      · exact (liftOpt_error hd).elim
      · rw [IM.pure_some h]
        exact .some (ih.expr _ _ _ _ hv) (liftOpt_ok hk)

theorem evalExprs_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m es r, (evalExprs cfg o fc (n+1) fr m es).run = some r → EvalExprs cfg o fc fr m es (resOf r) := by
  intro fr m es r h
  cases es with
  | nil =>
    simp only [evalExprs] at h
    rw [IM.pure_some h]; exact .nil
  | cons e es =>
    simp only [evalExprs] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .headRevert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr2, m2⟩, hvs, h⟩ <;> try dsimp only at h
      · exact .tailRevert (ih.expr _ _ _ _ hv) (ih.exprs _ _ _ _ hd)
      · rw [IM.pure_some h]
        exact .cons (ih.expr _ _ _ _ hv) (ih.exprs _ _ _ _ hvs)

theorem evalLValue_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m e r, (evalLValue cfg o fc (n+1) fr m e).run = some r → EvalLValue cfg o fc fr m e (resOf r) := by
  intro fr m e r h
  cases e with
  | ident x =>
    simp only [evalLValue] at h
    split at h
    · rename_i l hl
      rw [IM.pure_some h]; exact .local hl
    · rename_i hx
      split at h
      · rename_i v hv
        split at h
        · rename_i hmut; rw [IM.pure_some h]; exact .stateVar hx hv hmut
        · rename_i hmut; rw [IM.pure_some h]; exact .immutableVar hx hv hmut
        · exact (IM.failure_some h).elim
      · exact (IM.failure_some h).elim
  | member e f =>
    simp only [evalLValue] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .memberRevert (ih.expr _ _ _ _ hd)
    · split at h
      · rename_i er ty
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨er', fty⟩, hf, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rw [IM.pure_some h]; exact .memberStorage (ih.expr _ _ _ _ hv) (liftOpt_ok hf)
      · rename_i obj
        rw [IM.pure_some h]; exact .memberMem (ih.expr _ _ _ _ hv)
      · exact (IM.failure_some h).elim
  | index e i =>
    simp only [evalLValue] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨base, fr1, m1⟩, hb, h⟩ <;> try dsimp only at h
    · exact .indexBaseRevert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨iv, fr2, m2⟩, hi, h⟩ <;> try dsimp only at h
      · exact .indexRevert (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ hd)
      · split at h
        · rename_i er ty
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨er', ty'⟩, hs, h⟩ <;> try dsimp only at h
          · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
            exact .indexStoragePanic (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ hi) hp
          · rw [IM.pure_some h]
            exact .indexStorage (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ hi) (liftOp_ok hs)
        · rename_i obj
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨k, hk, h⟩
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨len, hlen, h⟩
            · exact (liftOpt_error hd).elim
            · split at h
              · rename_i hlt
                rw [IM.pure_some h]
                exact .indexMem (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ hi) (liftOpt_ok hk) (liftOpt_ok hlen) hlt
              · rename_i hge
                rw [IM.throw_some h]
                exact .indexMemPanic (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ hi) (liftOpt_ok hk) (liftOpt_ok hlen)
                  (Nat.le_of_not_lt hge)
        · exact (IM.failure_some h).elim
  | _ => simp [evalLValue] at h

theorem assignTuple_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m ls vs r, (assignTuple cfg o fc (n+1) fr m ls vs).run = some r →
      AssignTuple cfg o fc fr m ls vs (unitResOf r) := by
  intro fr m ls vs r h
  match ls, vs with
  | [], [] =>
    simp only [assignTuple] at h
    rw [IM.pure_some h]; exact .nil
  | none :: ls, v :: vs =>
    simp only [assignTuple] at h
    exact .skip (ih.assignTuple _ _ _ _ _ h)
  | some l :: ls, v :: vs =>
    simp only [assignTuple] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨lv, fr1, m1⟩, hl, h⟩ <;> try dsimp only at h
    · exact .revert (ih.lvalue _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, ha, h⟩ <;> try dsimp only at h
      · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
        exact .assignPanic (ih.lvalue _ _ _ _ hl) hp
      · exact .cons (ih.lvalue _ _ _ _ hl) (liftOp_ok ha) (ih.assignTuple _ _ _ _ _ h)
  | [], _ :: _ => simp [assignTuple] at h
  | _ :: _, [] => simp [assignTuple] at h

theorem declareTuple_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m bs vs r, (declareTuple cfg o fc (n+1) fr m bs vs).run = some r →
      DeclareTuple cfg o fc fr m bs vs (unitResOf r) := by
  intro fr m bs vs r h
  match bs, vs with
  | [], [] =>
    simp only [declareTuple] at h
    rw [IM.pure_some h]; exact .nil
  | none :: bs, v :: vs =>
    simp only [declareTuple] at h
    exact .skip (ih.declareTuple _ _ _ _ _ h)
  | some p :: bs, v :: vs =>
    simp only [declareTuple] at h
    split at h
    · rename_i x hx
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr1, m1⟩, hdecl, h⟩ <;> try dsimp only at h
      · obtain ⟨q, hq, rfl⟩ := liftOp_error hd
        exact .panic hx hq
      · exact .cons hx (liftOp_ok hdecl) (ih.declareTuple _ _ _ _ _ h)
    · exact (IM.failure_some h).elim
  | [], _ :: _ => simp [declareTuple] at h
  | _ :: _, [] => simp [declareTuple] at h

theorem execBlock_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m ss r, (execBlock cfg o fc (n+1) fr m ss).run = some r → ExecBlock cfg o fc fr m ss (execOf r) := by
  intro fr m ss r h
  cases ss with
  | nil =>
    simp only [execBlock] at h
    rw [IM.pure_some h]; exact .nil
  | cons s ss =>
    simp only [execBlock] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨a, ha, h⟩
    · exact .consRevert (ih.stmt _ _ _ _ hd)
    · have hs := ih.stmt _ _ _ _ ha
      cases a with
      | normal fr1 m1 => exact .cons hs (ih.block _ _ _ _ h)
      | returned fr1 m1 => rw [IM.pure_some h]; exact .consReturn hs
      | «break» fr1 m1 => rw [IM.pure_some h]; exact .consBreak hs
      | «continue» fr1 m1 => rw [IM.pure_some h]; exact .consContinue hs
      | reverted d => rw [IM.throw_some h]; exact .consRevert hs

theorem execChain_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m mods body r, (execChain cfg o fc (n+1) fr m mods body).run = some r →
      ExecChain cfg o fc fr m mods body (execOf r) := by
  intro fr m mods body r h
  cases mods with
  | nil =>
    simp only [execChain] at h
    exact .body (ih.block _ _ _ _ h)
  | cons mi rest =>
    simp only [execChain] at h
    split at h
    · rename_i md hmd
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
        · exact .modifierArgsRevert hmd (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, hb, h⟩ <;> try dsimp only at h
          · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
            exact .modifierPanic hmd (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) hp
          · split at h
            · rename_i mb hmb
              rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩
              · exact .modifier hmd (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hb) hmb (ih.block _ _ _ _ hd)
              · rw [IM.pure_some h]
                exact .modifier hmd (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hb) hmb (ih.block _ _ _ _ hr)
            · exact (IM.failure_some h).elim
    · rename_i hmd
      split at h
      · rename_i hlin
        exact .skipBase hmd hlin (ih.chain _ _ _ _ _ h)
      · exact (IM.failure_some h).elim

theorem callFn_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m fn args r, (callFn cfg o fc (n+1) fr m fn args).run = some r → CallFn cfg o fc fr m fn args (fnOf r) := by
  intro fr m fn args r h
  simp only [callFn] at h
  rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr0, m0⟩, he, h⟩ <;> try dsimp only at h
  · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
    exact .enterPanic hp
  · split at h
    · rename_i body hbody
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩
      · exact .reverted (liftOp_ok he) hbody (ih.chain _ _ _ _ _ hd)
      · have hc := ih.chain _ _ _ _ _ hr
        cases r' with
        | reverted d => rw [IM.throw_some h]; exact .reverted (liftOp_ok he) hbody hc
        | normal fr2 m2 =>
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2', m2'⟩, hf, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨rets, hrets, h⟩
            · exact (liftOpt_error hd).elim
            · rw [IM.pure_some h]
              exact .ok (liftOp_ok he) hbody hc (liftOpt_ok hf) (liftOpt_ok hrets)
        | returned fr2 m2 =>
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2', m2'⟩, hf, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨rets, hrets, h⟩
            · exact (liftOpt_error hd).elim
            · rw [IM.pure_some h]
              exact .ok (liftOp_ok he) hbody hc (liftOpt_ok hf) (liftOpt_ok hrets)
        | «break» fr2 m2 =>
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2', m2'⟩, hf, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · exact absurd (liftOpt_ok hf) (by simp [finished])
        | «continue» fr2 m2 =>
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2', m2'⟩, hf, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · exact absurd (liftOpt_ok hf) (by simp [finished])
    · exact (IM.failure_some h).elim

end Solidity
