import Solidity.Theory.InterpLemmas

/-! # Soundness step: expressions (`evalExpr`). -/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

theorem evalExpr_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m e r, (evalExpr cfg o fc (n+1) fr m e).run = some r → EvalExpr cfg o fc fr m e (resOf r) := by
  intro fr m e r h
  simp only [evalExpr] at h
  split at h
  · -- literal
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨v, hv, h⟩ <;> try dsimp only at h
    · exact (liftOpt_error hd).elim
    · rw [IM.pure_some h]; exact .lit (liftOpt_ok hv)
  · -- this
    rw [IM.pure_some h]; exact .thisRef
  · -- identifier
    split at h
    · rename_i l hl
      rw [IM.pure_some h]; exact .local hl
    · rename_i hx
      split at h
      · rename_i v hv
        split at h
        · rename_i hmut
          split at h
          · rename_i e he
            exact .constVar hx hv hmut he (ih.expr _ _ _ _ h)
          · simp at h
        · rename_i hmut
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨val, hval, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rw [IM.pure_some h]; exact .immutableVar hx hv hmut (liftOpt_ok hval)
        · rename_i hmut
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨val, hval, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rw [IM.pure_some h]; exact .stateVar hx hv hmut (liftOpt_ok hval)
      · simp at h
  · -- e.f
    split at h
    · rename_i hdm
      split at h
      · -- obj.f
        rename_i obj
        split at h
        · rename_i henv
          split at h
          · rename_i hmsg
            have hmsg' := hmsg
            simp only [Bool.and_eq_true, beq_iff_eq] at hmsg'
            rw [IM.pure_some h, hmsg'.1, hmsg'.2]
            exact .msgData rfl
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨v, hv, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rw [IM.pure_some h]; exact .envMember henv (liftOpt_ok hv)
        · rename_i henv
          have henv' : isEnvObj obj = false := by simpa using henv
          split at h
          · rename_i en hen
            have hg : fr.get? obj = none := by
              simp only [directMember, henv', Bool.false_or, Bool.and_eq_true, Option.isNone_iff_eq_none] at hdm
              exact hdm.1
            rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨i, hi, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rw [IM.pure_some h]; exact .enumMember henv' hg hen (liftOpt_ok hi)
          · simp at h
      · -- type(T).f
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨v, hv, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rw [IM.pure_some h]; exact .typeMember (liftOpt_ok hv)
      · simp at h
    · rename_i hdm
      exact ih.member _ _ _ _ _ (by simpa using hdm) h
  · -- e[i]
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨base, fr1, m1⟩, hb, h⟩ <;> try dsimp only at h
    · exact .indexBaseRevert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨iv, fr2, m2⟩, hi, h⟩ <;> try dsimp only at h
      · exact .indexRevert (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ hd)
      · have hb' := ih.expr _ _ _ _ hb
        have hi' := ih.expr _ _ _ _ hi
        split at h
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨er', ty'⟩, hs, h⟩ <;> try dsimp only at h
          · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
            exact .indexStoragePanic hb' hi' hp
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨v, hv, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rw [IM.pure_some h]; exact .indexStorage hb' hi' (liftOp_ok hs) (liftOpt_ok hv)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨v, hv, h⟩ <;> try dsimp only at h
          · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
            exact .indexMemPanic hb' hi' hp
          · split at h
            · split at h
              · split at h
                · rename_i v' hval
                  rw [IM.pure_some h]; exact .indexMemRaw hb' hi' (liftOp_ok hv) hval
                · rename_i d hval
                  rw [IM.throw_some h]; exact .indexMemRawRevert hb' hi' (liftOp_ok hv) hval
              · simp at h
            · rename_i hraw
              rw [IM.pure_some h]
              exact .indexMem hb' hi' (liftOp_ok hv) (by simpa using hraw)
        · simp at h
  · -- calls
    exact ih.call _ _ _ _ _ _ h
  · -- unary
    split at h
    · rename_i hinc
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨lv, fr1, m1⟩, hlv, h⟩ <;> try dsimp only at h
      · exact .incDecRevert hinc (ih.lvalue _ _ _ _ hd)
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨cur, hcur, h⟩ <;> try dsimp only at h
        · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
          exact .incDecReadPanic hinc (ih.lvalue _ _ _ _ hlv) hp
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨nv, hnv, h⟩ <;> try dsimp only at h
          · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
            exact .incDecPanic hinc (ih.lvalue _ _ _ _ hlv) (liftOp_ok hcur) hp
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, ha, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              exact .incDecAssignPanic hinc (ih.lvalue _ _ _ _ hlv) (liftOp_ok hcur) (liftOp_ok hnv) hp
            · rw [IM.pure_some h]
              exact .incDec hinc (ih.lvalue _ _ _ _ hlv) (liftOp_ok hcur) (liftOp_ok hnv) (liftOp_ok ha)
    · rename_i hinc
      split at h
      · rename_i hdel
        have hdel' := hdel
        simp only [beq_iff_eq] at hdel'
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨lv, fr1, m1⟩, hlv, h⟩ <;> try dsimp only at h
        · rw [hdel']; exact .deleteRevert (ih.lvalue _ _ _ _ hd)
        · split at h
          · split at h
            · rename_i l hl
              split at h
              · rename_i z h' hz
                rw [IM.pure_some h, hdel']; exact .deleteLocal (ih.lvalue _ _ _ _ hlv) hl hz
              · simp at h
            · simp at h
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨evm', hc, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              rw [hdel']; exact .deleteStoragePanic (ih.lvalue _ _ _ _ hlv) hp
            · rw [IM.pure_some h, hdel']; exact .deleteStorage (ih.lvalue _ _ _ _ hlv) (liftOp_ok hc)
          · simp at h
      · rename_i hdel
        have hdel' := hdel
        simp only [beq_iff_eq] at hdel'
        have hinc' := hinc
        simp only [Bool.not_eq_true] at hinc'
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
        · exact .unaryRevert (ih.expr _ _ _ _ hd) hinc' hdel'
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨rv, hr, h⟩ <;> try dsimp only at h
          · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
            exact .unaryPanic (ih.expr _ _ _ _ hv) hp hinc' hdel'
          · rw [IM.pure_some h]; exact .unary (ih.expr _ _ _ _ hv) (liftOp_ok hr) hinc' hdel'
  · -- a op b: `&&`/`||` short-circuit left to right; other operators evaluate the right operand first
    split at h
    · rename_i hand
      have hand' := hand
      simp only [beq_iff_eq] at hand'
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨va, fr1, m1⟩, ha, h⟩ <;> try dsimp only at h
      · rw [hand']; exact .andLeftRevert (ih.expr _ _ _ _ hd)
      · split at h
        · rw [IM.pure_some h, hand']; exact .andShort (ih.expr _ _ _ _ ha)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vb, fr2, m2⟩, hb, h⟩ <;> try dsimp only at h
          · rw [hand']; exact .andRightRevert (ih.expr _ _ _ _ ha) (ih.expr _ _ _ _ hd)
          · split at h
            · rw [IM.pure_some h, hand']; exact .andFull (ih.expr _ _ _ _ ha) (ih.expr _ _ _ _ hb)
            · simp at h
        · simp at h
    · rename_i hand
      have hop1 := hand
      simp only [beq_iff_eq] at hop1
      split at h
      · rename_i hor
        have hor' := hor
        simp only [beq_iff_eq] at hor'
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨va, fr1, m1⟩, ha, h⟩ <;> try dsimp only at h
        · rw [hor']; exact .orLeftRevert (ih.expr _ _ _ _ hd)
        · split at h
          · rw [IM.pure_some h, hor']; exact .orShort (ih.expr _ _ _ _ ha)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vb, fr2, m2⟩, hb, h⟩ <;> try dsimp only at h
            · rw [hor']; exact .orRightRevert (ih.expr _ _ _ _ ha) (ih.expr _ _ _ _ hd)
            · split at h
              · rw [IM.pure_some h, hor']; exact .orFull (ih.expr _ _ _ _ ha) (ih.expr _ _ _ _ hb)
              · simp at h
          · simp at h
      · rename_i hor
        have hop2 := hor
        simp only [beq_iff_eq] at hop2
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vb, fr1, m1⟩, hb, h⟩ <;> try dsimp only at h
        · exact .binaryRightRevert hop1 hop2 (ih.expr _ _ _ _ hd)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨va, fr2, m2⟩, ha, h⟩ <;> try dsimp only at h
          · exact .binaryLeftRevert hop1 hop2 (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨v, hv, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              exact .binaryPanic hop1 hop2 (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ ha) hp
            · rw [IM.pure_some h]; exact .binary hop1 hop2 (ih.expr _ _ _ _ hb) (ih.expr _ _ _ _ ha) (liftOp_ok hv)
  · -- c ? t : e
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨cv, fr1, m1⟩, hcv, h⟩ <;> try dsimp only at h
    · exact .condRevert (ih.expr _ _ _ _ hd)
    · split at h
      · exact .condT (ih.expr _ _ _ _ hcv) (ih.expr _ _ _ _ h)
      · exact .condF (ih.expr _ _ _ _ hcv) (ih.expr _ _ _ _ h)
      · simp at h
  · -- lhs op= rhs
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .assignRhsRevert (ih.expr _ _ _ _ hd)
    · split at h
      · split at h
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr2, m2⟩, hat, h⟩ <;> try dsimp only at h
          · exact .assignTupleRevert (ih.expr _ _ _ _ hv) (ih.assignTuple _ _ _ _ _ hd)
          · rw [IM.pure_some h]; exact .assignTuple (ih.expr _ _ _ _ hv) (ih.assignTuple _ _ _ _ _ hat)
        · simp at h
      · rename_i htup
        have htup' := htup
        simp only [Bool.not_eq_true] at htup'
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨lv, fr2, m2⟩, hlv, h⟩ <;> try dsimp only at h
        · exact .assignLhsRevert htup' (ih.expr _ _ _ _ hv) (ih.lvalue _ _ _ _ hd)
        · split at h
          · rename_i hop
            have hop' := hop
            simp only [beq_iff_eq] at hop'
            rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr3, m3⟩, ha, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              rw [hop']; exact .assignPanic htup' (ih.expr _ _ _ _ hv) (ih.lvalue _ _ _ _ hlv) hp
            · rw [IM.pure_some h, hop']
              exact .assignPlain htup' (ih.expr _ _ _ _ hv) (ih.lvalue _ _ _ _ hlv) (liftOp_ok ha)
          · rename_i hop
            have hop' := hop
            simp only [beq_iff_eq] at hop'
            rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨cur, hcur, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              exact .assignCompoundReadPanic htup' hop' (ih.expr _ _ _ _ hv) (ih.lvalue _ _ _ _ hlv) hp
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨rr, hr, h⟩ <;> try dsimp only at h
              · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
                exact .assignCompoundPanic htup' hop' (ih.expr _ _ _ _ hv) (ih.lvalue _ _ _ _ hlv) (liftOp_ok hcur) hp
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr3, m3⟩, ha, h⟩ <;> try dsimp only at h
                · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
                  exact .assignCompoundAssignPanic htup' hop' (ih.expr _ _ _ _ hv) (ih.lvalue _ _ _ _ hlv) (liftOp_ok hcur)
                    (liftOp_ok hr) hp
                · rw [IM.pure_some h]
                  exact .assignCompound htup' hop' (ih.expr _ _ _ _ hv) (ih.lvalue _ _ _ _ hlv) (liftOp_ok hcur) (liftOp_ok hr)
                    (liftOp_ok ha)
  · -- (e, ...)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es', hes, h⟩ <;> try dsimp only at h
    · exact (liftOpt_error hd).elim
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
      · exact .tupleRevert (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
      · rw [IM.pure_some h]; exact .tuple (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs)
  · -- [e, ...]
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
    · exact .arrayLitRevert (ih.exprs _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, m2⟩, hobj, h⟩ <;> try dsimp only at h
      · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
        exact .arrayLitPanic (ih.exprs _ _ _ _ hvs) hp
      · rw [IM.pure_some h]; exact .arrayLit (ih.exprs _ _ _ _ hvs) (liftOp_ok hobj)
  · simp at h

end Solidity
