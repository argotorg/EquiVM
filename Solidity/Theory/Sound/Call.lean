import Solidity.Theory.InterpLemmas

/-! # Soundness steps: calls (`evalCall`) and builtins (`evalBuiltin`). -/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

private theorem isSuperExpr_eq {e : Expr} (h : isSuperExpr e = true) : e = .super := by
  cases e <;> simp [isSuperExpr] at h ⊢

theorem evalBuiltin_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m f args r, (evalBuiltin cfg o fc (n+1) fr m f args).run = some r →
      EvalExpr cfg o fc fr m (.call (.ident f) [] args) (resOf r) := by
  intro fr m f args r h
  simp only [evalBuiltin] at h
  split at h
  · -- require(c, ...)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨cv, fr1, m1⟩, hcv, h⟩ <;> try dsimp only at h
    · exact .requireCondRevert (ih.expr _ _ _ _ hd)
    · have hc := ih.expr _ _ _ _ hcv
      split at h
      · rw [IM.pure_some h]; exact .requireTrue hc
      · rw [IM.throw_some h]; exact .requireFalse hc
      · split at h
        · split at h
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨ei, hei, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
              · exact (liftOpt_error hd).elim
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr2, m2⟩, hvs, h⟩ <;> try dsimp only at h
                · exact .requireCustomArgsRevert hc (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m3⟩, hsvs, h⟩ <;> try dsimp only at h
                  · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
                    exact .requireCustomPanic hc (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) hp
                  · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨dd, hdd, h⟩ <;> try dsimp only at h
                    · exact (liftOpt_error hd).elim
                    · rw [IM.throw_some h]
                      exact .requireCustom hc (liftOpt_ok hei) (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hsvs)
                        (liftOpt_ok hdd)
          · simp at h
        · rename_i hce
          have hce' := hce
          simp only [Bool.not_eq_true] at hce'
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨mv, fr2, m2⟩, hmv, h⟩ <;> try dsimp only at h
          · exact .requireMsgRevert hce' hc (ih.expr _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨s, hs, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rw [IM.throw_some h]; exact .requireMsg hce' hc (ih.expr _ _ _ _ hmv) (liftOpt_ok hs)
      · simp at h
  · -- assert(c)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨cv, fr1, m1⟩, hcv, h⟩ <;> try dsimp only at h
    · exact .assertRevert (ih.expr _ _ _ _ hd)
    · split at h
      · rw [IM.pure_some h]; exact .assertTrue (ih.expr _ _ _ _ hcv)
      · rw [IM.throw_some h]; exact .assertFalse (ih.expr _ _ _ _ hcv)
      · simp at h
  · -- revert()
    rw [IM.throw_some h]; exact .revertEmpty
  · -- revert(msg)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨mv, fr1, m1⟩, hmv, h⟩ <;> try dsimp only at h
    · exact .revertMsgRevert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨s, hs, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rw [IM.throw_some h]; exact .revertMsg (ih.expr _ _ _ _ hmv) (liftOpt_ok hs)
  · -- keccak256(b)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .keccakRevert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨s, hs, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rw [IM.pure_some h]; exact .keccak (ih.expr _ _ _ _ hv) (liftOpt_ok hs)
  · -- gasleft()
    rw [IM.pure_some h]; exact .gasleft
  · -- addmod / mulmod
    split at h
    · rename_i hf
      have hf' := hf
      simp only [Bool.or_eq_true, beq_iff_eq] at hf'
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
      · exact .modArgsRevert hf' (ih.exprs _ _ _ _ hd)
      · split at h
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨a, ha, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨b, hb, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨c, hc, h⟩ <;> try dsimp only at h
              · exact (liftOpt_error hd).elim
              · split at h
                · rename_i hc0
                  rw [IM.throw_bind_some h]
                  exact .modZero (ih.exprs _ _ _ _ hvs) (liftOpt_ok ha) (liftOpt_ok hb) (hc0 ▸ liftOpt_ok hc) hf'
                · rename_i hc0
                  have h := IM.pure_bind_some h
                  try dsimp only at h
                  rw [IM.pure_some h]
                  rcases hf' with hf' | hf'
                  · simp only [hf', beq_self_eq_true, ite_true]
                    exact .addmod (ih.exprs _ _ _ _ hvs) (liftOpt_ok ha) (liftOpt_ok hb) (liftOpt_ok hc) hc0
                  · simp only [hf', show ("mulmod" == "addmod") = false from by decide, Bool.false_eq_true, ite_false]
                    exact .mulmod (ih.exprs _ _ _ _ hvs) (liftOpt_ok ha) (liftOpt_ok hb) (liftOpt_ok hc) hc0
        · simp at h
    · simp at h
  · simp at h

theorem evalCall_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m callee opts args r, (evalCall cfg o fc (n+1) fr m callee opts args).run = some r →
      EvalExpr cfg o fc fr m (.call callee opts args) (resOf r) := by
  intro fr m callee opts args r h
  simp only [evalCall] at h
  split at h
  · -- T(a)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
    · exact .convertRevert (ih.expr _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v', h'⟩, hc, h⟩ <;> try dsimp only at h
      · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
        exact .convertPanic (ih.expr _ _ _ _ hv) hp
      · rw [IM.pure_some h]; exact .convert (ih.expr _ _ _ _ hv) (liftOp_ok hc)
  · -- new C(args) / new T[](n)
    rename_i ty
    split at h
    · -- contract creation
      rename_i c tys hct
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨value, fr1, m1⟩, hval, h⟩ <;> try dsimp only at h
      · exact .newContractValueRevert hct (ih.valueOpt _ _ _ _ hd)
      · have hv := ih.valueOpt _ _ _ _ hval
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨salt, fr2, m2⟩, hsalt, h⟩ <;> try dsimp only at h
        · exact .newContractSaltRevert hct hv (ih.saltOpt _ _ _ _ hd)
        · have hs := ih.saltOpt _ _ _ _ hsalt
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr3, m3⟩, hvs, h⟩ <;> try dsimp only at h
            · exact .newContractArgsRevert hct hv hs (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m4⟩, hsvs, h⟩ <;> try dsimp only at h
              · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
                exact .newContractAbiPanic hct hv hs (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) hp
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨a, m5, z, out⟩, hnew, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · have hbridge := newViaEVM_sound cfg o m4 c value svs salt (liftOpt_ok hnew)
                  cases z
                  · simp only [Bool.not_false, ite_true] at h
                    rw [IM.throw_bind_some h]
                    exact .newContractFailed hct hv hs (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hsvs) hbridge
                  · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
                    have h := IM.pure_bind_some h
                    try dsimp only at h
                    rw [IM.pure_some h]
                    exact .newContract hct hv hs (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hsvs) hbridge
    · -- memory allocation
      rename_i hct
      split at h
      · rename_i ne
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨nv, fr1, m1⟩, hnv, h⟩ <;> try dsimp only at h
        · exact .newArrayRevert hct (ih.expr _ _ _ _ hd)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨len, hlen, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u, hu, h⟩ <;> try dsimp only at h
            · exact (guard'_error hd).elim
            · have hvt : isValueType fc.types ty = false := by simpa using guard'_ok hu
              rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, h'⟩, hz, h⟩ <;> try dsimp only at h
              · exact (liftOpt_error hd).elim
              · rw [IM.pure_some h]
                exact .newArray hct (ih.expr _ _ _ _ hnv) (liftOpt_ok hlen) hvt (liftOpt_ok hz)
      · exact (IM.failure_some h).elim
  · -- f(args): builtin or user function
    split at h
    · exact ih.builtin _ _ _ _ _ h
    · rename_i hb
      exact ih.namedCall _ _ _ _ _ (by simpa using hb) h
  · -- recv.f{opts}(args)
    split at h
    · -- super.f(args)
      rename_i hsup
      have hsup' : _ = Expr.super := isSuperExpr_eq hsup
      split at h
      · rename_i hopts
        have hopts' : opts = [] := List.isEmpty_iff.mp hopts
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
          · rw [hsup', hopts']; exact .superArgsRevert (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨rets, m2⟩, hcall, h⟩ <;> try dsimp only at h
              · rw [hsup', hopts']
                exact .superCallRevert (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hfn) (ih.callFn _ _ _ _ _ hd)
              · rw [IM.pure_some h, hsup', hopts']
                exact .superCall (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hfn) (ih.callFn _ _ _ _ _ hcall)
      · simp at h
    · split at h
      · -- abi.f(es)
        split at h
        · split at h
          · exact ih.abi _ _ _ _ _ h
          · simp at h
        · simp at h
      · split at h
        · -- L.f(args)
          rename_i hlib
          split at h
          · rename_i l
            have hl := hlib
            simp only [libraryRecv, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hl
            split at h
            · rename_i hopts
              have hopts' : opts = [] := List.isEmpty_iff.mp hopts
              split at h
              · rename_i lib hlibl
                rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
                  · rw [hopts']; exact .libraryArgsRevert hl.1.2 hl.1.1 hlibl (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
                  · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨dcl, hdcl, h⟩ <;> try dsimp only at h
                    · exact (liftOpt_error hd).elim
                    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨rets, m2⟩, hcall, h⟩ <;> try dsimp only at h
                      · rw [hopts']
                        exact .libraryCallRevert hl.1.2 hl.1.1 hlibl (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl)
                          (ih.callFn _ _ _ _ _ hd)
                      · rw [IM.pure_some h, hopts']
                        exact .libraryCall hl.1.2 hl.1.1 hlibl (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl)
                          (ih.callFn _ _ _ _ _ hcall)
              · simp at h
            · simp at h
          · simp at h
        · exact ih.memberCall _ _ _ _ _ _ _ h
  · simp at h

end Solidity
