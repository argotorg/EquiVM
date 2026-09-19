import Solidity.Theory.Sound
import Solidity.Behaviors

/-!
# Soundness of the entry points

`interpExec` / `interpCtor` results are derivable by `solidityExec` / `solidityCtorExec`, and the
boolean rejection test implies the relation's rejection predicate.
-/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

theorem payableOrNoValue_of {d : FnDecl} {I : Ethereum.ExecutionEnv}
    (h : ¬ (d.mutability != .payable && I.weiValue != ⟨0⟩) = true) : payableOrNoValue d I := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, not_not] at h
  unfold payableOrNoValue
  by_cases hp : d.mutability = .payable
  · exact Or.inl hp
  · exact Or.inr (h hp)

theorem interpExec_sound {fuel cA gh bl σ σ₀ g A I res conv}
    (h : (interpExec cfg o fc fuel cA gh bl σ σ₀ g A I).run = some (.ok (res, conv))) :
    solidityExec cfg o fc cA gh bl σ σ₀ g A I res conv := by
  simp only [interpExec] at h
  split at h
  · -- a selector matched
    rename_i e he
    rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
    · exact (liftOpt_error hd).elim
    · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨retTys, hret, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · split at h
        · rename_i hnp
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hnp
          cases IM.pure_some h
          exact .nonPayable he (liftOpt_ok hfn) hnp.1 hnp.2 (liftOpt_ok hret)
        · rename_i hnp
          have hpay := payableOrNoValue_of hnp
          have h := IM.pure_bind_some h
          try dsimp only at h
          rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨svs, hsvs, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨⟨vs, h0⟩, hvs, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · split at h
              · rename_i rets m' hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨out, hout, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · cases IM.pure_some h
                  exact .call he (liftOpt_ok hfn) hpay (liftOpt_ok hret) (liftOpt_ok hsvs) (liftOpt_ok hvs) hc (liftOpt_ok hout)
              · rename_i d hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                cases IM.pure_some h
                exact .callReverted he (liftOpt_ok hfn) hpay (liftOpt_ok hret) (liftOpt_ok hsvs) (liftOpt_ok hvs) hc
              · simp at h
  · -- no selector
    rename_i he
    split at h
    · rename_i hrec
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hrec
      rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fid, hfid, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · split at h
          · rename_i rets m' hcall
            have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
            cases IM.pure_some h
            exact .receive hrec.1 (liftOpt_ok hfid) (liftOpt_ok hfn) hc
          · rename_i d hcall
            have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
            cases IM.pure_some h
            exact .receiveReverted hrec.1 (liftOpt_ok hfid) (liftOpt_ok hfn) hc
          · simp at h
    · rename_i hrec
      have hrec' : fc.receive? = none ∨ I.calldata.size ≠ 0 := by
        simp only [Bool.and_eq_true, beq_iff_eq, not_and, Option.isSome_iff_ne_none] at hrec
        by_cases hs : I.calldata.size = 0
        · exact Or.inl (by_contra fun hn => hrec hs hn)
        · exact Or.inr hs
      rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fid, hfid, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · split at h
          · rename_i hnp
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hnp
            cases IM.pure_some h
            exact .fallbackNonPayable he hrec' (liftOpt_ok hfid) (liftOpt_ok hfn) hnp.1 hnp.2
          · rename_i hnp
            have hpay := payableOrNoValue_of hnp
            have h := IM.pure_bind_some h
            try dsimp only at h
            rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨⟨vs, h0⟩, hvs, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · split at h
              · rename_i rets m' hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨out, hout, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · cases IM.pure_some h
                  exact .fallback he hrec' (liftOpt_ok hfid) (liftOpt_ok hfn) hpay (liftOpt_ok hvs) hc (liftOpt_ok hout)
              · rename_i d hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                cases IM.pure_some h
                exact .fallbackReverted he hrec' (liftOpt_ok hfid) (liftOpt_ok hfn) hpay (liftOpt_ok hvs) hc
              · simp at h

/-- The boolean rejection test implies the relation's rejection predicate. -/
theorem specRejectsB_sound {I : Ethereum.ExecutionEnv} (h : specRejectsB cfg fc I = true) : specRejects cfg fc I := by
  unfold specRejectsB at h
  split at h
  · rename_i hd
    exact Or.inl (by simpa using hd)
  · rename_i hd
    split at h
    · rename_i e he
      split at h
      · rename_i fn hfn
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
        exact Or.inr ⟨e, fn, he, hfn, h.1, h.2⟩
      · simp at h
    · simp at h

/-! ## Construction -/

def ctorOf : Except ByteArray CtorResult → CtorResult
  | .ok r => r
  | .error d => .reverted d

def chainOf : Except ByteArray (Machine × Store) → CtorResult
  | .ok (m, imms) => .ok m imms
  | .error d => .reverted d

theorem initsFold_sound (fuel : Nat) : ∀ (vs : List FlatVar) fr m r,
    (vs.foldlM (initStep cfg o fc fuel) (fr, m)).run = some r → ExecInits cfg o fc fr m vs (unitResOf r)
  | [], fr, m, r, h => by
    simp only [List.foldlM_nil] at h
    cases IM.pure_some h; exact .nil
  | v :: vs, fr, m, r, h => by
    simp only [List.foldlM_cons] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr1, m1⟩, hstep, h⟩ <;> try dsimp only at h
    · -- the step reverted
      simp only [initStep] at hd
      split at hd
      · rename_i e he
        rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨val, fr1, m1⟩, hval, hd⟩ <;> try dsimp only at hd
        · cases hdd; exact .revert he (evalExpr_sound hd')
        · split at hd
          · rename_i hmut
            obtain ⟨p, hp, hpd⟩ := liftOp_error hd
            cases hpd; exact .storagePanic hmut he (evalExpr_sound hval) hp
          · rename_i hmut
            obtain ⟨p, hp, hpd⟩ := liftOp_error hd
            cases hpd; exact .immutablePanic hmut he (evalExpr_sound hval) hp
          · simp at hd
      · simp at hd
    · simp only [initStep] at hstep
      split at hstep
      · rename_i e he
        rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨val, fr1', m1'⟩, hval, hstep⟩ <;> try dsimp only at hstep
        · cases hdd
        · split at hstep
          · rename_i hmut
            exact .storage hmut he (evalExpr_sound hval) (liftOp_ok hstep) (initsFold_sound fuel vs _ _ _ h)
          · rename_i hmut
            exact .immutable hmut he (evalExpr_sound hval) (liftOp_ok hstep) (initsFold_sound fuel vs _ _ _ h)
          · simp at hstep
      · simp at hstep

theorem ctorArgs_sound {fuel frP topArgs m step vs m1}
    (h : (ctorArgsOf cfg o fc fuel frP topArgs m step).run = some (.ok (vs, m1))) :
    ∃ fr', CtorArgs cfg o fc frP topArgs m step (.ok vs fr' m1) := by
  simp only [ctorArgsOf] at h
  split at h
  · rename_i hc
    cases IM.pure_some h
    exact ⟨frP, .top (by simpa using hc)⟩
  · rename_i hc
    have hc' : step.contract ≠ fc.name := by simpa using hc
    split at h
    · rename_i hargs
      cases IM.pure_some h
      exact ⟨frP, .none hc' hargs⟩
    · rename_i w a hargs
      rcases IM.bind_some h with ⟨d, hd, hdd⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, hdd⟩ | ⟨⟨vs', fr', m1'⟩, hvs, h⟩ <;> try dsimp only at h
        · cases hdd
        · cases IM.pure_some h
          exact ⟨fr', .some hc' hargs (liftOpt_ok hes) ((soundAt cfg o fc fuel).exprs _ _ _ _ hvs)⟩

theorem ctorArgs_revert {fuel frP topArgs m step d}
    (h : (ctorArgsOf cfg o fc fuel frP topArgs m step).run = some (.error d)) :
    CtorArgs cfg o fc frP topArgs m step (.reverted d) := by
  simp only [ctorArgsOf] at h
  split at h
  · cases IM.pure_some h
  · rename_i hc
    have hc' : step.contract ≠ fc.name := by simpa using hc
    split at h
    · cases IM.pure_some h
    · rename_i w a hargs
      rcases IM.bind_some h with ⟨d', hd, hdd⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d', hd, hdd⟩ | ⟨⟨vs', fr', m1'⟩, hvs, h⟩ <;> try dsimp only at h
        · cases hdd; exact .some hc' hargs (liftOpt_ok hes) ((soundAt cfg o fc fuel).exprs _ _ _ _ hd)
        · cases IM.pure_some h

theorem chainFold_sound (fuel : Nat) (frP : Frame) (topArgs : List Value) : ∀ (steps : List CtorStep) m imms r,
    (steps.foldlM (ctorStep cfg o fc fuel frP topArgs) (m, imms)).run = some r →
      ExecCtorChain cfg o fc frP topArgs imms m steps (chainOf r)
  | [], m, imms, r, h => by
    simp only [List.foldlM_nil] at h
    cases IM.pure_some h; exact .nil
  | step :: steps, m, imms, r, h => by
    simp only [List.foldlM_cons] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨m', imms'⟩, hstep, h⟩ <;> try dsimp only at h
    · simp only [ctorStep] at hd
      split at hd
      · cases IM.pure_some hd
      · rename_i fid hfid
        rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨fn, hfn, hd⟩ <;> try dsimp only at hd
        · exact (liftOpt_error hd').elim
        · rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨vs, m1⟩, hargs, hd⟩ <;> try dsimp only at hd
          · cases hdd; exact .argsReverted hfid (liftOpt_ok hfn) (ctorArgs_revert hd')
          · obtain ⟨fr', hca⟩ := ctorArgs_sound hargs
            rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨fr2, m2⟩, henter, hd⟩ <;> try dsimp only at hd
            · obtain ⟨p, hp, hpd⟩ := liftOp_error hd'
              cases hdd; cases hpd; exact .enterPanic hfid (liftOpt_ok hfn) hca hp
            · rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨mods, fr3, m3⟩, hmods, hd⟩ <;> try dsimp only at hd
              · cases hdd
                exact .modsReverted hfid (liftOpt_ok hfn) hca (liftOp_ok henter) ((soundAt cfg o fc fuel).mods _ _ _ _ hd')
              · split at hd
                · rename_i body hbody
                  rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨r', hr, hd⟩ <;> try dsimp only at hd
                  · cases hdd
                    exact .bodyReverted hfid (liftOpt_ok hfn) hca (liftOp_ok henter)
                      ((soundAt cfg o fc fuel).mods _ _ _ _ hmods) hbody ((soundAt cfg o fc fuel).chain _ _ _ _ _ hd')
                  · rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨fr4, m4⟩, hfin, hd⟩ <;> try dsimp only at hd
                    · exact (liftOpt_error hd').elim
                    · cases IM.pure_some hd
                · simp at hd
    · simp only [ctorStep] at hstep
      split at hstep
      · cases IM.pure_some hstep
        exact .skip ‹_› (chainFold_sound fuel frP topArgs steps _ _ _ h)
      · rename_i fid hfid
        rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨fn, hfn, hstep⟩ <;> try dsimp only at hstep
        · cases hdd
        · rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨vs, m1⟩, hargs, hstep⟩ <;> try dsimp only at hstep
          · cases hdd
          · obtain ⟨fr', hca⟩ := ctorArgs_sound hargs
            rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨fr2, m2⟩, henter, hstep⟩ <;> try dsimp only at hstep
            · cases hdd
            · rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨mods, fr3, m3⟩, hmods, hstep⟩ <;> try dsimp only at hstep
              · cases hdd
              · split at hstep
                · rename_i body hbody
                  rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨r', hr, hstep⟩ <;> try dsimp only at hstep
                  · cases hdd
                  · rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨fr4, m4⟩, hfin, hstep⟩ <;> try dsimp only at hstep
                    · exact (liftOpt_error hd').elim
                    · cases IM.pure_some hstep
                      exact .run hfid (liftOpt_ok hfn) hca (liftOp_ok henter) ((soundAt cfg o fc fuel).mods _ _ _ _ hmods)
                        hbody ((soundAt cfg o fc fuel).chain _ _ _ _ _ hr) (liftOpt_ok hfin)
                        (chainFold_sound fuel frP topArgs steps _ _ _ h)
                · simp at hstep

theorem ctorPayableB_iff {I : Ethereum.ExecutionEnv} : ctorPayableB fc I = true ↔ ctorPayable fc I := by
  unfold ctorPayableB ctorPayable
  split <;> rename_i heq <;> simp [heq]

theorem interpCtor_sound {fuel args cA gh bl σ σ₀ g A I r}
    (h : (interpCtor cfg o fc fuel args cA gh bl σ σ₀ g A I).run = some r) :
    solidityCtorExec cfg o fc args cA gh bl σ σ₀ g A I (ctorOf r) := by
  simp only [interpCtor] at h
  split at h
  · rename_i hnp
    cases IM.pure_some h
    exact .nonPayable (fun hpay => by simp [ctorPayableB_iff.mpr hpay] at hnp)
  · rename_i hp
    have hpay : ctorPayable fc I := ctorPayableB_iff.mp (by simpa using hp)
    have h := IM.pure_bind_some h
    try dsimp only at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨imms0, himms, h⟩ <;> try dsimp only at h
    · exact (liftOpt_error hd).elim
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨topArgs, h0⟩, hargs, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨frP, m1⟩, hpf, h⟩ <;> try dsimp only at h
        · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
          exact .paramPanic hpay (liftOpt_ok himms) (liftOpt_ok hargs) hp
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨frP1, m2⟩, hinits, h⟩ <;> try dsimp only at h
          · exact .initsReverted hpay (liftOpt_ok himms) (liftOpt_ok hargs) (liftOp_ok hpf) (initsFold_sound fuel _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨m3, imms⟩, hchain, h⟩ <;> try dsimp only at h
            · exact .run hpay (liftOpt_ok himms) (liftOpt_ok hargs) (liftOp_ok hpf) (initsFold_sound fuel _ _ _ _ hinits)
                (chainFold_sound fuel _ _ _ _ _ _ hd)
            · cases IM.pure_some h
              exact .run hpay (liftOpt_ok himms) (liftOpt_ok hargs) (liftOp_ok hpf) (initsFold_sound fuel _ _ _ _ hinits)
                (chainFold_sound fuel _ _ _ _ _ _ hchain)

end Solidity
