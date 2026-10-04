import Solidity.Theory.InterpSound
import Solidity.Theory.Complete

/-!
# Equivalence of the relational semantics and the interpreter

Completeness of the entry points (`interpExec`, `interpCtor`), the `iff` characterisations of
`solidityExec` / `solidityCtorExec` by the interpreter, and determinism of the relations.
-/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

/-! ## Boolean forms of the payability guards -/

theorem payableOrNoValue_false {d : FnDecl} {I : Ethereum.ExecutionEnv} (h : payableOrNoValue d I) :
    (d.mutability != .payable && I.weiValue != ⟨0⟩) = false := by
  unfold payableOrNoValue at h
  rcases h with h | h <;> simp [h]

theorem nonPayable_true {d : FnDecl} {I : Ethereum.ExecutionEnv} (h1 : d.mutability ≠ .payable)
    (h2 : I.weiValue ≠ ⟨0⟩) : (d.mutability != .payable && I.weiValue != ⟨0⟩) = true := by
  simp [h1, h2]

theorem selectorDispatch_empty {calldata : ByteArray} (h : calldata.size = 0) :
    selectorDispatch fc calldata = none := by
  simp [selectorDispatch, h]

theorem noReceive_false {I : Ethereum.ExecutionEnv} (h : fc.receive? = none ∨ I.calldata.size ≠ 0) :
    (I.calldata.size == 0 && fc.receive?.isSome) = false := by
  rcases h with h | h <;> simp [h]

theorem ctorPayableB_false {I : Ethereum.ExecutionEnv} (h : ¬ ctorPayable fc I) : ctorPayableB fc I = false := by
  cases hb : ctorPayableB fc I
  · rfl
  · exact absurd (ctorPayableB_iff.mp hb) h

/-! ## Completeness of the message-call entry point -/

theorem interpExec_complete {cA gh bl σ σ₀ g A I res conv}
    (h : solidityExec cfg o fc cA gh bl σ σ₀ g A I res conv) :
    ∃ n, ∀ k, n ≤ k → (interpExec cfg o fc k cA gh bl σ σ₀ g A I).run = some (.ok (res, conv)) := by
  cases h with
  | call he hfn hpay hret hsvs hvs hc hout =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine cA gh bl σ σ₀ g A I _) _ _ = some (.ok (_, _)) := ih k hk
    interp_simp [interpExec, he, hfn, hret, hsvs, hvs, hout, ih', payableOrNoValue_false hpay]
  | callReverted he hfn hpay hret hsvs hvs hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine cA gh bl σ σ₀ g A I _) _ _ = some (.error _) := ih k hk
    interp_simp [interpExec, he, hfn, hret, hsvs, hvs, ih', payableOrNoValue_false hpay]
  | nonPayable he hfn h1 h2 hret =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [interpExec, he, hfn, hret, nonPayable_true h1 h2]
  | receive hsz hrec hfn hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine cA gh bl σ σ₀ g A I) _ [] = some (.ok (_, _)) := ih k hk
    interp_simp [interpExec, selectorDispatch_empty hsz, hsz, hrec, hfn, ih']
  | receiveReverted hsz hrec hfn hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine cA gh bl σ σ₀ g A I) _ [] = some (.error _) := ih k hk
    interp_simp [interpExec, selectorDispatch_empty hsz, hsz, hrec, hfn, ih']
  | fallback he hrec hfb hfn hpay hargs hc hout =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine cA gh bl σ σ₀ g A I _) _ _ = some (.ok (_, _)) := ih k hk
    interp_simp [interpExec, he, noReceive_false hrec, hfb, hfn, hargs, hout, ih', payableOrNoValue_false hpay]
  | fallbackReverted he hrec hfb hfn hpay hargs hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine cA gh bl σ σ₀ g A I _) _ _ = some (.error _) := ih k hk
    interp_simp [interpExec, he, noReceive_false hrec, hfb, hfn, hargs, ih', payableOrNoValue_false hpay]
  | fallbackNonPayable he hrec hfb hfn h1 h2 =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [interpExec, he, noReceive_false hrec, hfb, hfn, nonPayable_true h1 h2]

/-! ## Completeness of construction -/

def toArgs : Res (List Value) → Except ByteArray (List Value × Machine)
  | .ok vs _ m => .ok (vs, m)
  | .reverted d => .error d

def toChain : CtorResult → Except ByteArray (Machine × Store)
  | .ok m imms => .ok (m, imms)
  | .reverted d => .error d

/-- A finished body is not a revert. -/
theorem toExec_of_finished {r : ExecResult} {fr : Frame} {m : Machine} (h : finished r = some (fr, m)) :
    toExec r = .ok r := by
  cases r <;> simp_all [finished, toExec]

theorem initsFold_complete {fr m vs r} (h : ExecInits cfg o fc fr m vs r) :
    ∃ n, ∀ k, n ≤ k → (vs.foldlM (initStep cfg o fc k) (fr, m)).run = some (toUnit r) := by
  induction h with
  | nil => exact ⟨0, fun k _ => by simp⟩
  | storage hmut hinit hev hassign _ ih =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    obtain ⟨n2, ih2⟩ := ih
    refine ⟨n1 + n2, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k (by omega), ih2 k (by omega)]
  | immutable hmut hinit hev hassign _ ih =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    obtain ⟨n2, ih2⟩ := ih
    refine ⟨n1 + n2, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k (by omega), ih2 k (by omega)]
  | revert hinit hev =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    refine ⟨n1, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hinit, ih1 k hk]
  | storagePanic hmut hinit hev hassign =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    refine ⟨n1, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k hk]
  | immutablePanic hmut hinit hev hassign =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    refine ⟨n1, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k hk]

theorem ctorArgs_complete {topArgs imms tbl m step r} (h : CtorArgs cfg o fc topArgs imms tbl m step r) :
    ∃ n, ∀ k, n ≤ k → (ctorArgsOf cfg o fc k topArgs imms tbl m step).run = some (toArgs r) := by
  cases h with
  | top hc =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [ctorArgsOf, toArgs, hc]
  | none hc hargs =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [ctorArgsOf, toArgs, hc, hargs]
  | some hc hargs hw hfr hes hev =>
    obtain ⟨n, ih⟩ := evalExprs_complete hev
    refine ⟨n, fun k hk => ?_⟩
    rcases r with ⟨vs, fr', m1⟩ | d <;> interp_simp [ctorArgsOf, toArgs, hc, hargs, hw, hfr, hes, ih k hk]
  | framePanic hc hargs hw hfr =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [ctorArgsOf, toArgs, hc, hargs, hw, hfr]

theorem argsFold_complete {topArgs imms tbl m steps r} (h : CtorArgsAll cfg o fc topArgs imms tbl m steps r) :
    ∃ n, ∀ k, n ≤ k → (steps.foldlM (argsStep cfg o fc k topArgs imms) (tbl, m)).run = some r := by
  induction h with
  | nil => exact ⟨0, fun k _ => by simp⟩
  | cons hca _ ih =>
    obtain ⟨na, iha⟩ := ctorArgs_complete hca
    obtain ⟨nr, ihr⟩ := ih
    refine ⟨na + nr, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, argsStep, toArgs, iha k (by omega), ihr k (by omega)]
  | revert hca =>
    obtain ⟨na, iha⟩ := ctorArgs_complete hca
    refine ⟨na, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, argsStep, toArgs, iha k hk]

theorem chainFold_complete {tbl imms m steps r} (h : ExecCtorChain cfg o fc tbl imms m steps r) :
    ∃ n, ∀ k, n ≤ k → (steps.foldlM (ctorStep cfg o fc k tbl) (m, imms)).run = some (toChain r) := by
  induction h with
  | nil => exact ⟨0, fun k _ => by simp [toChain]⟩
  | skip hfn _ ih =>
    obtain ⟨n, ihn⟩ := ih
    refine ⟨n, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, ctorStep, hfn, ihn k hk]
  | run hfid hfn hvs henter hbody hchain hfin _ ih =>
    obtain ⟨nc, ihc⟩ := execChain_complete hchain
    obtain ⟨nr, ihr⟩ := ih
    refine ⟨nc + nr, fun k hk => ?_⟩
    have ihc' := ihc k (by omega)
    rw [toExec_of_finished hfin] at ihc'
    interp_simp [List.foldlM_cons, ctorStep, toChain, hfid, hfn, hvs, henter, hbody, hfin, ihc', ihr k (by omega)]
  | bodyReverted hfid hfn hvs henter hbody hchain =>
    obtain ⟨nc, ihc⟩ := execChain_complete hchain
    refine ⟨nc, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, ctorStep, toChain, hfid, hfn, hvs, henter, hbody, ihc k (by omega)]
  | enterPanic hfid hfn hvs henter =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [List.foldlM_cons, ctorStep, toChain, hfid, hfn, hvs, henter]

theorem interpCtor_complete {args cA gh bl σ σ₀ g A I r}
    (h : solidityCtorExec cfg o fc args cA gh bl σ σ₀ g A I r) :
    ∃ n, ∀ k, n ≤ k → ((interpCtor cfg o fc k args cA gh bl σ σ₀ g A I).run).map ctorOf = some r := by
  cases h with
  | run hpay himms hargs hinits hav hchain =>
    obtain ⟨ni, ihi⟩ := initsFold_complete hinits
    obtain ⟨na, iha⟩ := argsFold_complete hav
    obtain ⟨nc, ihc⟩ := chainFold_complete hchain
    refine ⟨ni + na + nc, fun k hk => ?_⟩
    rcases r with ⟨m3, imms⟩ | d <;>
      interp_simp [interpCtor, ctorOf, toChain, ctorPayableB_iff.mpr hpay, himms, hargs, ihi k (by omega),
        iha k (by omega), ihc k (by omega), Option.map_some]
  | initsReverted hpay himms hargs hinits =>
    obtain ⟨ni, ihi⟩ := initsFold_complete hinits
    refine ⟨ni, fun k hk => ?_⟩
    interp_simp [interpCtor, ctorOf, ctorPayableB_iff.mpr hpay, himms, hargs, ihi k hk, Option.map_some]
  | argsReverted hpay himms hargs hinits hav =>
    obtain ⟨ni, ihi⟩ := initsFold_complete hinits
    obtain ⟨na, iha⟩ := argsFold_complete hav
    refine ⟨ni + na, fun k hk => ?_⟩
    interp_simp [interpCtor, ctorOf, ctorPayableB_iff.mpr hpay, himms, hargs, ihi k (by omega), iha k (by omega),
      Option.map_some]
  | nonPayable hnp =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [interpCtor, ctorOf, ctorPayableB_false hnp, Option.map_some]

/-! ## The relations are exactly what the interpreter computes -/

theorem solidityExec_iff {cA gh bl σ σ₀ g A I res conv} :
    solidityExec cfg o fc cA gh bl σ σ₀ g A I res conv ↔
      ∃ k, (interpExec cfg o fc k cA gh bl σ σ₀ g A I).run = some (.ok (res, conv)) :=
  ⟨fun h => let ⟨n, hn⟩ := interpExec_complete h; ⟨n, hn n (Nat.le_refl n)⟩, fun ⟨_, hk⟩ => interpExec_sound hk⟩

theorem solidityCtorExec_iff {args cA gh bl σ σ₀ g A I r} :
    solidityCtorExec cfg o fc args cA gh bl σ σ₀ g A I r ↔
      ∃ k, ((interpCtor cfg o fc k args cA gh bl σ σ₀ g A I).run).map ctorOf = some r := by
  refine ⟨fun h => let ⟨n, hn⟩ := interpCtor_complete h; ⟨n, hn n (Nat.le_refl n)⟩, fun ⟨k, hk⟩ => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hk
  exact interpCtor_sound hx

theorem evalExpr_iff {fr m e r} :
    EvalExpr cfg o fc fr m e r ↔ ∃ k, (evalExpr cfg o fc k fr m e).run = some (toRes r) :=
  ⟨fun h => let ⟨n, hn⟩ := evalExpr_complete h; ⟨n, hn n (Nat.le_refl n)⟩,
   fun ⟨k, hk⟩ => by cases r <;> exact evalExpr_sound hk⟩

theorem execStmt_iff {fr m s r} :
    ExecStmt cfg o fc fr m s r ↔ ∃ k, (execStmt cfg o fc k fr m s).run = some (toExec r) :=
  ⟨fun h => let ⟨n, hn⟩ := execStmt_complete h; ⟨n, hn n (Nat.le_refl n)⟩,
   fun ⟨k, hk⟩ => by cases r <;> exact execStmt_sound hk⟩

theorem callFn_iff {fr m fn args r} :
    CallFn cfg o fc fr m fn args r ↔ ∃ k, (callFn cfg o fc k fr m fn args).run = some (toFn r) :=
  ⟨fun h => let ⟨n, hn⟩ := callFn_complete h; ⟨n, hn n (Nat.le_refl n)⟩,
   fun ⟨k, hk⟩ => by cases r <;> exact callFn_sound hk⟩

/-! ## Determinism -/

theorem toRes_inj {α} {r r' : Res α} (h : toRes r = toRes r') : r = r' := by
  cases r <;> cases r' <;> simp_all [toRes]

theorem toExec_inj {r r' : ExecResult} (h : toExec r = toExec r') : r = r' := by
  cases r <;> cases r' <;> simp_all [toExec]

theorem toFn_inj {r r' : FnResult} (h : toFn r = toFn r') : r = r' := by
  cases r <;> cases r' <;> simp_all [toFn]

theorem evalExpr_det {fr m e r r'} (h : EvalExpr cfg o fc fr m e r) (h' : EvalExpr cfg o fc fr m e r') : r = r' := by
  obtain ⟨n, hn⟩ := evalExpr_complete h
  obtain ⟨n', hn'⟩ := evalExpr_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  exact toRes_inj (Option.some.inj this)

theorem execStmt_det {fr m s r r'} (h : ExecStmt cfg o fc fr m s r) (h' : ExecStmt cfg o fc fr m s r') : r = r' := by
  obtain ⟨n, hn⟩ := execStmt_complete h
  obtain ⟨n', hn'⟩ := execStmt_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  exact toExec_inj (Option.some.inj this)

theorem callFn_det {fr m fn args r r'} (h : CallFn cfg o fc fr m fn args r) (h' : CallFn cfg o fc fr m fn args r') :
    r = r' := by
  obtain ⟨n, hn⟩ := callFn_complete h
  obtain ⟨n', hn'⟩ := callFn_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  exact toFn_inj (Option.some.inj this)

theorem solidityExec_det {cA gh bl σ σ₀ g A I res conv res' conv'}
    (h : solidityExec cfg o fc cA gh bl σ σ₀ g A I res conv)
    (h' : solidityExec cfg o fc cA gh bl σ σ₀ g A I res' conv') : res = res' ∧ conv = conv' := by
  obtain ⟨n, hn⟩ := interpExec_complete h
  obtain ⟨n', hn'⟩ := interpExec_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  simpa using this

theorem solidityCtorExec_det {args cA gh bl σ σ₀ g A I r r'}
    (h : solidityCtorExec cfg o fc args cA gh bl σ σ₀ g A I r)
    (h' : solidityCtorExec cfg o fc args cA gh bl σ σ₀ g A I r') : r = r' := by
  obtain ⟨n, hn⟩ := interpCtor_complete h
  obtain ⟨n', hn'⟩ := interpCtor_complete h'
  exact Option.some.inj ((hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega)))

end Solidity
