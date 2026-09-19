import Solidity.Theory.InterpLemmas

/-! # Soundness steps: member access, `abi.*`, named calls and member calls. -/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

theorem evalMember_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m e f r, directMember fc fr e = false → (evalMember cfg o fc (n+1) fr m e f).run = some r →
      EvalExpr cfg o fc fr m (.member e f) (resOf r) := by
  intro fr m e f r hdm h
  simp only [evalMember] at h
  rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr1, m1⟩, hv, h⟩ <;> try dsimp only at h
  · exact .memberRevert hdm (ih.expr _ _ _ _ hd)
  · have he := ih.expr _ _ _ _ hv
    split at h
    · rename_i er ty
      split at h
      · rename_i hf
        have hf' : f = "length" := by simpa using hf
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨k, hk, h⟩ <;> try dsimp only at h
        · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
          rw [hf']; exact .memberStorageLengthPanic hdm he hp
        · rw [IM.pure_some h, hf']; exact .memberStorageLength hdm he (liftOp_ok hk)
      · rename_i hf
        have hf' : f ≠ "length" := by simpa using hf
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨er', fty⟩, hsf, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rw [IM.pure_some h]; exact .memberField hdm hf' he (liftOpt_ok hsf) (liftOpt_ok hr)
    · rename_i obj
      split at h
      · rename_i hf
        have hf' : f = "length" := by simpa using hf
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨k, hk, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rw [IM.pure_some h, hf']; exact .memberMemLength hdm he (liftOpt_ok hk)
      · rename_i hf
        have hf' : f ≠ "length" := by simpa using hf
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨r', hr, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rw [IM.pure_some h]; exact .memberMemField hdm hf' he (liftOpt_ok hr)
    · rename_i k bs
      split at h
      · rename_i hf
        have hf' : f = "length" := by simpa using hf
        rw [IM.pure_some h, hf']; exact .memberBytesLength hdm he
      · simp at h
    · split at h
      · rename_i hf
        have hf' : f = "balance" := by simpa using hf
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨a, ha, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rw [IM.pure_some h, hf']; exact .memberBalance hdm he (liftOpt_ok ha)
      · simp at h

theorem evalAbi_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m f es r, (evalAbi cfg o fc (n+1) fr m f es).run = some r →
      EvalExpr cfg o fc fr m (.call (.member (.ident "abi") f) [] (.positional es)) (resOf r) := by
  intro fr m f es r h
  simp only [evalAbi] at h
  split at h
  · -- abi.decode(d, T)
    split at h
    · rename_i d tyArg
      rcases IM.bind_some h with ⟨dd, hd, rfl⟩ | ⟨⟨dv, fr1, m1⟩, hdv, h⟩ <;> try dsimp only at h
      · exact .abiDecodeRevert (ih.expr _ _ _ _ hd)
      · rcases IM.bind_some h with ⟨dd, hd, rfl⟩ | ⟨s, hs, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rcases IM.bind_some h with ⟨dd, hd, rfl⟩ | ⟨tys, htys, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨dd, hd, rfl⟩ | ⟨atys, hatys, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · split at h
              · rename_i hdec
                rw [IM.throw_some h]
                exact .abiDecodeFail (ih.expr _ _ _ _ hdv) (liftOpt_ok hs) (liftOpt_ok htys) (liftOpt_ok hatys) hdec
              · rename_i svs hsvs
                rcases IM.bind_some h with ⟨dd, hd, rfl⟩ | ⟨⟨vs, h'⟩, hvs, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · rw [IM.pure_some h]
                  exact .abiDecode (ih.expr _ _ _ _ hdv) (liftOpt_ok hs) (liftOpt_ok htys) (liftOpt_ok hatys) hsvs (liftOpt_ok hvs)
    · simp at h
  · -- abi.encodeWithSelector(sel, ...)
    split at h
    · rename_i sel rest
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs0, fr1, m1⟩, hvs0, h⟩ <;> try dsimp only at h
      · exact .abiEncodeRevert (by decide) (ih.exprs _ _ _ _ hd)
      · split at h
        · rename_i k sb vs
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u, hu, h⟩ <;> try dsimp only at h
          · exact (guard'_error hd).elim
          · have hk : k.val = 3 := by simpa using guard'_ok hu
            rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨tys, htys, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m2⟩, hsvs, h⟩ <;> try dsimp only at h
              · obtain ⟨p, hp, _⟩ := liftOp_error hd
                exact (abiArgsAbi_ne_error _ _ _ _ _ _ hp).elim
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨bs, hbs, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · rw [IM.pure_some h]
                  exact .abiEncodeWithSelector (ih.exprs _ _ _ _ hvs0) hk (liftOpt_ok htys) (liftOp_ok hsvs) (liftOpt_ok hbs) rfl
        · simp at h
    · simp at h
  · -- abi.encodeWithSignature(sig, ...)
    split at h
    · rename_i sig rest
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs0, fr1, m1⟩, hvs0, h⟩ <;> try dsimp only at h
      · exact .abiEncodeRevert (by decide) (ih.exprs _ _ _ _ hd)
      · split at h
        · rename_i sv vs
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨s, hs, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨tys, htys, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m2⟩, hsvs, h⟩ <;> try dsimp only at h
              · obtain ⟨p, hp, _⟩ := liftOp_error hd
                exact (abiArgsAbi_ne_error _ _ _ _ _ _ hp).elim
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨bs, hbs, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · rw [IM.pure_some h]
                  exact .abiEncodeWithSignature (ih.exprs _ _ _ _ hvs0) (liftOpt_ok hs) (liftOpt_ok htys) (liftOp_ok hsvs) (liftOpt_ok hbs) rfl
        · simp at h
    · simp at h
  · -- abi.encode(...)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
    · exact .abiEncodeRevert (by decide) (ih.exprs _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨tys, htys, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m2⟩, hsvs, h⟩ <;> try dsimp only at h
        · obtain ⟨p, hp, _⟩ := liftOp_error hd
          exact (abiArgsAbi_ne_error _ _ _ _ _ _ hp).elim
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨bs, hbs, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rw [IM.pure_some h]
            exact .abiEncode (ih.exprs _ _ _ _ hvs) (liftOpt_ok htys) (liftOp_ok hsvs) (liftOpt_ok hbs) rfl
  · -- abi.encodePacked(...)
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
    · exact .abiEncodeRevert (by decide) (ih.exprs _ _ _ _ hd)
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨tys, htys, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m2⟩, hsvs, h⟩ <;> try dsimp only at h
        · obtain ⟨p, hp, _⟩ := liftOp_error hd
          exact (abiArgsAbi_ne_error _ _ _ _ _ _ hp).elim
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨parts, hparts, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rw [IM.pure_some h]
            exact .abiEncodePacked (ih.exprs _ _ _ _ hvs) (liftOpt_ok htys) (liftOp_ok hsvs) (liftOpt_ok hparts) rfl
  · simp at h

theorem evalNamedCall_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m f args r, isBuiltinFn f = false → (evalNamedCall cfg o fc (n+1) fr m f [] args).run = some r →
      EvalExpr cfg o fc fr m (.call (.ident f) [] args) (resOf r) := by
  intro fr m f args r hb h
  simp only [evalNamedCall] at h
  rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u, hu, h⟩ <;> try dsimp only at h
  · exact (guard'_error hd).elim
  · have hfr : fr.get? f = none := Option.isNone_iff_eq_none.mp (guard'_ok hu)
    split at h
    · rename_i hne
      rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
        · exact .internalArgsRevert hb hfr hne (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨rets, m2⟩, hcall, h⟩ <;> try dsimp only at h
            · exact .internalCallRevert hb hfr hne (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hfn) (ih.callFn _ _ _ _ _ hd)
            · rw [IM.pure_some h]
              exact .internalCall hb hfr hne (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hfn) (ih.callFn _ _ _ _ _ hcall)
    · rename_i hnil
      have hnil' : fc.fnsNamed f = [] := by simpa using hnil
      split at h
      · rename_i sd hsd
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr1, m1⟩, hvs, h⟩ <;> try dsimp only at h
          · exact .structLitRevert hb hfr hnil' hsd (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, m2⟩, hobj, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              exact .structLitPanic hb hfr hnil' hsd (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) hp
            · rw [IM.pure_some h]
              exact .structLit hb hfr hnil' hsd (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOp_ok hobj)
      · rename_i hsd
        split at h
        · rename_i hconv
          simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hconv
          split at h
          · rename_i a
            exact .convertUser hb hfr hconv.1 hnil' hsd hconv.2 (ih.call _ _ _ _ _ _ h)
          · simp at h
        · simp at h

/-- `opts.isEmpty` guard. -/
private theorem isContractValue_false {v : Value} (h : ∀ c a, v = .contract c a → False) : isContractValue v = false := by
  cases v <;> first | rfl | exact (h _ _ rfl).elim

private theorem opts_empty {opts : List CallOpt} {u : Unit} (h : (guard' opts.isEmpty).run = some (.ok u)) : opts = [] :=
  List.isEmpty_iff.mp (guard'_ok h)

theorem evalMemberCall_sound_step {n} (ih : SoundAt cfg o fc n) :
    ∀ fr m recv f opts args r, (evalMemberCall cfg o fc (n+1) fr m recv f opts args).run = some r →
      EvalExpr cfg o fc fr m (.call (.member recv f) opts args) (resOf r) := by
  intro fr m recv f opts args r h
  simp only [evalMemberCall] at h
  rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u, hu, h⟩ <;> try dsimp only at h
  · exact (guard'_error hd).elim
  · have henv : memberCallDirect fc fr recv = false := by simpa using guard'_ok hu
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨rv, fr1, m1⟩, hrv, h⟩ <;> try dsimp only at h
    · exact .callRecvRevert henv (ih.expr _ _ _ _ hd)
    · have he := ih.expr _ _ _ _ hrv
      split at h
      swap
      · -- `using L for T`
        rename_i hspec
        have hspec' : specialMemberCall rv f = false := by simpa using hspec
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u', hu', h⟩ <;> try dsimp only at h
        · exact (guard'_error hd).elim
        · have hopts := opts_empty hu'
          split at h
          · rename_i lib hlib
            rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr2, m2⟩, hvs, h⟩ <;> try dsimp only at h
              · rw [hopts]; exact .usingForArgsRevert henv he hspec' hlib (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨dcl, hdcl, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨rets, m3⟩, hcall, h⟩ <;> try dsimp only at h
                  · rw [hopts]
                    exact .usingForCallRevert henv he hspec' hlib (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl)
                      (ih.callFn _ _ _ _ _ hd)
                  · rw [IM.pure_some h, hopts]
                    exact .usingForCall henv he hspec' hlib (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl)
                      (ih.callFn _ _ _ _ _ hcall)
          · simp at h
      rename_i hspec
      split at h
      · -- push
        rename_i er e
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u', hu', h⟩ <;> try dsimp only at h
        · exact (guard'_error hd).elim
        · have hopts := opts_empty hu'
          split at h
          · rename_i x
            rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨v, fr2, m2⟩, hv, h⟩ <;> try dsimp only at h
            · rw [hopts]; exact .push1Revert henv he (ih.expr _ _ _ _ hd)
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨m3, hm3, h⟩ <;> try dsimp only at h
              · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
                rw [hopts]; exact .push1Panic henv he (ih.expr _ _ _ _ hv) hp
              · rw [IM.pure_some h]; rw [hopts]; exact .push1 henv he (ih.expr _ _ _ _ hv) (liftOp_ok hm3)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨m2, hm2, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              rw [hopts]; exact .push0Panic henv he hp
            · rw [IM.pure_some h]; rw [hopts]; exact .push0 henv he (liftOp_ok hm2)
          · simp at h
      · -- pop
        rename_i er e
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u', hu', h⟩ <;> try dsimp only at h
        · exact (guard'_error hd).elim
        · have hopts := opts_empty hu'
          split at h
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨m2, hm2, h⟩ <;> try dsimp only at h
            · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
              rw [hopts]; exact .popPanic henv he hp
            · rw [IM.pure_some h, hopts]; exact .pop henv he (liftOp_ok hm2)
          · simp at h
      · -- external call on a contract value
        rename_i c a
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨value, fr2, m2⟩, hval, h⟩ <;> try dsimp only at h
        · exact .externalValueRevert henv he (ih.valueOpt _ _ _ _ hd)
        · have hv := ih.valueOpt _ _ _ _ hval
          rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨gasReq, fr3, m3⟩, hgas, h⟩ <;> try dsimp only at h
          · exact .externalGasRevert henv he hv (ih.gasOpt _ _ _ _ hd)
          · have hg := ih.gasOpt _ _ _ _ hgas
            rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨vs, fr4, m4⟩, hvs, h⟩ <;> try dsimp only at h
              · exact .externalArgsRevert henv he hv hg (liftOpt_ok hes) (ih.exprs _ _ _ _ hd)
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨dcl, hdcl, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · split at h
                  · rename_i hnc
                    simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hnc
                    rw [IM.throw_bind_some h]
                    exact .externalCallNoCode henv he hv hg (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl) hnc.1 hnc.2
                  · rename_i hnc
                    simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq, not_and] at hnc
                    have h := IM.pure_bind_some h
                    try dsimp only at h
                    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨sigStr, ptys, rtys⟩, hsig, h⟩ <;> try dsimp only at h
                    · exact (liftOpt_error hd).elim
                    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨svs, m5⟩, hsvs, h⟩ <;> try dsimp only at h
                      · obtain ⟨p, hp, rfl⟩ := liftOp_error hd
                        exact .externalAbiPanic henv he hv hg (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl) (liftOpt_ok hsig) hp hnc
                      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨bs, hbs, h⟩ <;> try dsimp only at h
                        · exact (liftOpt_error hd).elim
                        · generalize hX : Interp.callViaEVM o m5 a value (selectorOf sigStr ++ bs.toByteArray)
                            (m5.evm.executionEnv.perm && dcl.mutability != Mutability.view && dcl.mutability != Mutability.pure)
                            (calleeGas o m5 gasReq value) = X at h
                          have hbridge := hX ▸ callViaEVM_sound o m5 a value (selectorOf sigStr ++ bs.toByteArray)
                            (m5.evm.executionEnv.perm && dcl.mutability != Mutability.view && dcl.mutability != Mutability.pure)
                            (calleeGas o m5 gasReq value)
                          obtain ⟨z, m6, out⟩ := X
                          dsimp only at h
                          cases z
                          · simp only [Bool.not_false, ite_true] at h
                            rw [IM.throw_bind_some h]
                            exact .externalCallFailed henv he hv hg (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl)
                              (liftOpt_ok hsig) (liftOp_ok hsvs) (liftOpt_ok hbs) hnc hbridge
                          · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
                            have h := IM.pure_bind_some h
                            try dsimp only at h
                            split at h
                            · rename_i rets m7 hdec
                              rw [IM.pure_some h]
                              exact .externalCall henv he hv hg (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl)
                                (liftOpt_ok hsig) (liftOp_ok hsvs) (liftOpt_ok hbs) hnc hbridge hdec
                            · rename_i hdec
                              rw [IM.throw_some h]
                              exact .externalCallDecodeFail henv he hv hg (liftOpt_ok hes) (ih.exprs _ _ _ _ hvs) (liftOpt_ok hdcl)
                                (liftOpt_ok hsig) (liftOp_ok hsvs) (liftOpt_ok hbs) hnc hbridge hdec
      · -- low-level call
        have hcv : isContractValue rv = false := isContractValue_false ‹_›
        rcases haddr : addrNat rv with _ | a
        · rw [haddr] at h
          cases args with
          | named fs => simp at h
          | positional es => rcases es with _ | ⟨dataE, _ | ⟨e2, es⟩⟩ <;> simp at h
        · rw [haddr] at h
          cases args with
          | named fs => simp at h
          | positional es =>
            rcases es with _ | ⟨dataE, _ | ⟨e2, es⟩⟩
            · simp at h
            · dsimp only at h
              rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨value, fr2, m2⟩, hval, h⟩ <;> try dsimp only at h
              · exact .lowLevelValueRevert (Or.inl rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hd)
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨gasReq, fr3, m3⟩, hgas, h⟩ <;> try dsimp only at h
                · exact .lowLevelGasRevert (Or.inl rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hval) (ih.gasOpt _ _ _ _ hd)
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨dv, fr4, m4⟩, hdv, h⟩ <;> try dsimp only at h
                  · exact .lowLevelDataRevert (Or.inl rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hval)
                      (ih.gasOpt _ _ _ _ hgas) (ih.expr _ _ _ _ hd)
                  · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨data, hdata, h⟩ <;> try dsimp only at h
                    · exact (liftOpt_error hd).elim
                    · rw [IM.pure_some h]
                      exact .lowLevelCall (Or.inl rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hval) (ih.gasOpt _ _ _ _ hgas)
                        (ih.expr _ _ _ _ hdv) (liftOpt_ok hdata) (callViaEVM_sound o m4 (EVM.address a) value data _ _) rfl
            · simp at h
      · -- low-level staticcall
        have hcv : isContractValue rv = false := isContractValue_false ‹_›
        rcases haddr : addrNat rv with _ | a
        · rw [haddr] at h
          cases args with
          | named fs => simp at h
          | positional es => rcases es with _ | ⟨dataE, _ | ⟨e2, es⟩⟩ <;> simp at h
        · rw [haddr] at h
          cases args with
          | named fs => simp at h
          | positional es =>
            rcases es with _ | ⟨dataE, _ | ⟨e2, es⟩⟩
            · simp at h
            · dsimp only at h
              rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨value, fr2, m2⟩, hval, h⟩ <;> try dsimp only at h
              · exact .lowLevelValueRevert (Or.inr rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hd)
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨gasReq, fr3, m3⟩, hgas, h⟩ <;> try dsimp only at h
                · exact .lowLevelGasRevert (Or.inr rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hval) (ih.gasOpt _ _ _ _ hd)
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨dv, fr4, m4⟩, hdv, h⟩ <;> try dsimp only at h
                  · exact .lowLevelDataRevert (Or.inr rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hval)
                      (ih.gasOpt _ _ _ _ hgas) (ih.expr _ _ _ _ hd)
                  · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨data, hdata, h⟩ <;> try dsimp only at h
                    · exact (liftOpt_error hd).elim
                    · rw [IM.pure_some h]
                      exact .lowLevelCall (Or.inr rfl) henv he hcv haddr (ih.valueOpt _ _ _ _ hval) (ih.gasOpt _ _ _ _ hgas)
                        (ih.expr _ _ _ _ hdv) (liftOpt_ok hdata) (callViaEVM_sound o m4 (EVM.address a) value data _ _) rfl
            · simp at h
      · -- delegatecall
        have hcv : isContractValue rv = false := isContractValue_false ‹_›
        rcases haddr : addrNat rv with _ | a
        · rw [haddr] at h
          cases args with
          | named fs => simp at h
          | positional es => rcases es with _ | ⟨dataE, _ | ⟨e2, es⟩⟩ <;> simp at h
        · rw [haddr] at h
          cases args with
          | named fs => simp at h
          | positional es =>
            rcases es with _ | ⟨dataE, _ | ⟨e2, es⟩⟩
            · simp at h
            · dsimp only at h
              rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨gasReq, fr2, m2⟩, hgas, h⟩ <;> try dsimp only at h
              · exact .delegateCallGasRevert henv he hcv haddr (ih.gasOpt _ _ _ _ hd)
              · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨dv, fr3, m3⟩, hdv, h⟩ <;> try dsimp only at h
                · exact .delegateCallDataRevert henv he hcv haddr (ih.gasOpt _ _ _ _ hgas) (ih.expr _ _ _ _ hd)
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨data, hdata, h⟩ <;> try dsimp only at h
                  · exact (liftOpt_error hd).elim
                  · rw [IM.pure_some h]
                    exact .delegateCall henv he hcv haddr (ih.gasOpt _ _ _ _ hgas) (ih.expr _ _ _ _ hdv) (liftOpt_ok hdata)
                      (delegateCallViaEVM_sound o m3 (EVM.address a) data _) rfl
            · simp at h
      · -- transfer
        have hcv : isContractValue rv = false := isContractValue_false ‹_›
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u', hu', h⟩ <;> try dsimp only at h
        · exact (guard'_error hd).elim
        · have hopts := opts_empty hu'
          rcases haddr : addrNat rv with _ | a
          · rw [haddr] at h
            cases args with
            | named fs => simp at h
            | positional es => rcases es with _ | ⟨amt, _ | ⟨e2, es⟩⟩ <;> simp at h
          · rw [haddr] at h
            cases args with
            | named fs => simp at h
            | positional es =>
              rcases es with _ | ⟨amt, _ | ⟨e2, es⟩⟩
              · simp at h
              · dsimp only at h
                rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨av, fr2, m2⟩, hav, h⟩ <;> try dsimp only at h
                · rw [hopts]; exact .transferAmtRevert (Or.inl rfl) henv he hcv haddr (ih.expr _ _ _ _ hd)
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨value, hvalue, h⟩ <;> try dsimp only at h
                  · exact (liftOpt_error hd).elim
                  · generalize hX : Interp.callViaEVM o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm
                      (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) = X at h
                    have hbridge := hX ▸ callViaEVM_sound o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm
                      (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value)
                    obtain ⟨z, m3, out⟩ := X
                    dsimp only at h
                    cases z
                    · simp only [beq_self_eq_true, eq_self_iff_true, Bool.false_eq_true, ite_true, ite_false] at h
                      rw [IM.throw_some h, hopts]
                      exact .transferFailed henv he hcv haddr (ih.expr _ _ _ _ hav) (liftOpt_ok hvalue) hbridge
                    · simp only [beq_self_eq_true, eq_self_iff_true, Bool.false_eq_true, ite_true, ite_false] at h
                      rw [IM.pure_some h, hopts]
                      exact .transfer henv he hcv haddr (ih.expr _ _ _ _ hav) (liftOpt_ok hvalue) hbridge
              · simp at h
      · -- send
        have hcv : isContractValue rv = false := isContractValue_false ‹_›
        rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨u', hu', h⟩ <;> try dsimp only at h
        · exact (guard'_error hd).elim
        · have hopts := opts_empty hu'
          rcases haddr : addrNat rv with _ | a
          · rw [haddr] at h
            cases args with
            | named fs => simp at h
            | positional es => rcases es with _ | ⟨amt, _ | ⟨e2, es⟩⟩ <;> simp at h
          · rw [haddr] at h
            cases args with
            | named fs => simp at h
            | positional es =>
              rcases es with _ | ⟨amt, _ | ⟨e2, es⟩⟩
              · simp at h
              · dsimp only at h
                rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨av, fr2, m2⟩, hav, h⟩ <;> try dsimp only at h
                · rw [hopts]; exact .transferAmtRevert (Or.inr rfl) henv he hcv haddr (ih.expr _ _ _ _ hd)
                · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨value, hvalue, h⟩ <;> try dsimp only at h
                  · exact (liftOpt_error hd).elim
                  · generalize hX : Interp.callViaEVM o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm
                      (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) = X at h
                    have hbridge := hX ▸ callViaEVM_sound o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm
                      (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value)
                    obtain ⟨z, m3, out⟩ := X
                    dsimp only at h
                    simp only [show ("send" == "transfer") = false from by decide, Bool.false_eq_true, ite_false] at h
                    rw [IM.pure_some h, hopts]
                    exact .send henv he hcv haddr (ih.expr _ _ _ _ hav) (liftOpt_ok hvalue) hbridge
              · simp at h
      · simp at h

end Solidity
