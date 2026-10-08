import Solm.Interp

/-!
# Soundness of the executable semantics

Every result the interpreter of `Solm/Interp.lean` produces is a derivation of the relational
semantics of `Solm/Semantics/Exec.lean`, provided the oracle's witnesses are the relation's: each
call result is a `Θ` result for some call gas and input substate, each creation result a `Lambda`
result (`Oracle.Sound`).  The relational semantics is the specification; nothing here changes it.
-/

namespace Solm.Interp

open ABI Ethereum Ethereum.EVM

/-- An oracle whose witnesses are the relation's existentials. -/
structure Oracle.Sound (o : Oracle Ω) : Prop where
  call : ∀ ω req evm res ω', o.call ω req evm = .ok (res, ω') →
    ∃ gas A_in, res = thetaCall gas A_in req evm
  create : ∀ ω req evm res ω', o.create ω req evm = .ok (res, ω') →
    ∃ gas A_in, res = lambdaCreate gas A_in req evm

theorem thetaOracle_sound (gas : UInt256) : (thetaOracle gas).Sound where
  call := fun _ _ evm _ _ h => by
    simp only [thetaOracle, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨gas, evm.substate, h.1.symm⟩
  create := fun _ _ evm _ _ h => by
    simp only [thetaOracle, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨gas, evm.substate, h.1.symm⟩

/-! ## Call bridges -/

/-- The `Θ` result behind `thetaCall` for a `CALL`/`STATICCALL` request. -/
theorem thetaCall_call (gas : UInt256) (A_in : Substate) (kind : CallKind)
    (hk : kind ≠ .delegatecall) (target : EVM.Address) (value : Int) (calldata : ByteArray)
    (calleePerm : Bool) (evm : EVM.State) :
    ∃ σ' g' A' z o,
      thetaCall gas A_in ⟨kind, target, value, calldata, calleePerm⟩ evm = ⟨z, σ', A', o⟩ ∧
      (σ', g', A', z, o) = Θ evm.accountMap evm.σ₀ A_in evm.executionEnv.codeOwner
        evm.executionEnv.sender target (toExecute evm.accountMap target) gas
        (.ofNat evm.executionEnv.gasPrice) (EVM.wordOfInt value) (EVM.wordOfInt value) calldata
        (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes
        evm.executionEnv.blocks calleePerm := by
  cases kind
  case delegatecall => exact absurd rfl hk
  all_goals
    unfold thetaCall
    dsimp only
    exact ⟨_, _, _, _, _, rfl, rfl⟩

/-- The `Θ` result behind `thetaCall` for a `DELEGATECALL` request. -/
theorem thetaCall_delegatecall (gas : UInt256) (A_in : Substate) (target : EVM.Address)
    (calldata : ByteArray) (calleePerm : Bool) (evm : EVM.State) :
    ∃ σ' g' A' z o,
      thetaCall gas A_in ⟨.delegatecall, target, 0, calldata, calleePerm⟩ evm = ⟨z, σ', A', o⟩ ∧
      (σ', g', A', z, o) = Θ evm.accountMap evm.σ₀ A_in evm.executionEnv.source
        evm.executionEnv.sender evm.executionEnv.codeOwner (toExecute evm.accountMap target) gas
        (.ofNat evm.executionEnv.gasPrice) ⟨0⟩ evm.executionEnv.weiValue calldata
        (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes
        evm.executionEnv.blocks evm.executionEnv.perm := by
  unfold thetaCall
  dsimp only
  exact ⟨_, _, _, _, _, rfl, rfl⟩

/-- The `Lambda` result behind `lambdaCreate`, in the shape of `newViaEVM.created`. -/
theorem lambdaCreate_spec (gas : UInt256) (A_in : Substate) (value : Int) (initCode : ByteArray)
    (salt : Option ByteArray) (evm : EVM.State) :
    ∃ addr σ' g' A' z o,
      lambdaCreate gas A_in ⟨value, initCode, salt⟩ evm = ⟨addr, σ', A', z⟩ ∧
      (addr, σ', g', A', z, o) = Lambda
        (evm.accountMap.insert evm.executionEnv.codeOwner
          { (evm.accountMap.get? evm.executionEnv.codeOwner |>.getD default) with
              nonce := (evm.accountMap.get? evm.executionEnv.codeOwner |>.getD default).nonce + ⟨1⟩ })
        evm.σ₀ A_in evm.executionEnv.codeOwner evm.executionEnv.sender gas
        (.ofNat evm.executionEnv.gasPrice) (EVM.wordOfInt value) initCode
        (evm.executionEnv.depth + 1) salt evm.executionEnv.header
        evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks evm.executionEnv.perm := by
  unfold lambdaCreate
  dsimp only
  exact ⟨_, _, _, _, _, _, rfl, rfl⟩

theorem newCanCreateB_iff (evm : EVM.State) (value : Int) (initCode : ByteArray) :
    newCanCreateB evm value initCode = true ↔ newCanCreate evm value initCode := by
  simp only [newCanCreateB, newCanCreate, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem callViaEVMRun_sound {o : Oracle Ω} (hs : o.Sound) {ω ω' : Ω} {evm : EVM.State}
    {target : EVM.Address} {value : Int} {calldata : ByteArray} {perm z : Bool} {evm' : EVM.State}
    {out : ByteArray}
    (h : callViaEVMRun o ω evm target value calldata perm = .ok ((z, evm', out), ω')) :
    callViaEVM evm target value calldata (z, evm', out) perm := by
  unfold callViaEVMRun at h
  dsimp only at h
  split at h
  · next hg =>
    simp only [callMadeGuard, decide_eq_true_eq] at hg
    split at h
    · next r ω'' hcall =>
      obtain ⟨gas, A_in, hr⟩ := hs.call _ _ _ _ _ hcall
      subst hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hz, hevm, hout⟩, -⟩ := h
      subst hz hevm hout
      obtain ⟨σ', g', A', z', o', hr, hΘ⟩ := thetaCall_call gas A_in
        (if perm then .call else .staticcall) (by cases perm <;> decide) target value calldata
        (perm && evm.executionEnv.perm) evm
      rw [hr]
      exact callViaEVM.callMade rfl ⟨gas, A_in, hΘ⟩ rfl hg.1 hg.2
    · cases h
  · next hg =>
    simp only [callMadeGuard, decide_eq_true_eq] at hg
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hz, hevm, hout⟩, -⟩ := h
    subst hz hevm hout
    exact callViaEVM.callNotMade rfl rfl hg

theorem delegateCallViaEVMRun_sound {o : Oracle Ω} (hs : o.Sound) {ω ω' : Ω} {evm : EVM.State}
    {target : EVM.Address} {calldata : ByteArray} {z : Bool} {evm' : EVM.State} {out : ByteArray}
    (h : delegateCallViaEVMRun o ω evm target calldata = .ok ((z, evm', out), ω')) :
    delegateCallViaEVM evm target calldata (z, evm', out) := by
  unfold delegateCallViaEVMRun at h
  dsimp only at h
  split at h
  · next hd =>
    split at h
    · next r ω'' hcall =>
      obtain ⟨gas, A_in, hr⟩ := hs.call _ _ _ _ _ hcall
      subst hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hz, hevm, hout⟩, -⟩ := h
      subst hz hevm hout
      obtain ⟨σ', g', A', z', o', hr, hΘ⟩ :=
        thetaCall_delegatecall gas A_in target calldata evm.executionEnv.perm evm
      rw [hr]
      exact delegateCallViaEVM.callMade ⟨gas, A_in, hΘ⟩ rfl hd
    · cases h
  · next hd =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hz, hevm, hout⟩, -⟩ := h
    subst hz hevm hout
    exact delegateCallViaEVM.callNotMade rfl rfl (not_ne_iff.1 hd)

theorem typedCallViaEVMRun_sound {o : Oracle Ω} (hs : o.Sound) {ω ω' : Ω} {cfg : Config}
    {evm : EVM.State} {target : EVM.Address} {name : Ident} {value : Int} {args : List Value}
    {perm z : Bool} {evm' : EVM.State} {out : ByteArray}
    (h : typedCallViaEVMRun o ω cfg evm target name value args perm = .ok ((z, evm', out), ω')) :
    typedCallViaEVM cfg evm target name value args (z, evm', out) perm := by
  unfold typedCallViaEVMRun at h
  split at h
  · cases h
  · next calldata henc => exact ⟨calldata, henc, callViaEVMRun_sound hs h⟩

theorem newViaEVMRun_sound {o : Oracle Ω} (hs : o.Sound) {ω ω' : Ω} {cfg : Config}
    {evm : EVM.State} {name : Ident} {value : Int} {args : List Value} {salt : Option ByteArray}
    {addr : EVM.Address} {evm' : EVM.State} {z : Bool}
    (h : newViaEVMRun o ω cfg evm name value args salt = .ok ((addr, evm', z), ω')) :
    newViaEVM cfg evm name value args salt (addr, evm', z) := by
  unfold newViaEVMRun at h
  split at h
  · cases h
  · next initCode hcode =>
    dsimp only at h
    split at h
    · next hg =>
      split at h
      · next r ω'' hcreate =>
        obtain ⟨gas, A_in, hr⟩ := hs.create _ _ _ _ _ hcreate
        subst hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨haddr, hevm, hz⟩, -⟩ := h
        subst haddr hevm hz
        obtain ⟨addr', σ', g', A', z', o', hr, hΛ⟩ :=
          lambdaCreate_spec gas A_in value initCode salt evm
        rw [hr]
        -- the rule's discarded gas and output are functions of the existential witnesses
        exact @newViaEVM.created cfg evm name value args salt (fun _ _ => g') (fun _ _ => o') initCode
          _ addr' σ' A' z' _ hcode ((newCanCreateB_iff _ _ _).1 hg) rfl ⟨gas, A_in, hΛ⟩ rfl
      · cases h
    · next hg =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨haddr, hevm, hz⟩, -⟩ := h
      subst haddr hevm hz
      exact newViaEVM.notCreated hcode fun hc => hg ((newCanCreateB_iff _ _ _).2 hc)

/-! ## Statements -/

theorem no_stuckEval {what : String} {e : EvalError} {ω ω' : Ω} {r : ExecResult}
    (h : (stuckEval what e, ω) = (Outcome.result r, ω')) : False := by
  cases e <;> simp [stuckEval] at h

/-- Soundness of the four statement-level interpreters, by induction on the fuel. -/
theorem exec_sound {o : Oracle Ω} (hs : o.Sound) (fuel : Nat) :
    (∀ {ω ω' : Ω} {cfg : Config} {solm : Frame} {evm : EVM.State} {stmt : Stmt} {r : ExecResult},
      execStmt fuel o ω cfg solm evm stmt = (.result r, ω') → ExecStmt cfg solm evm stmt r) ∧
    (∀ {ω ω' : Ω} {cfg : Config} {solm : Frame} {evm : EVM.State} {cond : Expr}
      {post body : List Stmt} {r : ExecResult},
      execForLoop fuel o ω cfg solm evm cond post body = (.result r, ω') →
      ExecForLoop cfg solm evm cond post body r) ∧
    (∀ {ω ω' : Ω} {cfg : Config} {solm : Frame} {evm : EVM.State} {stmts : List Stmt}
      {r : ExecResult},
      execBlock fuel o ω cfg solm evm stmts = (.result r, ω') → ExecBlock cfg solm evm stmts r) ∧
    (∀ {ω ω' : Ω} {cfg : Config} {solm : Frame} {evm : EVM.State} {body : List Stmt}
      {r : ExecResult},
      execFuncBody fuel o ω cfg solm evm body = (.result r, ω') →
      ExecFuncBody cfg solm evm body r) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω ω' cfg solm evm stmt r h; rw [execStmt] at h; cases h
    · intro ω ω' cfg solm evm cond post body r h; rw [execForLoop] at h; cases h
    · intro ω ω' cfg solm evm stmts r h; rw [execBlock] at h; cases h
    · intro ω ω' cfg solm evm body r h; rw [execFuncBody] at h; cases h
  | succ fuel ih =>
    obtain ⟨ihS, ihL, ihB, ihF⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `ExecStmt`
      intro ω ω' cfg solm evm stmt r h
      rw [execStmt] at h
      split at h
      · cases h
      rename_i hover
      clear hover
      cases stmt <;> try dsimp only at h
      case letDecl name ty expr =>
        split at h
        · next value hv => cases h; exact ExecStmt.letDecl hv
        · next hv => cases h; exact ExecStmt.letDeclRevert hv
        · exact (no_stuckEval h).elim
      case letStorage name ref =>
        split at h
        · next er ty hv => cases h; exact ExecStmt.letStorage hv
        · next hv => cases h; exact ExecStmt.letStorageRevert hv
        · exact (no_stuckEval h).elim
      case letGas name => cases h; exact ExecStmt.letGas _
      case assign origin slot expr =>
        split at h
        · next hv => cases h; exact ExecStmt.assignExprRevert hv
        · exact (no_stuckEval h).elim
        · next value hv =>
          split at h
          · next hst => cases h; exact ExecStmt.assignStoreRevert hv hst
          · exact (no_stuckEval h).elim
          · next solm' evm' hst =>
            split at h
            · next hc =>
              cases h
              obtain ⟨hor | hor, hp⟩ := hc <;> subst hor
              · exact ExecStmt.assignStatic hv hst hp
              · exact ExecStmt.assignTransientStatic hv hst hp
            · cases h; exact ExecStmt.assign hv hst
      case require cond =>
        split at h
        · next hc => cases h; exact ExecStmt.requireTrue hc
        · next hc => cases h; exact ExecStmt.requireFalse hc
        · next hc => cases h; exact ExecStmt.requireRevert hc
        · cases h
        · exact (no_stuckEval h).elim
      case «while» cond body =>
        split at h
        · next hc => cases h; exact ExecStmt.whileFalse hc
        · next hc => cases h; exact ExecStmt.whileCondRevert hc
        · next hc =>
          generalize hb : execBlock fuel o ω cfg solm evm body = p at h
          obtain ⟨oc, ω''⟩ := p
          rcases oc with (⟨s, e, v⟩ | ⟨s, e⟩ | ⟨s, e⟩ | ⟨s, e⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
          · cases h; exact ExecStmt.whileReturn hc (ihB hb)
          · exact ExecStmt.whileTrue hc (ihB hb) (ihS h)
          · cases h; exact ExecStmt.whileBreak hc (ihB hb)
          · exact ExecStmt.whileContinue hc (ihB hb) (ihS h)
          · cases h; exact ExecStmt.whileRevert hc (ihB hb)
          · cases h; exact ExecStmt.whileStatic hc (ihB hb)
          · cases h
          · cases h
          · cases h
        · cases h
        · exact (no_stuckEval h).elim
      case «for» init cond post body =>
        generalize hb : execBlock fuel o ω cfg solm evm init = p at h
        obtain ⟨oc, ω''⟩ := p
        rcases oc with (⟨s, e, v⟩ | ⟨s, e⟩ | ⟨s, e⟩ | ⟨s, e⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
        · cases h; exact ExecStmt.forInitReturn (ihB hb)
        · exact ExecStmt.for (ihB hb) (ihL h)
        · cases h
        · cases h
        · cases h; exact ExecStmt.forInitRevert (ihB hb)
        · cases h; exact ExecStmt.forInitStatic (ihB hb)
        · cases h
        · cases h
        · cases h
      case ite cond thenB elseB =>
        split at h
        · next hc => exact ExecStmt.iteTrue hc (ihB h)
        · next hc => exact ExecStmt.iteFalse hc (ihB h)
        · next hc => cases h; exact ExecStmt.iteCondRevert hc
        · cases h
        · exact (no_stuckEval h).elim
      case internalCall name args retVar =>
        split at h
        · next hargs => cases h; exact ExecStmt.internalCallArgsRevert hargs
        · exact (no_stuckEval h).elim
        · next argVals hargs =>
          split at h
          · cases h
          · next callee hcallee =>
            split at h
            · cases h
            · next locals hbind =>
              generalize hbody :
                execFuncBody fuel o ω cfg { solm with locals := locals } evm callee.body = p at h
              obtain ⟨oc, ω''⟩ := p
              rcases oc with (⟨s, e, v⟩ | ⟨s, e⟩ | ⟨s, e⟩ | ⟨s, e⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
              · cases h; exact ExecStmt.internalCallReturn hargs hcallee hbind (ihF hbody)
              · cases h
              · cases h
              · cases h
              · cases h; exact ExecStmt.internalCallRevert hargs hcallee hbind (ihF hbody)
              · cases h; exact ExecStmt.internalCallStatic hargs hcallee hbind (ihF hbody)
              · cases h
              · cases h
              · cases h
      case externalCall receiver name eth args retVar perm' =>
        split at h
        · next hrecv => cases h; exact ExecStmt.externalCallReceiverRevert hrecv
        · exact (no_stuckEval h).elim
        · next target hrecv =>
          split at h
          · next hval => cases h; exact ExecStmt.externalCallSendRevert hrecv hval
          · exact (no_stuckEval h).elim
          · next sendVal hval =>
            split at h
            · next hargs => cases h; exact ExecStmt.externalCallArgsRevert hrecv hval hargs
            · exact (no_stuckEval h).elim
            · next argVals hargs =>
              split at h
              · next hc => cases h; exact ExecStmt.externalCallStatic hrecv hval hargs hc.1 hc.2
              · next hc =>
                split at h
                · cases h
                · next evm' out ω'' hcall =>
                  cases h
                  exact ExecStmt.externalCallFailure hrecv hval hargs
                    (typedCallViaEVMRun_sound hs hcall)
                · next evm' out ω'' hcall =>
                  split at h
                  · next value hdec =>
                    cases h
                    exact ExecStmt.externalCallSuccess hrecv hval hargs
                      (typedCallViaEVMRun_sound hs hcall) hdec
                  · next hdec =>
                    cases h
                    exact ExecStmt.externalCallReturnDecodeRevert hrecv hval hargs
                      (typedCallViaEVMRun_sound hs hcall) hdec
          · cases h
        · cases h
      case lowLevelCall receiver eth cdata okVar dataVar perm' =>
        split at h
        · next hrecv => cases h; exact ExecStmt.lowLevelCallReceiverRevert hrecv
        · exact (no_stuckEval h).elim
        · next target hrecv =>
          split at h
          · next hval => cases h; exact ExecStmt.lowLevelCallSendRevert hrecv hval
          · exact (no_stuckEval h).elim
          · next sendVal hval =>
            split at h
            · next hcd => cases h; exact ExecStmt.lowLevelCallDataRevert hrecv hval hcd
            · exact (no_stuckEval h).elim
            · next calldata hcd =>
              split at h
              · next hc => cases h; exact ExecStmt.lowLevelCallStatic hrecv hval hcd hc.1 hc.2
              · next hc =>
                split at h
                · cases h
                · next z evm' out ω'' hcall =>
                  cases h
                  cases z
                  · exact ExecStmt.lowLevelCallFailure hrecv hval hcd (callViaEVMRun_sound hs hcall)
                  · exact ExecStmt.lowLevelCallSuccess hrecv hval hcd (callViaEVMRun_sound hs hcall)
            · cases h
          · cases h
        · cases h
      case delegateCall receiver cdata okVar dataVar =>
        split at h
        · next hrecv => cases h; exact ExecStmt.delegateCallReceiverRevert hrecv
        · exact (no_stuckEval h).elim
        · next target hrecv =>
          split at h
          · next hcd => cases h; exact ExecStmt.delegateCallDataRevert hrecv hcd
          · exact (no_stuckEval h).elim
          · next calldata hcd =>
            split at h
            · cases h
            · next z evm' out ω'' hcall =>
              cases h
              cases z
              · exact ExecStmt.delegateCallFailure hrecv hcd (delegateCallViaEVMRun_sound hs hcall)
              · exact ExecStmt.delegateCallSuccess hrecv hcd (delegateCallViaEVMRun_sound hs hcall)
          · cases h
        · cases h
      case checkedCall receiver name eth args retVar onSuccess errVar onFail perm' =>
        split at h
        · next hrecv => cases h; exact ExecStmt.checkedCallReceiverRevert hrecv
        · exact (no_stuckEval h).elim
        · next target hrecv =>
          split at h
          · next hval => cases h; exact ExecStmt.checkedCallSendRevert hrecv hval
          · exact (no_stuckEval h).elim
          · next sendVal hval =>
            split at h
            · next hargs => cases h; exact ExecStmt.checkedCallArgsRevert hrecv hval hargs
            · exact (no_stuckEval h).elim
            · next argVals hargs =>
              split at h
              · next hc => cases h; exact ExecStmt.checkedCallStatic hrecv hval hargs hc.1 hc.2
              · next hc =>
                split at h
                · cases h
                · next evm' out ω'' hcall =>
                  exact ExecStmt.checkedCallFail hrecv hval hargs
                    (typedCallViaEVMRun_sound hs hcall) (ihB h)
                · next evm' out ω'' hcall =>
                  split at h
                  · next value hdec =>
                    exact ExecStmt.checkedCallSuccess hrecv hval hargs
                      (typedCallViaEVMRun_sound hs hcall) hdec (ihB h)
                  · next hdec =>
                    cases h
                    exact ExecStmt.checkedCallReturnDecodeRevert hrecv hval hargs
                      (typedCallViaEVMRun_sound hs hcall) hdec
          · cases h
        · cases h
      case new name valExpr args retVar salt =>
        split at h
        · next hv => cases h; exact ExecStmt.newValueRevert hv
        · exact (no_stuckEval h).elim
        · next sendVal hv =>
          split at h
          · next hargs => cases h; exact ExecStmt.newArgsRevert hv hargs
          · exact (no_stuckEval h).elim
          · next argVals hargs =>
            split at h
            · exact (no_stuckEval h).elim
            · cases h
            · next saltBytes hsalt =>
              split at h
              · next hp => cases h; exact ExecStmt.newStatic hv hargs hsalt hp
              · next hp =>
                split at h
                · cases h
                · next addr evm' ω'' hcall =>
                  cases h
                  exact ExecStmt.newSuccess hv hargs hsalt (newViaEVMRun_sound hs hcall)
                · next addr evm' ω'' hcall =>
                  cases h
                  exact ExecStmt.newRevert hv hargs hsalt (newViaEVMRun_sound hs hcall)
        · cases h
      case «return» exprs =>
        split at h
        · next values hv => cases h; exact ExecStmt.return hv
        · next hv => cases h; exact ExecStmt.returnRevert hv
        · exact (no_stuckEval h).elim
      case setImmutable name expr =>
        split at h
        · next hv => cases h; exact ExecStmt.setImmutableRevert hv
        · exact (no_stuckEval h).elim
        · next value hv =>
          split at h
          · cases h
          · next ty hty =>
            split at h
            · next hfit => cases h; exact ExecStmt.setImmutable hv hty hfit
            · cases h
      case «break» => cases h; exact ExecStmt.break
      case «continue» => cases h; exact ExecStmt.continue
      case emit name args =>
        split at h
        · next hargs => cases h; exact ExecStmt.emitArgsRevert hargs
        · exact (no_stuckEval h).elim
        · next vals hargs =>
          split at h
          · next hp => cases h; exact ExecStmt.emitStatic hargs hp
          · cases h; exact ExecStmt.emit hargs
      case push ref e? =>
        cases e? with
        | none =>
          dsimp only at h
          split at h
          · next hp => cases h; exact ExecStmt.pushGrowRevert hp
          · exact (no_stuckEval h).elim
          · next evm' hp =>
            split at h
            · next hperm => cases h; exact ExecStmt.pushGrowStatic hp hperm
            · cases h; exact ExecStmt.pushGrow hp
        | some expr =>
          dsimp only at h
          split at h
          · next hv => cases h; exact ExecStmt.pushValExprRevert hv
          · exact (no_stuckEval h).elim
          · next value hv =>
            split at h
            · next hp => cases h; exact ExecStmt.pushValStoreRevert hv hp
            · exact (no_stuckEval h).elim
            · next evm' hp =>
              split at h
              · next hperm => cases h; exact ExecStmt.pushValStatic hv hp hperm
              · cases h; exact ExecStmt.pushVal hv hp
      case pop ref =>
        split at h
        · next hp => cases h; exact ExecStmt.popRevert hp
        · exact (no_stuckEval h).elim
        · next evm' hp =>
          split at h
          · next hperm => cases h; exact ExecStmt.popStatic hp hperm
          · cases h; exact ExecStmt.pop hp
      case delete ref =>
        split at h
        · next hp => cases h; exact ExecStmt.deleteRevert hp
        · exact (no_stuckEval h).elim
        · next evm' hp =>
          split at h
          · next hperm => cases h; exact ExecStmt.deleteStatic hp hperm
          · cases h; exact ExecStmt.delete hp
    · -- `ExecForLoop`
      intro ω ω' cfg solm evm cond post body r h
      rw [execForLoop] at h
      split at h
      · next hc => cases h; exact ExecForLoop.falseDone hc
      · next hc => cases h; exact ExecForLoop.condRevert hc
      · next hc =>
        generalize hb : execBlock fuel o ω cfg solm evm body = p at h
        obtain ⟨oc, ω''⟩ := p
        rcases oc with (⟨s, e, v⟩ | ⟨s, e⟩ | ⟨s, e⟩ | ⟨s, e⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
        · cases h; exact ExecForLoop.bodyReturn hc (ihB hb)
        · generalize hp : execBlock fuel o ω'' cfg s e post = q at h
          obtain ⟨oc, ω₃⟩ := q
          rcases oc with (⟨s₂, e₂, v₂⟩ | ⟨s₂, e₂⟩ | ⟨s₂, e₂⟩ | ⟨s₂, e₂⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
          · cases h
          · exact ExecForLoop.iterate hc (ihB hb) (ihB hp) (ihL h)
          · cases h
          · cases h
          · cases h; exact ExecForLoop.iteratePostRevert hc (ihB hb) (ihB hp)
          · cases h; exact ExecForLoop.iteratePostStatic hc (ihB hb) (ihB hp)
          · cases h
          · cases h
          · cases h
        · cases h; exact ExecForLoop.bodyBreak hc (ihB hb)
        · generalize hp : execBlock fuel o ω'' cfg s e post = q at h
          obtain ⟨oc, ω₃⟩ := q
          rcases oc with (⟨s₂, e₂, v₂⟩ | ⟨s₂, e₂⟩ | ⟨s₂, e₂⟩ | ⟨s₂, e₂⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
          · cases h
          · exact ExecForLoop.continueIter hc (ihB hb) (ihB hp) (ihL h)
          · cases h
          · cases h
          · cases h; exact ExecForLoop.continuePostRevert hc (ihB hb) (ihB hp)
          · cases h; exact ExecForLoop.continuePostStatic hc (ihB hb) (ihB hp)
          · cases h
          · cases h
          · cases h
        · cases h; exact ExecForLoop.bodyRevert hc (ihB hb)
        · cases h; exact ExecForLoop.bodyStatic hc (ihB hb)
        · cases h
        · cases h
        · cases h
      · cases h
      · exact (no_stuckEval h).elim
    · -- `ExecBlock`
      intro ω ω' cfg solm evm stmts r h
      cases stmts with
      | nil => rw [execBlock] at h; cases h; exact ExecBlock.nil
      | cons stmt rest =>
        rw [execBlock] at h
        generalize hst : execStmt fuel o ω cfg solm evm stmt = p at h
        obtain ⟨oc, ω''⟩ := p
        rcases oc with (⟨s, e, v⟩ | ⟨s, e⟩ | ⟨s, e⟩ | ⟨s, e⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
        · cases h; exact ExecBlock.consReturn (ihS hst)
        · exact ExecBlock.consNormal (ihS hst) (ihB h)
        · cases h; exact ExecBlock.consBreak (ihS hst)
        · cases h; exact ExecBlock.consContinue (ihS hst)
        · cases h; exact ExecBlock.consRevert (ihS hst)
        · cases h; exact ExecBlock.consStatic (ihS hst)
        · cases h
        · cases h
        · cases h
    · -- `ExecFuncBody`
      intro ω ω' cfg solm evm body r h
      rw [execFuncBody] at h
      generalize hb : execBlock fuel o ω cfg solm evm body = p at h
      obtain ⟨oc, ω''⟩ := p
      rcases oc with (⟨s, e, v⟩ | ⟨s, e⟩ | ⟨s, e⟩ | ⟨s, e⟩ | _ | _) | _ | _ | _ <;> dsimp only at h
      · cases h; exact ExecFuncBody.execBlockRet (ihB hb)
      · cases h; exact ExecFuncBody.execBlockOK (ihB hb)
      · cases h; exact ExecFuncBody.execBlockBreak (ihB hb)
      · cases h; exact ExecFuncBody.execBlockContinue (ihB hb)
      · cases h; exact ExecFuncBody.execBlockRevert (ihB hb)
      · cases h; exact ExecFuncBody.execBlockStatic (ihB hb)
      · cases h
      · cases h
      · cases h

theorem execStmt_sound {o : Oracle Ω} (hs : o.Sound) {fuel : Nat} {ω ω' : Ω} {cfg : Config}
    {solm : Frame} {evm : EVM.State} {stmt : Stmt} {r : ExecResult}
    (h : execStmt fuel o ω cfg solm evm stmt = (.result r, ω')) : ExecStmt cfg solm evm stmt r :=
  (exec_sound hs fuel).1 h

theorem execForLoop_sound {o : Oracle Ω} (hs : o.Sound) {fuel : Nat} {ω ω' : Ω} {cfg : Config}
    {solm : Frame} {evm : EVM.State} {cond : Expr} {post body : List Stmt} {r : ExecResult}
    (h : execForLoop fuel o ω cfg solm evm cond post body = (.result r, ω')) :
    ExecForLoop cfg solm evm cond post body r :=
  (exec_sound hs fuel).2.1 h

theorem execBlock_sound {o : Oracle Ω} (hs : o.Sound) {fuel : Nat} {ω ω' : Ω} {cfg : Config}
    {solm : Frame} {evm : EVM.State} {stmts : List Stmt} {r : ExecResult}
    (h : execBlock fuel o ω cfg solm evm stmts = (.result r, ω')) : ExecBlock cfg solm evm stmts r :=
  (exec_sound hs fuel).2.2.1 h

theorem execFuncBody_sound {o : Oracle Ω} (hs : o.Sound) {fuel : Nat} {ω ω' : Ω} {cfg : Config}
    {solm : Frame} {evm : EVM.State} {body : List Stmt} {r : ExecResult}
    (h : execFuncBody fuel o ω cfg solm evm body = (.result r, ω')) :
    ExecFuncBody cfg solm evm body r :=
  (exec_sound hs fuel).2.2.2 h

/-! ## Messages -/

theorem solmExecRun_sound {o : Oracle Ω} (hs : o.Sound) {fuel : Nat} {ω ω' : Ω} {cfg : Config}
    {contract : ContractDecl} {immutables : Store} {σ σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv} {r : ExecResult} {rc : ReturnConvention}
    (h : solmExecRun fuel o ω cfg contract immutables σ σ₀ g A I = (.ran (.result r) rc, ω')) :
    solmExec cfg contract immutables σ σ₀ g A I r rc := by
  unfold solmExecRun at h
  dsimp only at h
  split at h
  · next transition hsel =>
    split at h
    · next callargs hdec =>
      generalize hbody : execTransitionBody fuel o ω cfg contract (initialState σ σ₀ g A I)
        callargs transition.body immutables = p at h
      obtain ⟨oc, ω₀⟩ := p
      cases h
      exact solmExec.intro hsel rfl hdec rfl (execFuncBody_sound hs hbody)
    · cases h
  · next hsel =>
    split at h
    · next transition hrecv =>
      split at h
      · next hshape =>
        generalize hbody : execTransitionBody fuel o ω cfg contract (initialState σ σ₀ g A I)
          ∅ transition.body immutables = p at h
        obtain ⟨oc, ω₀⟩ := p
        cases h
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hshape
        exact solmExec.receive hrecv hshape.1 hshape.2 rfl (execFuncBody_sound hs hbody)
      · cases h
    · next hrecv =>
      split at h
      · next transition hfb =>
        split at h
        · next callargs rc₀ hargs hrc =>
          generalize hbody : execTransitionBody fuel o ω cfg contract (initialState σ σ₀ g A I)
            callargs transition.body immutables = p at h
          obtain ⟨oc, ω₀⟩ := p
          cases h
          exact solmExec.fallback hsel hrecv hfb hargs hrc rfl (execFuncBody_sound hs hbody)
        · cases h
      · cases h

theorem solmCtorExecRun_sound {o : Oracle Ω} (hs : o.Sound) {fuel : Nat} {ω ω' : Ω}
    {cfg : Config} {contract : ContractDecl} {args : List Value} {σ σ₀ : AccountMap}
    {g : UInt256} {A : Substate} {I : ExecutionEnv} {r : ExecResult}
    (h : solmCtorExecRun fuel o ω cfg contract args σ σ₀ g A I = some (.result r, ω')) :
    solmCtorExec cfg contract args σ σ₀ g A I r := by
  unfold solmCtorExecRun at h
  split at h
  · next hlen =>
    simp only [Option.some.injEq] at h
    exact solmCtorExec.intro rfl hlen rfl (execFuncBody_sound hs h)
  · cases h

end Solm.Interp
