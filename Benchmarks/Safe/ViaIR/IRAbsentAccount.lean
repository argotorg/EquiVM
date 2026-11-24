import Benchmarks.Safe.ViaIR.AddOwnerSource
import Benchmarks.Safe.ViaIR.Calldata

variable {fork : Ethereum.Fork}

/-! Regression witness for the IR owner's cached increment with an absent executing account.

The public refinement premises permit this account map. Storage writes leave it unchanged,
so the source's threshold check reads zero, while the IR check uses the incremented value one.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def safeIRAbsentOwnerCalldata : ByteArray :=
  ⟨#[0x0d, 0x58, 0x2f, 0x13]⟩ ++
    (UInt256.ofNat 8192).toByteArray ++ (UInt256.ofNat 1).toByteArray

def safeIRAbsentOwnerEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    codeOwner := AccountAddress.ofNat 4096
    source := AccountAddress.ofNat 4096
    calldata := safeIRAbsentOwnerCalldata
    weiValue := ⟨0⟩
    perm := true }

def safeIRAbsentOwnerState : State :=
  initState default default (.ofUInt256 ⟨100000⟩) default safeIRAbsentOwnerEnv

theorem safeIRAbsentOwnerPremises :
    safeIRAbsentOwnerEnv.code = safeBytecode ∧
      safeIRAbsentOwnerEnv.calldata.size < UInt256.size ∧
      selectorDispatchMsg contract safeIRAbsentOwnerEnv.calldata =
        some addownerwiththresholdTransition := by
  refine ⟨rfl, ?_, ?_⟩ <;> native_decide

theorem safeIRAbsentOwnerDecoding :
    config.externalABI.decodeCalldata?
      (addownerwiththresholdTransition.params.map Param.name)
      (transitionSignature addownerwiththresholdTransition).paramTypes
      safeIRAbsentOwnerEnv.calldata = some (addOwnerArgs ⟨8192⟩ ⟨1⟩) := by
  have hkey : calldataWord safeIRAbsentOwnerCalldata 4 = ⟨8192⟩ := by native_decide
  have hthreshold : calldataWord safeIRAbsentOwnerCalldata 36 = ⟨1⟩ := by native_decide
  have hdec := decodeCalldata_addr_uint256_ok (cd := safeIRAbsentOwnerCalldata)
    (x := "owner") (y := "_threshold") (by native_decide) (by native_decide)
    (by rw [hkey]; decide)
  simpa only [hkey, hthreshold] using hdec

theorem safeIRAbsentOwnerSourceReverts :
    ExecTransitionBody fork config contract safeIRAbsentOwnerState (addOwnerArgs ⟨8192⟩ ⟨1⟩)
      addownerwiththresholdTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safeAddOwnerPrefix (hperm := rfl) safeIRAbsentOwnerState ⟨8192⟩ ⟨1⟩
    (by decide) rfl rfl
    ⟨by decide, by decide, Or.inl (by decide)⟩ (by rfl)
  apply safeAddOwnerTailRevert (hperm := rfl)
  · decide
  · apply safeAddOwnerThresholdRevert
    · decide
    · apply safeThresholdSourceTooLarge
      decide

theorem safeIRAbsentOwnerExecution :
    (match Ξ .cancun default default ⟨100000⟩ default safeIRAbsentOwnerEnv with
      | .ok (.success (_, gas, _) output) => gas == ⟨28205⟩ && output.isEmpty
      | _ => false) = true := by
  native_decide

theorem safeIRAbsentOwnerResultsDiffer (rc : ReturnConvention) :
    ¬execResultsEquiv (Ξ .cancun default default ⟨100000⟩ default safeIRAbsentOwnerEnv)
      .reverted rc := by
  intro heq
  have hsuccess := safeIRAbsentOwnerExecution
  cases heq <;> simp_all

private def nonHalting (r : ExecResult) : Prop :=
  r ≠ .reverted ∧ r ≠ .staticViolation

private theorem requireTail {cfg f s cond tail r}
    (h : ExecBlock fork cfg f s (.require cond :: tail) r) (hr : nonHalting r) :
    ExecBlock fork cfg f s tail r := by
  cases h with
  | consNormal hs ht => cases hs; exact ht
  | consReturn hs => cases hs
  | consBreak hs => cases hs
  | consContinue hs => cases hs
  | consRevert => exact (hr.1 rfl).elim
  | consStatic => exact (hr.2 rfl).elim

private theorem twoRequiresReturn {cfg f s c₁ c₂ f' s' value}
    (h : ExecFuncBody fork cfg f s [.require c₁, .require c₂] (.returned f' s' value)) :
    f' = f ∧ s' = s ∧ value = none := by
  cases h <;> rename_i hb
  all_goals
    have ht := requireTail (requireTail hb (by constructor <;> intro h <;> cases h))
      (by constructor <;> intro h <;> cases h)
    cases ht
  exact ⟨rfl, rfl, rfl⟩

private theorem consTail {cfg f s stmt tail r f' s'}
    (h : ExecBlock fork cfg f s (stmt :: tail) r) (hr : nonHalting r)
    (hs : ∀ result, ExecStmt fork cfg f s stmt result →
      result = .ok f' s' ∨ result = .reverted ∨ result = .staticViolation) :
    ExecBlock fork cfg f' s' tail r := by
  cases h with
  | consNormal hstmt ht =>
    rcases hs _ hstmt with he | he | he
    · cases he; exact ht
    · cases he
    · cases he
  | consReturn hstmt => rcases hs _ hstmt with he | he | he <;> cases he
  | consBreak hstmt => rcases hs _ hstmt with he | he | he <;> cases he
  | consContinue hstmt => rcases hs _ hstmt with he | he | he <;> cases he
  | consRevert => exact (hr.1 rfl).elim
  | consStatic => exact (hr.2 rfl).elim

private theorem assignResult {cfg f s origin ref expr f' s'}
    (h : ExecStmt fork cfg f s (.assign origin ref expr) (.ok f' s'))
    (r) (h' : ExecStmt fork cfg f s (.assign origin ref expr) r) :
    r = .ok f' s' ∨ r = .reverted ∨ r = .staticViolation := by
  cases h with
  | assign _ heval hstore => cases h' <;> simp_all

private theorem emitResult {cfg f s name args r}
    (h : ExecStmt fork cfg f s (.emit name args) r) :
    r = .ok f s ∨ r = .reverted ∨ r = .staticViolation := by
  cases h <;> simp

private theorem singletonResult {cfg f s stmt r} (h : ExecBlock fork cfg f s [stmt] r) :
    ExecStmt fork cfg f s stmt r := by
  cases h with
  | consNormal hs ht => cases ht; exact hs
  | consReturn hs | consBreak hs | consContinue hs | consRevert hs | consStatic hs => exact hs

private theorem falseRequireBlock {cfg f s cond tail r}
    (h : ExecBlock fork cfg f s (.require cond :: tail) r) (hr : nonHalting r)
    (hf : evalExpr? cfg f s cond = .ok (.bool false)) : False := by
  cases h with
  | consNormal hs _ => cases hs with | requireTrue ht => rw [hf] at ht; cases ht
  | consReturn hs => cases hs
  | consBreak hs => cases hs
  | consContinue hs => cases hs
  | consRevert => exact hr.1 rfl
  | consStatic => exact hr.2 rfl

private theorem absentCanAddResult (r)
    (h : ExecStmt fork config (addOwnerFrame ⟨8192⟩ ⟨1⟩) safeIRAbsentOwnerState
      (.internalCall "requireCanAddOwner" [.var "owner"] "_ok") r) :
    r = .ok (addOwnerFrame₁ ⟨8192⟩ ⟨1⟩) safeIRAbsentOwnerState ∨
      r = .reverted ∨ r = .staticViolation := by
  cases h with
  | internalCallReturn heval hlookup hbind hbody =>
    have he : evalExprs? config (addOwnerFrame ⟨8192⟩ ⟨1⟩) safeIRAbsentOwnerState
        [.var "owner"] = .ok [.address (AccountAddress.ofNat 8192)] := by
      simp [addOwnerFrame, addOwnerArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
        EvalResult.bind, bind, pure, Std.HashMap.getElem_insert]
      rfl
    rw [he] at heval
    cases heval
    have hl : lookupCallable? (addOwnerFrame ⟨8192⟩ ⟨1⟩).contract "requireCanAddOwner" =
        some requireCanAddOwnerFunction.toCallable := rfl
    rw [hl] at hlookup
    cases hlookup
    have hb : bindParams? requireCanAddOwnerFunction.toCallable.params
        [.address (AccountAddress.ofNat 8192)] = some (canAddOwnerArgs ⟨8192⟩) := rfl
    rw [hb] at hbind
    cases hbind
    obtain ⟨_, hs, hv⟩ := twoRequiresReturn hbody
    subst hs
    subst hv
    exact .inl rfl
  | internalCallRevert => exact .inr (.inl rfl)
  | internalCallArgsRevert => exact .inr (.inl rfl)
  | internalCallStatic => exact .inr (.inr rfl)

private theorem absentThresholdCannotReturn {f s value}
    (h : ExecFuncBody fork config (thresholdFrame ⟨1⟩) safeIRAbsentOwnerState
      changeThresholdBodyFunction.body (.returned f s value)) : False := by
  have hf := safeThresholdBound safeIRAbsentOwnerState ⟨1⟩
  change evalExpr? config (thresholdFrame ⟨1⟩) safeIRAbsentOwnerState
    (leE (.var "_threshold") (.storage ownerCountRef)) = .ok (.bool false) at hf
  cases h <;> rename_i hb
  all_goals exact falseRequireBlock hb (by constructor <;> intro h <;> cases h) hf

private theorem absentThresholdStmt {r}
    (h : ExecStmt fork config (addOwnerFrame₁ ⟨8192⟩ ⟨1⟩) safeIRAbsentOwnerState
      (.internalCall "changeThresholdBody" [.var "_threshold"] "_thresholdChanged") r)
    (hr : nonHalting r) : False := by
  cases h with
  | internalCallReturn heval hlookup hbind hbody =>
    have he : evalExprs? config (addOwnerFrame₁ ⟨8192⟩ ⟨1⟩) safeIRAbsentOwnerState
        [.var "_threshold"] = .ok [.int 1] :=
      evalExprs?_singleton (safeAddOwnerEvalThreshold _ _ _)
    rw [he] at heval
    cases heval
    have hl : lookupCallable? (addOwnerFrame₁ ⟨8192⟩ ⟨1⟩).contract "changeThresholdBody" =
        some changeThresholdBodyFunction.toCallable := rfl
    rw [hl] at hlookup
    cases hlookup
    have hb : bindParams? changeThresholdBodyFunction.toCallable.params [.int 1] =
        some (thresholdArgs ⟨1⟩) := rfl
    rw [hb] at hbind
    cases hbind
    exact absentThresholdCannotReturn hbody
  | internalCallRevert => exact hr.1 rfl
  | internalCallArgsRevert => exact hr.1 rfl
  | internalCallStatic => exact hr.2 rfl

private theorem absentAddOwnerBlock {r}
    (h : ExecBlock fork config (addOwnerFrame ⟨8192⟩ ⟨1⟩) safeIRAbsentOwnerState
      addownerwiththresholdTransition.body r) (hr : nonHalting r) : False := by
  have htail := consTail (requireTail (requireTail h hr) hr) hr absentCanAddResult
  let f := addOwnerFrame₁ ⟨8192⟩ ⟨1⟩
  let s := safeIRAbsentOwnerState
  have hb : f.locals["owners"]? = none := safeAddOwnerLocal _ _ _ (by decide)
  have hfirst : ExecStmt fork config f s
      (.assign .storage (ownersRef (.var "owner")) (.storage (ownersRef sentinelAddr)))
      (.ok f s) := .assign (Or.inr rfl)
    (safeEvalOwnerLink s _ sentinelAddr ⟨1⟩ hb (by decide) (safeEvalOwnerSentinel s _))
    (safeAssignOwnerLink s _ _ ⟨8192⟩ (ownerLink s ⟨1⟩) hb (by decide)
      (solcAddrMask_result_canonical _) (safeAddOwnerEval s ⟨8192⟩ ⟨1⟩))
  have hsecond : ExecStmt fork config f s
      (.assign .storage (ownersRef sentinelAddr) (.var "owner")) (.ok f s) :=
    .assign (Or.inr rfl) (safeAddOwnerEval s ⟨8192⟩ ⟨1⟩)
      (safeAssignOwnerLink s _ sentinelAddr ⟨1⟩ ⟨8192⟩ hb (by decide) (by decide)
        (safeEvalOwnerSentinel s _))
  have hcount : ExecStmt fork config f s
      (.assign .storage ownerCountRef (inc256 (.storage ownerCountRef))) (.ok f s) :=
    safeAddOwnerIncrement (hperm := rfl) s ⟨8192⟩ ⟨1⟩ (by decide)
  have hafter := consTail (consTail (consTail htail hr (assignResult hfirst)) hr
    (assignResult hsecond)) hr (assignResult hcount)
  have hlast := singletonResult (consTail hafter hr (fun _ hs ↦ emitResult hs))
  have hc := safeAddOwnerThresholdGuard s ⟨8192⟩ ⟨1⟩
  change evalExpr? config f s (neE (.storage thresholdRef) (.var "_threshold")) =
    .ok (.bool true) at hc
  cases hlast with
  | iteTrue _ hcall => exact absentThresholdStmt (singletonResult hcall) hr
  | iteFalse hf _ => rw [hc] at hf; cases hf
  | iteCondRevert => exact hr.1 rfl

theorem safeIRAbsentOwnerSourceCannotReturn {f s value} :
    ¬ExecTransitionBody fork config contract safeIRAbsentOwnerState (addOwnerArgs ⟨8192⟩ ⟨1⟩)
      addownerwiththresholdTransition.body (.returned f s value) := by
  intro h
  cases h <;> rename_i hb
  all_goals exact absentAddOwnerBlock hb (by constructor <;> intro h <;> cases h)

/-- The unrestricted runtime obligation includes this input and is false for the current model. -/
theorem safeIRAbsentOwnerNotRefines :
    ¬runtimeRefinementFor .cancun config contract default default ⟨100000⟩ default
      safeIRAbsentOwnerEnv := by
  intro h
  have hex := safeIRAbsentOwnerExecution
  cases h with
  | execution hxi hstele hrel =>
    cases hrel with
    | success hevm hsource _ _ =>
      cases hsource
      cases hstele with
      | intro hsel hsig hdec hstate hbody =>
        rw [safeIRAbsentOwnerPremises.2.2] at hsel
        cases hsel
        subst hsig
        rw [safeIRAbsentOwnerDecoding] at hdec
        cases hdec
        cases hstate
        exact safeIRAbsentOwnerSourceCannotReturn hbody
      | fallback hsel _ _ _ _ _ _ =>
        rw [safeIRAbsentOwnerPremises.2.2] at hsel
        cases hsel
      | receive hrecv _ _ _ _ =>
        change none = some _ at hrecv
        cases hrecv
    | revert hevm _ | noMatch hevm _ | decodingFailed hevm _ =>
      rw [hxi, hevm] at hex
      cases hex
    | invalidHalt hevm _ | staticHalt hevm _ =>
      rw [hxi, hevm] at hex
      cases hex
  | outOfGas hevm =>
    rw [hevm] at hex
    cases hex

end Benchmarks.Safe.ViaIR
