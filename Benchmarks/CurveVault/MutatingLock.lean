import Benchmarks.CurveVault.Lock
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a transient write preserves every persistent storage word.
theorem codeOwnerStorageWord_tstore (I : ExecutionEnv) (σ : AccountMap) (slot value readSlot : UInt256) :
    codeOwnerStorageWord I (tstoreAccountMap I.codeOwner σ slot value) readSlot =
      codeOwnerStorageWord I σ readSlot := by
  unfold codeOwnerStorageWord tstoreAccountMap
  cases h : σ.get? I.codeOwner with
  | none => simp only [Option.option, h]
  | some acc =>
      simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]
      split <;> rfl

-- LIBRARY CANDIDATE: storage preservation across an opaque static call in SourceState form.
theorem sourceStateStaticStorageRead {cfg : Config} {s0 I σ σ' evm evm'}
    {target : EVM.Address} {name : Ident} {args : List Value} {z : Bool} {out : ByteArray}
    (hs : SourceState s0 I σ evm) (hs' : SourceState s0 I σ' evm')
    (hcall : typedCallViaEVM fork cfg evm target name 0 args (z, evm', out) false) (slot : UInt256) :
    codeOwnerStorageWord I σ' slot = codeOwnerStorageWord I σ slot := by
  have h := typedCallViaEVM_static_storage_getD_of_accounts_eq slot ⟨0⟩ hs.accounts hcall
  simpa only [hs.env, hs'.env, ← hs'.accounts] using h

-- LIBRARY CANDIDATE: transient counterpart of RD.sstoreStatic.
theorem tstoreStaticReach {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {slot value : UInt256} {R : List UInt256}
    (h : RD fork code I g s0 pc (slot :: value :: R) mem aw rdata σ k C)
    (hperm : I.perm = false) (hdec : decode code pc = some (.TSTORE, .none))
    (hstack : R.length ≤ 1024) : RDstatic fork code g s0 := by
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, _, hk, hC, _, _, _, _, hee, _⟩
  · exact Or.inl hoog
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.TSTORE, .none) := by
      rw [hcode, hpc]; exact hdec
    have hperms : s.executionEnv.perm = false := by rw [hee]; exact hperm
    have st : Xstep fork (D_J code 0) s =
        (if s.machineState.gasAvailable.toNat < Ctstore then .error .OutOfGass
         else .error .StaticModeViolation) := by
      rw [← hcode, step_tstore s hd, hstk]
      have hov : ¬ ((slot :: value :: R).length - 2 + 0 > 1024) := by simp only [List.length_cons]; omega
      simp only [if_neg hov, hperms, Bool.false_eq_true, not_false_eq_true, if_true]
    rcases stepStatic (g := g) st hk hC with h | h
    · exact Or.inl (hX.trans h)
    · exact Or.inr (hX.trans h)

-- LIBRARY CANDIDATE: transient counterpart of SourceState.storageWrite.
theorem sourceStateTransientWrite {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot value : UInt256) :
    SourceState s0 I (tstoreAccountMap I.codeOwner σ slot value)
      (Stele.EVM.transientStore evm I.codeOwner slot value) := by
  refine ⟨(transientStore_σ₀ _ _ _ _).trans hs.world,
    (transientStore_executionEnv _ _ _ _).trans hs.env, ?_⟩
  rw [transientStore_accountMap, hs.accounts]

def vaultSetLock (evm : State) (value : UInt256) : State :=
  Stele.EVM.transientStore evm evm.executionEnv.codeOwner ⟨0⟩ value

abbrev vaultLockAssignStmt (value : UInt256) : Stmt :=
  .assign .transient {base := "nonreentrant_lock", steps := []} (.intLit (Int.ofNat value.toNat))

theorem vaultLockAssign (evm : State) (locals : Store) (value : UInt256) :
    assignStorageRef? config {contract := contract, locals := locals} evm .transient
      {base := "nonreentrant_lock", steps := []} (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals}, vaultSetLock evm value) := by
  apply assignStorageRef_transient_scalar
    (er := {base := "nonreentrant_lock", steps := []}) (loc := uint256Loc ⟨0⟩)
    (by simp [evalTransientStorageRef, evalTransientStorageRefSteps, EvalResult.bind, pure, bind])
    rfl rfl rfl (Or.inl ⟨_, rfl⟩)
  exact transientLocStore_uint256 _ _ _

theorem vaultLockSet (evm : State) (locals : Store) (value : UInt256)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config {contract := contract, locals := locals} evm (vaultLockAssignStmt value)
      (.ok {contract := contract, locals := locals} (vaultSetLock evm value)) :=
  ExecStmt.assign (hperm := Or.inr hperm) (by simp [evalExpr?, pure]) (vaultLockAssign evm locals value)

theorem vaultMutatingBodyStatic (evm : State) (locals : Store) (rest : List Stmt)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm locals
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: .require vaultLockExpr ::
        vaultLockAssignStmt ⟨1⟩ :: rest) .staticViolation :=
  ExecFuncBody.execBlockStatic <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock)) <|
        ExecBlock.consStatic (ExecStmt.assignTransientStatic (value := .int 1) (by simp [evalExpr?, pure]; rfl)
          (vaultLockAssign evm locals ⟨1⟩) hperm)

theorem vaultMutatingBodyReturns {evm calleeEvm : State} {locals calleeLocals : Store}
    {fn : FunctionDecl} {calleeStele : Frame} {args : List Expr} {argVals : List Value} {value : Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩)
    (hargs : evalExprs? config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) args = .ok argVals)
    (hlookup : lookupCallable? contract fn.name = some fn.toCallable)
    (hbind : bindParams? fn.params argVals = some calleeLocals)
    (hbody : ExecFuncBody fork config {contract := contract, locals := calleeLocals} (vaultSetLock evm ⟨1⟩) fn.body
      (.returned calleeStele calleeEvm (some [value])))
    (hperm : evm.executionEnv.perm = true)
    (hpermAfter : calleeEvm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm locals
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .require vaultLockExpr,
        vaultLockAssignStmt ⟨1⟩, .internalCall fn.name args "__r", vaultLockAssignStmt ⟨0⟩, .return [.var "__r"]]
      (.returned {contract := contract, locals := locals.insert "__r" value}
        (vaultSetLock calleeEvm ⟨0⟩) (some [value])) := by
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (retVar := "__r") hargs hlookup hbind hbody
  refine ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock)) <|
        ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := hperm) evm locals ⟨1⟩) <|
          ExecBlock.consNormal hcall <|
            ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := hpermAfter) calleeEvm (locals.insert "__r" value) ⟨0⟩) <|
              ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp [evalExpr?, EvalResult.ofOption]

theorem vaultMutatingBodyVoidReturns {evm calleeEvm : State} {locals calleeLocals : Store}
    {fn : FunctionDecl} {calleeStele : Frame} {args : List Expr} {argVals : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩)
    (hargs : evalExprs? config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) args = .ok argVals)
    (hlookup : lookupCallable? contract fn.name = some fn.toCallable)
    (hbind : bindParams? fn.params argVals = some calleeLocals)
    (hbody : ExecFuncBody fork config {contract := contract, locals := calleeLocals} (vaultSetLock evm ⟨1⟩) fn.body
      (.returned calleeStele calleeEvm none))
    (hperm : evm.executionEnv.perm = true)
    (hpermAfter : calleeEvm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm locals
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .require vaultLockExpr,
        vaultLockAssignStmt ⟨1⟩, .internalCall fn.name args "__r", vaultLockAssignStmt ⟨0⟩]
      (.returned {contract := contract, locals := locals.insert "__r" .unit}
        (vaultSetLock calleeEvm ⟨0⟩) none) := by
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (retVar := "__r") hargs hlookup hbind hbody
  exact ExecFuncBody.execBlockOK <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock)) <|
        ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := hperm) evm locals ⟨1⟩) <|
          ExecBlock.consNormal hcall <|
            ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := hpermAfter) calleeEvm (locals.insert "__r" .unit) ⟨0⟩) ExecBlock.nil

theorem vaultMutatingBodyReverts {evm : State} {locals calleeLocals : Store}
    {fn : FunctionDecl} {args : List Expr} {argVals : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩)
    (hargs : evalExprs? config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) args = .ok argVals)
    (hlookup : lookupCallable? contract fn.name = some fn.toCallable)
    (hbind : bindParams? fn.params argVals = some calleeLocals)
    (hbody : ExecFuncBody fork config {contract := contract, locals := calleeLocals} (vaultSetLock evm ⟨1⟩) fn.body .reverted)
    (rest : List Stmt := [vaultLockAssignStmt ⟨0⟩, .return [.var "__r"]])
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm locals
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: .require vaultLockExpr ::
        vaultLockAssignStmt ⟨1⟩ :: .internalCall fn.name args "__r" :: rest)
      .reverted :=
  ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock)) <|
        ExecBlock.consNormal (vaultLockSet (fork := fork) (hperm := hperm) evm locals ⟨1⟩) <|
          ExecBlock.consRevert (internalCallFunctionRevert hargs hlookup hbind hbody)

end Benchmarks.CurveVault
