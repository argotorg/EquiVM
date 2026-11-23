import Stele.Semantics.Dispatch
import Stele.Semantics.Eval
import Stele.Semantics.Calls

/-! Statement and transaction big-step semantics: `ExecStmt` through `steleExec`. -/

namespace Stele

open ABI

inductive ExecResult where
  /-- The returned-value component is `Option (List Value)`: `none` means the body fell through
      without executing `return`; `some vs` is an explicit `return` of the listed values (`some []`
      is an explicit void return). -/
  | returned : Frame -> EVM.State -> Option (List Value) -> ExecResult
  | ok : Frame -> EVM.State -> ExecResult
  | break : Frame -> EVM.State -> ExecResult
  | continue : Frame -> EVM.State -> ExecResult
  | reverted : ExecResult
  /-- No entry point accepts the message: selector, receive, and fallback dispatch all fail.
      Produced by `steleExec` before any function body runs. -/
  | noMatch : ExecResult
  /-- A selector selects an entry point, but the configured calldata decoder rejects its
      arguments. Produced by `steleExec` before the selected function body runs. -/
  | decodingFailed : ExecResult
  /-- Static-mode halt: a state-changing statement (storage write, event, value call, `new`) ran
      with `evm.executionEnv.perm = false`.  Mirrors the EVM's `StaticModeViolation` exception.
      Ordinary execution requires write permission for these operations, so a body halts at
      its first forbidden operation. Local assignments and zero-value calls remain available. -/
  | staticViolation : ExecResult

structure CallableDecl where
  params : List FunctionParam
  returnType : List StorageType := []
  body : Body
  deriving Repr, Inhabited

def bindParams? (params : List FunctionParam) (args : List Value) : Option Store :=
  match params, args with
  | [], [] => some ∅
  | p :: ps, v :: vs => do
      let rest <- bindParams? ps vs
      pure (rest.insert p.name v)
  | _, _ => none

def FunctionDecl.toCallable (decl : FunctionDecl) : CallableDecl :=
  { params := decl.params, returnType := decl.returnType, body := decl.body }

def TransitionDecl.toCallable (decl : TransitionDecl) : CallableDecl :=
  { params := decl.params.map Param.toFunctionParam
    returnType := decl.returnType.map StorageType.ofABI, body := decl.body }


def lookupFunction? (decls : List FunctionDecl) (name : Ident) : Option CallableDecl :=
  match decls with
  | [] => none
  | d :: ds =>
      if d.name = name then some d.toCallable else lookupFunction? ds name

def lookupTransition? (decls : List TransitionDecl) (name : Ident) : Option CallableDecl :=
  match decls with
  | [] => none
  | d :: ds =>
      if d.name = name then some d.toCallable else lookupTransition? ds name


def lookupCallable? (contract : ContractDecl) (name : Ident) : Option CallableDecl :=
  match lookupFunction? contract.functions name with
  | some decl => some decl
  | none => lookupTransition? contract.transitions name

/-- The declared type of the immutable `name`. -/
def immutableType? (contract : ContractDecl) (name : Ident) : Option ElemType :=
  (contract.immutables.find? (·.name == name)).map (·.ty)

/-- The immutables at the start of construction: every declared immutable at its zero value. -/
def initialImmutables (contract : ContractDecl) : Store :=
  contract.immutables.foldl (fun acc d => acc.insert d.name (elemDefaultValue d.ty)) ∅

theorem initialImmutables_noImmutables {contract : ContractDecl} (h : contract.immutables = []) :
    initialImmutables contract = ∅ := by
  simp [initialImmutables, h]

/-- CREATE2 salt: a `bytes32` value → its 32 salt bytes; anything else is invalid. -/
def saltBytes? : Value → Option ByteArray
  | .fixedBytes n bs => if n.val = 31 ∧ bs.length = 32 then some (ByteArray.mk bs.toArray) else none
  | _ => none

#guard saltBytes? (.fixedBytes ⟨31, by decide⟩ (List.replicate 32 0))
  = some (ByteArray.mk (Array.replicate 32 0))
#guard saltBytes? (.int 5) = none

/-- Collapse a callee's returned list into the single value bound to a call's result identifier.
    This `Value.tuple` is internal-call plumbing only — it is never ABI-encoded; the ABI boundary is
    transitions, which use the return list directly. -/
def collapseReturns : List Value → Value
  | []  => .unit
  | [v] => v
  | vs  => .tuple vs

def resumeAfterInternalCall (caller : Frame) (retVar : Ident) (value : Option (List Value)) :
    Frame :=
  let valueToWrite := match value with
    | none    => .unit
    | some vs => collapseReturns vs
  { caller with locals := caller.locals.insert retVar valueToWrite }

/-- Unqualified mutation targets prefer persistent declarations and local persistent aliases.
    Explicit `.transient` expressions and assignments do not consult local aliases. -/
@[simp] def usesTransientStorage (stele : Frame) (ref : StorageRef) : Bool :=
  !(stele.contract.storage.find? (fun decl ↦ decl.name == ref.base)).isSome &&
    stele.contract.transient.any (fun decl ↦ decl.name == ref.base) &&
    match stele.locals.get? ref.base with
    | some (.storageRef _ _) => false
    | _ => true

/-- A successfully resolved persistent reference keeps selecting the persistent backend. -/
theorem usesTransientStorage_of_resolveStorageRef
    (h : resolveStorageRef? cfg stele evm ref = .ok (er, ty)) :
    usesTransientStorage stele ref = false := by
  unfold resolveStorageRef? at h
  split at h
  · rename_i hlocal
    simp only [usesTransientStorage, hlocal, Bool.and_false]
  · cases hbase : stele.contract.storage.find? (fun decl ↦ decl.name == ref.base) with
    | some decl => simp [usesTransientStorage, hbase]
    | none =>
      unfold evalStorageRef at h
      cases hsteps : evalStorageRefSteps cfg stele evm ref.base [] ref.steps <;>
        simp [hsteps, storageTypeAt?, hbase, EvalResult.ofOption, EvalResult.bind, bind,
          pure] at h

/-- Grow a dynamic storage value through the selected backend. -/
def pushArray? (cfg : Config) (stele : Frame) (evm : EVM.State) (ref : StorageRef)
    (value : Option Value) : EvalResult EVM.State :=
  if usesTransientStorage stele ref then do
    let (er, ty) ← resolveTransientStorageRef? cfg stele evm ref
    let s' ← cfg.transientBackend.push er ty value (EVM.ownTransient evm)
    pure (EVM.setOwnTransient evm s')
  else do
    let (er, ty) ← resolveStorageRef? cfg stele evm ref
    let s' ← cfg.storageBackend.push er ty value (EVM.ownStorage evm)
    pure (EVM.setOwnStorage evm s')

def popArray? (cfg : Config) (stele : Frame) (evm : EVM.State) (ref : StorageRef) :
    EvalResult EVM.State :=
  if usesTransientStorage stele ref then do
    let (er, ty) ← resolveTransientStorageRef? cfg stele evm ref
    let s' ← cfg.transientBackend.pop er ty (EVM.ownTransient evm)
    pure (EVM.setOwnTransient evm s')
  else do
    let (er, ty) ← resolveStorageRef? cfg stele evm ref
    let s' ← cfg.storageBackend.pop er ty (EVM.ownStorage evm)
    pure (EVM.setOwnStorage evm s')

/-- `delete x`: reset the storage at `ref` through the configured backend. -/
def deleteStorage? (cfg : Config) (stele : Frame) (evm : EVM.State) (ref : StorageRef)
    : EvalResult EVM.State :=
  if usesTransientStorage stele ref then do
    let (er, ty) ← resolveTransientStorageRef? cfg stele evm ref
    let s' ← cfg.transientBackend.clear er ty (EVM.ownTransient evm)
    pure (EVM.setOwnTransient evm s')
  else do
    let (er, ty) ← resolveStorageRef? cfg stele evm ref
    let s' ← cfg.storageBackend.clear er ty (EVM.ownStorage evm)
    pure (EVM.setOwnStorage evm s')

/-- Evaluate a `new`'s optional salt: `none` ⇒ CREATE; `some e` must be a `bytes32` ⇒ CREATE2. -/
def evalSalt? (cfg : Config) (stele : Frame) (evm : EVM.State) :
    Option Expr → EvalResult (Option ByteArray)
  | none => .ok none
  | some e => do
      let v <- evalExpr? cfg stele evm e
      match saltBytes? v with
      | some b => .ok (some b)
      | none => .error .typeError

mutual

inductive ExecStmt (cfg : Config) :
    Frame -> EVM.State -> Stmt -> ExecResult -> Prop where
  | letDecl :
      evalExpr? cfg stele evm expr = .ok value ->
      ExecStmt cfg stele evm (.letDecl name ty expr)
        (.ok { stele with locals := stele.locals.insert name value } evm)
  | letDeclRevert :
      evalExpr? cfg stele evm expr = .revert ->
      ExecStmt cfg stele evm (.letDecl name ty expr) .reverted
  | letStorage :
      resolveStorageRef? cfg stele evm ref = .ok (er, ty) ->
      ExecStmt cfg stele evm (.letStorage name ref)
        (.ok { stele with locals := stele.locals.insert name (.storageRef er ty) } evm)
  | letStorageRevert :
      resolveStorageRef? cfg stele evm ref = .revert ->
      ExecStmt cfg stele evm (.letStorage name ref) .reverted
  /-- `gasleft()`: Stele tracks no gas, so any word `w` is a legal result.  A proof picks the `w`
      matching the EVM's actual gas at the corresponding `GAS` opcode. -/
  | letGas (w : EVM.Word) :
      ExecStmt cfg stele evm (.letGas name)
        (.ok { stele with locals := stele.locals.insert name (.int (Int.ofNat w.toNat)) } evm)
  | assign (hperm : origin = .localVar ∨ evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm expr = .ok value ->
      assignStorageRef? cfg stele evm origin slot value = .ok (stele', evm') ->
      ExecStmt cfg stele evm (.assign origin slot expr) (.ok stele' evm')
  | assignExprRevert :
      evalExpr? cfg stele evm expr = .revert ->
      ExecStmt cfg stele evm (.assign origin slot expr) .reverted
  | assignStoreRevert :
      evalExpr? cfg stele evm expr = .ok value ->
      assignStorageRef? cfg stele evm origin slot value = .revert ->
      ExecStmt cfg stele evm (.assign origin slot expr) .reverted
  /-- Static mode: a storage write that would otherwise succeed halts (`SSTORE` is forbidden). -/
  | assignStatic :
      evalExpr? cfg stele evm expr = .ok value ->
      assignStorageRef? cfg stele evm .storage slot value = .ok (stele', evm') ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.assign .storage slot expr) .staticViolation
  /-- `TSTORE` is forbidden in static mode, just like a persistent storage write. -/
  | assignTransientStatic :
      evalExpr? cfg stele evm expr = .ok value →
      assignStorageRef? cfg stele evm .transient slot value = .ok (stele', evm') →
      evm.executionEnv.perm = false →
      ExecStmt cfg stele evm (.assign .transient slot expr) .staticViolation
  | pushVal (hperm : evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm expr = .ok value ->
      pushArray? cfg stele evm ref (some value) = .ok evm' ->
      ExecStmt cfg stele evm (.push ref (some expr)) (.ok stele evm')
  | pushValExprRevert :
      evalExpr? cfg stele evm expr = .revert ->
      ExecStmt cfg stele evm (.push ref (some expr)) .reverted
  | pushValStoreRevert :
      evalExpr? cfg stele evm expr = .ok value ->
      pushArray? cfg stele evm ref (some value) = .revert ->
      ExecStmt cfg stele evm (.push ref (some expr)) .reverted
  | pushValStatic :
      evalExpr? cfg stele evm expr = .ok value ->
      pushArray? cfg stele evm ref (some value) = .ok evm' ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.push ref (some expr)) .staticViolation
  | pushGrow (hperm : evm.executionEnv.perm = true) :
      pushArray? cfg stele evm ref none = .ok evm' ->
      ExecStmt cfg stele evm (.push ref none) (.ok stele evm')
  | pushGrowRevert :
      pushArray? cfg stele evm ref none = .revert ->
      ExecStmt cfg stele evm (.push ref none) .reverted
  | pushGrowStatic :
      pushArray? cfg stele evm ref none = .ok evm' ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.push ref none) .staticViolation
  | pop (hperm : evm.executionEnv.perm = true) :
      popArray? cfg stele evm ref = .ok evm' ->
      ExecStmt cfg stele evm (.pop ref) (.ok stele evm')
  | popRevert :
      popArray? cfg stele evm ref = .revert ->
      ExecStmt cfg stele evm (.pop ref) .reverted
  | popStatic :
      popArray? cfg stele evm ref = .ok evm' ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.pop ref) .staticViolation
  | delete (hperm : evm.executionEnv.perm = true) :
      deleteStorage? cfg stele evm ref = .ok evm' ->
      ExecStmt cfg stele evm (.delete ref) (.ok stele evm')
  | deleteRevert :
      deleteStorage? cfg stele evm ref = .revert ->
      ExecStmt cfg stele evm (.delete ref) .reverted
  | deleteStatic :
      deleteStorage? cfg stele evm ref = .ok evm' ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.delete ref) .staticViolation
  | requireTrue {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecStmt cfg stele evm (.require condExpr) (.ok stele evm)
  | requireFalse {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool false) ->
      ExecStmt cfg stele evm (.require condExpr) .reverted
  | requireRevert {condExpr} :
      evalExpr? cfg stele evm condExpr = .revert ->
      ExecStmt cfg stele evm (.require condExpr) .reverted
  | whileFalse {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool false) ->
      ExecStmt cfg stele evm (.while condExpr body) (.ok stele evm)
  | whileCondRevert {condExpr} :
      evalExpr? cfg stele evm condExpr = .revert ->
      ExecStmt cfg stele evm (.while condExpr body) .reverted
  | whileTrue {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecBlock cfg stele evm body (.ok stele' evm') ->
      ExecStmt cfg stele' evm' (.while condExpr body) result ->
      ExecStmt cfg stele evm (.while condExpr body) result
  | whileReturn {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecBlock cfg stele evm body (.returned stele' evm' value) ->
      ExecStmt cfg stele evm (.while condExpr body) (.returned stele' evm' value)
  | whileRevert {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecBlock cfg stele evm body .reverted ->
      ExecStmt cfg stele evm (.while condExpr body) .reverted
  | whileBreak {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecBlock cfg stele evm body (.break stele' evm') ->
      ExecStmt cfg stele evm (.while condExpr body) (.ok stele' evm')
  | whileContinue {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecBlock cfg stele evm body (.continue stele' evm') ->
      ExecStmt cfg stele' evm' (.while condExpr body) result ->
      ExecStmt cfg stele evm (.while condExpr body) result
  | whileStatic {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecBlock cfg stele evm body .staticViolation ->
      ExecStmt cfg stele evm (.while condExpr body) .staticViolation
  /-- `for (init; cond; post) { body }`: run `init` once, then loop via `ExecForLoop`. -/
  | for :
      ExecBlock cfg stele evm init (.ok stele1 evm1) ->
      ExecForLoop cfg stele1 evm1 condExpr post body result ->
      ExecStmt cfg stele evm (.for init condExpr post body) result
  | forInitReturn :
      ExecBlock cfg stele evm init (.returned stele1 evm1 value) ->
      ExecStmt cfg stele evm (.for init condExpr post body) (.returned stele1 evm1 value)
  | forInitRevert :
      ExecBlock cfg stele evm init .reverted ->
      ExecStmt cfg stele evm (.for init condExpr post body) .reverted
  | forInitStatic :
      ExecBlock cfg stele evm init .staticViolation ->
      ExecStmt cfg stele evm (.for init condExpr post body) .staticViolation
  | iteTrue {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool true) ->
      ExecBlock cfg stele evm thenB result ->
      ExecStmt cfg stele evm (.ite condExpr thenB elseB) result
  | iteFalse {condExpr} :
      evalExpr? cfg stele evm condExpr = .ok (.bool false) ->
      ExecBlock cfg stele evm elseB result ->
      ExecStmt cfg stele evm (.ite condExpr thenB elseB) result
  | iteCondRevert {condExpr} :
      evalExpr? cfg stele evm condExpr = .revert ->
      ExecStmt cfg stele evm (.ite condExpr thenB elseB) .reverted
  | internalCallReturn :
      evalExprs? cfg stele evm args = .ok argVals ->
      lookupCallable? stele.contract name = some callee ->
      bindParams? callee.params argVals = some locals ->
      ExecFuncBody cfg { stele with locals := locals } evm callee.body
        (.returned calleeStele calleeEvm value) ->
      ExecStmt cfg stele evm (.internalCall name args retVar)
        (.ok (resumeAfterInternalCall stele retVar value) calleeEvm)
  | internalCallRevert :
      evalExprs? cfg stele evm args = .ok argVals ->
      lookupCallable? stele.contract name = some callee ->
      bindParams? callee.params argVals = some locals ->
      ExecFuncBody cfg { stele with locals := locals } evm callee.body .reverted ->
      ExecStmt cfg stele evm (.internalCall name args retVar) .reverted
  | internalCallArgsRevert :
      evalExprs? cfg stele evm args = .revert ->
      ExecStmt cfg stele evm (.internalCall name args retVar) .reverted
  | internalCallStatic :
      evalExprs? cfg stele evm args = .ok argVals ->
      lookupCallable? stele.contract name = some callee ->
      bindParams? callee.params argVals = some locals ->
      ExecFuncBody cfg { stele with locals := locals } evm callee.body .staticViolation ->
      ExecStmt cfg stele evm (.internalCall name args retVar) .staticViolation
  | externalCallSuccess (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = some value ->
      ExecStmt cfg stele evm (.externalCall receiver name eth args retVar (perm := perm))
        (.ok { stele with locals := stele.locals.insert retVar (collapseReturns value) } evm')
  | externalCallFailure (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (false, evm', out) perm ->
      ExecStmt cfg stele evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallReturnDecodeRevert
      (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      -- The sub-call *succeeds* (`z = true`) but the returned bytes do not ABI-decode to the
      -- expected return value (`decode? = none`).  The caller's solc-generated return decoder then
      -- reverts (`if slt(returndatasize, 32) { revert }`), so the whole statement reverts.
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = none ->
      ExecStmt cfg stele evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallReceiverRevert :
      evalExpr? cfg stele evm receiver = .revert ->
      ExecStmt cfg stele evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallSendRevert :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .revert ->
      ExecStmt cfg stele evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallArgsRevert :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .revert ->
      ExecStmt cfg stele evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  /-- Static mode: a `CALL` transferring value halts before the call is made. -/
  | externalCallStatic :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      EVM.wordOfInt sendVal ≠ ⟨0⟩ ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.externalCall receiver name eth args retVar (perm := perm))
        .staticViolation
  | lowLevelCallSuccess (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExpr? cfg stele evm cdata = .ok (.bytes calldata) ->
      callViaEVM evm (EVM.address target) sendVal calldata (true, evm', out) perm ->
      ExecStmt cfg stele evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm))
        (.ok { stele with locals := (stele.locals.insert okVar (.bool true)).insert dataVar (.bytes out) } evm')
  | lowLevelCallFailure (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExpr? cfg stele evm cdata = .ok (.bytes calldata) ->
      callViaEVM evm (EVM.address target) sendVal calldata (false, evm', out) perm ->
      ExecStmt cfg stele evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm))
        (.ok { stele with locals := (stele.locals.insert okVar (.bool false)).insert dataVar (.bytes out) } evm')
  | lowLevelCallReceiverRevert :
      evalExpr? cfg stele evm receiver = .revert ->
      ExecStmt cfg stele evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm)) .reverted
  | lowLevelCallSendRevert :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .revert ->
      ExecStmt cfg stele evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm)) .reverted
  | lowLevelCallDataRevert :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExpr? cfg stele evm cdata = .revert ->
      ExecStmt cfg stele evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm)) .reverted
  | lowLevelCallStatic :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExpr? cfg stele evm cdata = .ok (.bytes calldata) ->
      EVM.wordOfInt sendVal ≠ ⟨0⟩ ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm))
        .staticViolation
  | delegateCallSuccess :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm cdata = .ok (.bytes calldata) ->
      delegateCallViaEVM evm (EVM.address target) calldata (true, evm', out) ->
      ExecStmt cfg stele evm (.delegateCall receiver cdata okVar dataVar)
        (.ok
          { stele with
              locals := (stele.locals.insert okVar (.bool true)).insert dataVar (.bytes out) }
          evm')
  | delegateCallFailure :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm cdata = .ok (.bytes calldata) ->
      delegateCallViaEVM evm (EVM.address target) calldata (false, evm', out) ->
      ExecStmt cfg stele evm (.delegateCall receiver cdata okVar dataVar)
        (.ok
          { stele with
              locals := (stele.locals.insert okVar (.bool false)).insert dataVar (.bytes out) }
          evm')
  | delegateCallReceiverRevert :
      evalExpr? cfg stele evm receiver = .revert ->
      ExecStmt cfg stele evm (.delegateCall receiver cdata okVar dataVar) .reverted
  | delegateCallDataRevert :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm cdata = .revert ->
      ExecStmt cfg stele evm (.delegateCall receiver cdata okVar dataVar) .reverted
  | checkedCallSuccess (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = some value ->
      ExecBlock cfg { stele with locals := stele.locals.insert retVar (collapseReturns value) } evm' onSuccess result ->
      ExecStmt cfg stele evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) result
  | checkedCallFail (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      -- callee reverted: bind the raw returndata to `errVar` and run `onFail`.  The per-contract spec
      -- decides there (via `ite` on `errVar`) whether to recover or re-revert (`require false`).
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (false, evm', out) perm ->
      ExecBlock cfg { stele with locals := stele.locals.insert errVar (.bytes out) } evm' onFail result ->
      ExecStmt cfg stele evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) result
  | checkedCallReturnDecodeRevert
      (hperm : EVM.wordOfInt sendVal = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
      -- Call succeeds but returndata doesn't ABI-decode (`decode? = none`, e.g. codeless callee):
      -- solc's return decoder reverts *uncaught* (never enters `onFail`).  Cf. externalCall twin.
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = none ->
      ExecStmt cfg stele evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | checkedCallReceiverRevert :
      evalExpr? cfg stele evm receiver = .revert ->
      ExecStmt cfg stele evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | checkedCallSendRevert :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .revert ->
      ExecStmt cfg stele evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | checkedCallArgsRevert :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .revert ->
      ExecStmt cfg stele evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | checkedCallStatic :
      evalExpr? cfg stele evm receiver = .ok (.address target) ->
      evalExpr? cfg stele evm eth = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      EVM.wordOfInt sendVal ≠ ⟨0⟩ ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm))
        .staticViolation
  | newSuccess (hperm : evm.executionEnv.perm = true) :
      evalExpr? cfg stele evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      evalSalt? cfg stele evm salt = .ok saltBytes ->
      newViaEVM cfg evm name sendVal argVals saltBytes (addr, evm', true) ->
      ExecStmt cfg stele evm (.new name valExpr args retVar salt)
        (.ok { stele with locals := stele.locals.insert retVar (.address addr) } evm')
  | newRevert (hperm : evm.executionEnv.perm = true) :
      -- A failed creation reverts the caller, unlike a low-level external call.
      evalExpr? cfg stele evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      evalSalt? cfg stele evm salt = .ok saltBytes ->
      newViaEVM cfg evm name sendVal argVals saltBytes (addr, evm', false) ->
      ExecStmt cfg stele evm (.new name valExpr args retVar salt) .reverted
  | newValueRevert :
      evalExpr? cfg stele evm valExpr = .revert ->
      ExecStmt cfg stele evm (.new name valExpr args retVar salt) .reverted
  | newArgsRevert :
      evalExpr? cfg stele evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .revert ->
      ExecStmt cfg stele evm (.new name valExpr args retVar salt) .reverted
  /-- Static mode: `CREATE`/`CREATE2` is forbidden regardless of value. -/
  | newStatic :
      evalExpr? cfg stele evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg stele evm args = .ok argVals ->
      evalSalt? cfg stele evm salt = .ok saltBytes ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.new name valExpr args retVar salt) .staticViolation
  | return :
      evalExprs? cfg stele evm exprs = .ok values ->
      ExecStmt cfg stele evm (.return exprs) (.returned stele evm (some values))
  | returnRevert :
      evalExprs? cfg stele evm exprs = .revert ->
      ExecStmt cfg stele evm (.return exprs) .reverted
  /-- `name = e;` for a declared immutable: the value must have the declared type.  Solidity only
      accepts this in the constructor, where `steleCtorExec` keeps the final values. -/
  | setImmutable :
      evalExpr? cfg stele evm expr = .ok value ->
      immutableType? stele.contract name = some ty ->
      elemValueFits ty value = true ->
      ExecStmt cfg stele evm (.setImmutable name expr)
        (.ok { stele with immutables := stele.immutables.insert name value } evm)
  | setImmutableRevert :
      evalExpr? cfg stele evm expr = .revert ->
      ExecStmt cfg stele evm (.setImmutable name expr) .reverted
  | break :
      ExecStmt cfg stele evm .break (.break stele evm)
  | continue :
      ExecStmt cfg stele evm .continue (.continue stele evm)
  /-- `emit`: the arguments are evaluated; the log is not modelled. -/
  | emit (hperm : evm.executionEnv.perm = true) :
      evalExprs? cfg stele evm args = .ok vals ->
      ExecStmt cfg stele evm (.emit name args) (.ok stele evm)
  | emitArgsRevert :
      evalExprs? cfg stele evm args = .revert ->
      ExecStmt cfg stele evm (.emit name args) .reverted
  /-- Static mode: `LOG*` is forbidden. -/
  | emitStatic :
      evalExprs? cfg stele evm args = .ok vals ->
      evm.executionEnv.perm = false ->
      ExecStmt cfg stele evm (.emit name args) .staticViolation

/-- The loop part of a `for (init; cond; post) { body }`, after `init` has run.  Each iteration
    checks `cond`; on `true` it runs `body` then `post` and loops.  A `break` in `body` exits the
    loop with `.ok` (skipping `post`); a `continue` runs `post` and loops; `return`/`revert`
    propagate.  `post` may only fall through (`.ok`) or revert. -/
inductive ExecForLoop (cfg : Config) :
    Frame -> EVM.State -> Expr /- cond -/ -> List Stmt /- post -/ -> List Stmt /- body -/ ->
    ExecResult -> Prop where
  | falseDone {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool false) ->
      ExecForLoop cfg stele evm condExpr post body (.ok stele evm)
  | condRevert {condExpr} :
      evalExpr? cfg stele evm condExpr =.revert ->
      ExecForLoop cfg stele evm condExpr post body .reverted
  | bodyReturn {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.returned stele' evm' value) ->
      ExecForLoop cfg stele evm condExpr post body (.returned stele' evm' value)
  | bodyRevert {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body .reverted ->
      ExecForLoop cfg stele evm condExpr post body .reverted
  | bodyBreak {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.break stele' evm') ->
      ExecForLoop cfg stele evm condExpr post body (.ok stele' evm')
  | iterate {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.ok stele1 evm1) ->
      ExecBlock cfg stele1 evm1 post (.ok stele2 evm2) ->
      ExecForLoop cfg stele2 evm2 condExpr post body result ->
      ExecForLoop cfg stele evm condExpr post body result
  | iteratePostRevert {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.ok stele1 evm1) ->
      ExecBlock cfg stele1 evm1 post .reverted ->
      ExecForLoop cfg stele evm condExpr post body .reverted
  | continueIter {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.continue stele1 evm1) ->
      ExecBlock cfg stele1 evm1 post (.ok stele2 evm2) ->
      ExecForLoop cfg stele2 evm2 condExpr post body result ->
      ExecForLoop cfg stele evm condExpr post body result
  | continuePostRevert {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.continue stele1 evm1) ->
      ExecBlock cfg stele1 evm1 post .reverted ->
      ExecForLoop cfg stele evm condExpr post body .reverted
  | bodyStatic {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body .staticViolation ->
      ExecForLoop cfg stele evm condExpr post body .staticViolation
  | iteratePostStatic {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.ok stele1 evm1) ->
      ExecBlock cfg stele1 evm1 post .staticViolation ->
      ExecForLoop cfg stele evm condExpr post body .staticViolation
  | continuePostStatic {condExpr} :
      evalExpr? cfg stele evm condExpr =.ok (.bool true) ->
      ExecBlock cfg stele evm body (.continue stele1 evm1) ->
      ExecBlock cfg stele1 evm1 post .staticViolation ->
      ExecForLoop cfg stele evm condExpr post body .staticViolation

inductive ExecBlock (cfg : Config) :
    Frame -> EVM.State -> List Stmt -> ExecResult -> Prop where
  | nil :
      ExecBlock cfg stele evm [] (.ok stele evm)
  | consNormal :
      ExecStmt cfg stele evm stmt (.ok stele' evm') ->
      ExecBlock cfg stele' evm' stmts result ->
      ExecBlock cfg stele evm (stmt :: stmts) result
  | consReturn :
      ExecStmt cfg stele evm stmt (.returned stele' evm' value) ->
      ExecBlock cfg stele evm (stmt :: stmts) (.returned stele' evm' value)
  | consRevert :
      ExecStmt cfg stele evm stmt .reverted ->
      ExecBlock cfg stele evm (stmt :: stmts) .reverted
  | consBreak :
      ExecStmt cfg stele evm stmt (.break stele' evm') ->
      ExecBlock cfg stele evm (stmt :: stmts) (.break stele' evm')
  | consContinue :
      ExecStmt cfg stele evm stmt (.continue stele' evm') ->
      ExecBlock cfg stele evm (stmt :: stmts) (.continue stele' evm')
  | consStatic :
      ExecStmt cfg stele evm stmt .staticViolation ->
      ExecBlock cfg stele evm (stmt :: stmts) .staticViolation

inductive ExecFuncBody (cfg : Config) :
    Frame -> EVM.State -> List Stmt -> ExecResult -> Prop where
  | execBlockOK :
      ExecBlock cfg stele evm body (.ok stele' evm') ->
      ExecFuncBody cfg stele evm body (.returned stele' evm' none)
  | execBlockRet :
      ExecBlock cfg stele evm body (.returned stele' evm' value) ->
      ExecFuncBody cfg stele evm body (.returned stele' evm' value)
  | execBlockRevert :
      ExecBlock cfg stele evm body .reverted ->
      ExecFuncBody cfg stele evm body .reverted
  /-- A `break`/`continue` that occurs outside a loop is malformed. We have to handle it so that
      `ExecFuncBody` is never stuck. -/
  | execBlockBreak :
      ExecBlock cfg stele evm body (.break stele' evm') ->
      ExecFuncBody cfg stele evm body (.returned stele' evm' none)
  | execBlockContinue :
      ExecBlock cfg stele evm body (.continue stele' evm') ->
      ExecFuncBody cfg stele evm body (.returned stele' evm' none)
  | execBlockStatic :
      ExecBlock cfg stele evm body .staticViolation ->
      ExecFuncBody cfg stele evm body .staticViolation

end

/-- Dispatch and calldata-decoding failures cannot arise while executing a statement. -/
theorem ExecStmt.not_dispatchFailure {cfg : Config} {stele : Frame} {evm : EVM.State}
    {stmt : Stmt} {r : ExecResult} (h : ExecStmt cfg stele evm stmt r) :
    r ≠ .noMatch ∧ r ≠ .decodingFailed := by
  induction h using ExecStmt.rec
    (motive_2 := fun _ _ _ _ _ r _ => r ≠ .noMatch ∧ r ≠ .decodingFailed)
    (motive_3 := fun _ _ _ r _ => r ≠ .noMatch ∧ r ≠ .decodingFailed)
    (motive_4 := fun _ _ _ r _ => r ≠ .noMatch ∧ r ≠ .decodingFailed)
  all_goals simp_all

/-- A block propagates body outcomes only; dispatch failures happen before its execution. -/
theorem ExecBlock.not_dispatchFailure {cfg : Config} {stele : Frame} {evm : EVM.State}
    {body : List Stmt} {r : ExecResult} (h : ExecBlock cfg stele evm body r) :
    r ≠ .noMatch ∧ r ≠ .decodingFailed := by
  induction body generalizing stele evm with
  | nil => cases h; simp
  | cons stmt rest ih =>
      cases h with
      | consNormal _ hrest => exact ih hrest
      | _ => simp

/-- Run a transition (or constructor) body from a fresh frame with the given locals and
    immutables. -/
def ExecTransitionBody (cfg : Config) (contract : ContractDecl) (evm : EVM.State)
    (locals : Store) (body : Body) (result : ExecResult) (immutables : Store := ∅) : Prop :=
  ExecFuncBody cfg { contract := contract, locals := locals, immutables := immutables } evm body
    result

/-- Stele transaction dispatch and execution, with `immutables` the values the deployed contract
    was constructed with. Dispatch and calldata-decoding failures are execution results, without
    running a body. A missing entry point uses the empty ABI return convention; a decoding failure
    retains the selected transition's return convention. -/
inductive steleExec
    (conf : Config)
    (contract : ContractDecl) /- Spec -/
    (immutables : Store)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
: ExecResult -> ReturnConvention -> Prop where
  | noMatch :
    dispatchMsg contract I.calldata = .none →
    steleExec conf contract immutables σ σ₀ g A I .noMatch (.abi [])
  | decodingFailed :
    selectorDispatchMsg contract I.calldata = .some transition →
    conf.externalABI.decodeCalldata? (transition.params.map Param.name)
      (transitionSignature transition).paramTypes I.calldata = .none →
    steleExec conf contract immutables σ σ₀ g A I .decodingFailed
      (.abi transition.returnType)
  | intro :
    /- Stele selector transition dispatch. -/
    selectorDispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    conf.externalABI.decodeCalldata? (transition.params.map Param.name)
      transitionSig.paramTypes I.calldata = .some callargs →
    evmState =
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          machineState.gasAvailable := .ofUInt256 g
      } →
    ExecTransitionBody conf contract evmState callargs transition.body steleRes immutables →
    steleExec conf contract immutables σ σ₀ g A I steleRes
      (.abi transition.returnType)
  | fallback :
    /- Solidity fallback dispatch has no selector or ABI argument decoding. -/
    selectorDispatchMsg contract I.calldata = .none →
    receiveDispatchMsg contract I.calldata = .none →
    contract.fallback = .some transition →
    fallbackCallargs I.calldata transition.params = some callargs →
    fallbackReturnConvention transition = some returnConvention →
    evmState =
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          machineState.gasAvailable := .ofUInt256 g
      } →
    ExecTransitionBody conf contract evmState callargs transition.body steleRes immutables →
    steleExec conf contract immutables σ σ₀ g A I steleRes
      returnConvention
  | receive :
    /- Solidity receive dispatch has no selector or ABI argument decoding. -/
    receiveDispatchMsg contract I.calldata = .some transition →
    transition.params = [] →
    transition.returnType = [] →
    evmState =
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          machineState.gasAvailable := .ofUInt256 g
      } →
    ExecTransitionBody conf contract evmState ∅ transition.body steleRes immutables →
    steleExec conf contract immutables σ σ₀ g A I steleRes (.abi [])

/-- Stele constructor execution.  The body starts from the zero immutables; the final frame of a
    `.returned` result holds the immutables the deployed code embeds. -/
inductive steleCtorExec
    (conf : Config)
    (contract : ContractDecl) /- Spec -/
    (args : List Value)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (steleRes : ExecResult)
: Prop where
  | intro :
    evmState =
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          machineState.gasAvailable := .ofUInt256 g
      } →
    -- This may be redundant when `cfg.selfDeployment` already enforces valid constructor ABI
    -- encoding, but it keeps the parameter store from relying on `List.zip` truncation.
    args.length = contract.ctor.params.length →
    argsStore = Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args) →
    ExecTransitionBody conf contract evmState argsStore contract.ctor.body steleRes
      (initialImmutables contract) →
    steleCtorExec conf contract args σ σ₀ g A I steleRes

end Stele
