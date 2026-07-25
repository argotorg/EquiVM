import Solm.Semantics.Dispatch
import Solm.Semantics.Eval
import Solm.Semantics.Calls

/-! Statement and transaction big-step semantics: `ExecStmt` through `solmExec`. -/

namespace Solm

open ABI

inductive ExecResult where
  /- The returned-value component is `Option (List Value)`: `none` means the body fell through
     without executing `return`; `some vs` is an explicit `return` of the listed values (`some []`
     is an explicit void return). -/
  | returned : Frame -> EVM.State -> Option (List Value) -> ExecResult
  | ok : Frame -> EVM.State -> ExecResult
  | break : Frame -> EVM.State -> ExecResult
  | continue : Frame -> EVM.State -> ExecResult
  | reverted : ExecResult

structure CallableDecl where
  params : List Param
  returnType : List ABIType := []
  body : Body
  deriving Repr, Inhabited

def bindParams? (params : List Param) (args : List Value) : Option Store :=
  match params, args with
  | [], [] => some ∅
  | p :: ps, v :: vs => do
      let rest <- bindParams? ps vs
      pure (rest.insert p.name v)
  | _, _ => none

def FunctionDecl.toCallable (decl : FunctionDecl) : CallableDecl :=
  { params := decl.params, returnType := decl.returnType, body := decl.body }

def TransitionDecl.toCallable (decl : TransitionDecl) : CallableDecl :=
  { params := decl.params, returnType := decl.returnType, body := decl.body }


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

-- CREATE2 salt: a `bytes32` value → its 32 salt bytes; anything else is invalid.
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

/-- `arr.push(v?)`: grow the dynamic array named by `ref` by one.  Reads the current length `L`
    (the layout's `.length` query), stores length `L+1`, then `some v` writes the value at element
    `L` via `writeStorage?`.  Writing the length first mirrors solc's generated storage order and
    also makes the new index in-bounds for the ordinary storage writer.  `none` is a grow-only push
    (the new slots are already zero by storage default).  `.revert`s only if evaluating the array ref
    does.  It `.error`s (a stuck, ill-formed program) when the target isn't a dynamic array, the
    layout has no `.length`/element slot for it, the length slot doesn't hold an integer, or a
    compound value's shape doesn't match the element type — i.e. for a well-formed layout + matching
    value, `.revert` is the only non-`.ok` outcome. -/
def pushArray? (cfg : Config) (solm : Frame) (evm : EVM.State) (ref : StorageRef)
    (value : Option Value) : EvalResult EVM.State := do
  let (er, ty) <- resolveStorageRef? cfg solm evm ref
  match ty with
  | .dynamicArray elemTy => do
      let lenLoc <- EvalResult.ofOption .storageError
        (cfg.storage.layout { er with steps := er.steps ++ [.length] } evm)
      match storageLocLoad evm lenLoc with
      | .int len => do
          let evmLen <- EvalResult.ofOption .storageError (storageLocStore evm lenLoc (.int (len + 1)))
          match value with
            | some v =>
                writeStorage? cfg evmLen
                  { er with steps := er.steps ++ [.aindex (.int len)] } elemTy v
            | none => pure evmLen
      | _ => .error .storageError
  -- `bytes`/`string` push: read-modify-write the whole value through the layout hooks (they handle
  -- short↔long transitions).  Arg-less appends a zero byte; else a `bytes1` (`fixedBytes ⟨0,_⟩`).
  | .bytes | .string => do
      match (← readStorage? cfg evm er ty) with
      | .bytes ba =>
          match value with
          | none => writeStorage? cfg evm er ty (.bytes (ba.push 0))
          | some (.fixedBytes n bs) =>
              if n.val = 0 ∧ bs.length = 1 then
                writeStorage? cfg evm er ty (.bytes (ba ++ ByteArray.mk bs.toArray))
              else .error .typeError
          | some _ => .error .typeError
      | _ => .error .storageError
  | _ => .error .storageError

/-- `arr.pop()`: remove the last element of the dynamic array named by `ref`.  Reverts when the
    array is empty (solc's `Panic(0x31)`).  Otherwise recursively clears the whole last element
    (per its declared type, via `clearStorage?` — so nested arrays/structs are fully zeroed) and
    sets the length to `L-1`. -/
def popArray? (cfg : Config) (solm : Frame) (evm : EVM.State) (ref : StorageRef)
    : EvalResult EVM.State := do
  let (er, ty) <- resolveStorageRef? cfg solm evm ref
  match ty with
  | .dynamicArray elemTy => do
      let lenLoc <- EvalResult.ofOption .storageError
        (cfg.storage.layout { er with steps := er.steps ++ [.length] } evm)
      match storageLocLoad evm lenLoc with
      | .int len =>
          if len ≤ 0 then .revert
          else do
            let evm1 <- clearStorage? cfg evm
              { er with steps := er.steps ++ [.aindex (.int (len - 1))] } elemTy
            EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int (len - 1)))
      | _ => .error .storageError
  -- `bytes`/`string` pop: read-modify-write; empty → revert (solc `Panic(0x31)`).
  | .bytes | .string => do
      match (← readStorage? cfg evm er ty) with
      | .bytes ba =>
          if ba.size = 0 then .revert
          else writeStorage? cfg evm er ty (.bytes (ba.extract 0 (ba.size - 1)))
      | _ => .error .storageError
  | _ => .error .storageError

/-- `delete x`: reset the storage at `ref` to its zero value, recursively per its declared type
    (`clearStorage?` — a dynamic array becomes empty, a struct/array is fully zeroed).  `.revert`s
    only if evaluating the ref does; `.error`s on an ill-formed layout/type. -/
def deleteStorage? (cfg : Config) (solm : Frame) (evm : EVM.State) (ref : StorageRef)
    : EvalResult EVM.State := do
  let (er, ty) <- resolveStorageRef? cfg solm evm ref
  clearStorage? cfg evm er ty

-- Evaluate a `new`'s optional salt: `none` ⇒ CREATE; `some e` must be a `bytes32` ⇒ CREATE2.
def evalSalt? (cfg : Config) (solm : Frame) (evm : EVM.State) :
    Option Expr → EvalResult (Option ByteArray)
  | none => .ok none
  | some e => do
      let v <- evalExpr? cfg solm evm e
      match saltBytes? v with
      | some b => .ok (some b)
      | none => .error .typeError

mutual

inductive ExecStmt (cfg : Config) :
    Frame -> EVM.State -> Stmt -> ExecResult -> Prop where
  | letDecl :
      evalExpr? cfg solm evm expr = .ok value ->
      ExecStmt cfg solm evm (.letDecl name ty expr)
        (.ok { solm with locals := solm.locals.insert name value } evm)
  | letDeclRevert :
      evalExpr? cfg solm evm expr = .revert ->
      ExecStmt cfg solm evm (.letDecl name ty expr) .reverted
  | letStorage :
      resolveStorageRef? cfg solm evm ref = .ok (er, ty) ->
      ExecStmt cfg solm evm (.letStorage name ref)
        (.ok { solm with locals := solm.locals.insert name (.storageRef er ty) } evm)
  | letStorageRevert :
      resolveStorageRef? cfg solm evm ref = .revert ->
      ExecStmt cfg solm evm (.letStorage name ref) .reverted
  -- `gasleft()`: Solm tracks no gas, so any word `w` is a legal result.  A proof picks the `w`
  -- matching the EVM's actual gas at the corresponding `GAS` opcode.
  | letGas (w : EVM.Word) :
      ExecStmt cfg solm evm (.letGas name)
        (.ok { solm with locals := solm.locals.insert name (.int (Int.ofNat w.toNat)) } evm)
  | assign :
      evalExpr? cfg solm evm expr = .ok value ->
      assignStorageRef? cfg solm evm origin slot value = .ok (solm', evm') ->
      ExecStmt cfg solm evm (.assign origin slot expr) (.ok solm' evm')
  | assignExprRevert :
      evalExpr? cfg solm evm expr = .revert ->
      ExecStmt cfg solm evm (.assign origin slot expr) .reverted
  | assignStoreRevert :
      evalExpr? cfg solm evm expr = .ok value ->
      assignStorageRef? cfg solm evm origin slot value = .revert ->
      ExecStmt cfg solm evm (.assign origin slot expr) .reverted
  | pushVal :
      evalExpr? cfg solm evm expr = .ok value ->
      pushArray? cfg solm evm ref (some value) = .ok evm' ->
      ExecStmt cfg solm evm (.push ref (some expr)) (.ok solm evm')
  | pushValExprRevert :
      evalExpr? cfg solm evm expr = .revert ->
      ExecStmt cfg solm evm (.push ref (some expr)) .reverted
  | pushValStoreRevert :
      evalExpr? cfg solm evm expr = .ok value ->
      pushArray? cfg solm evm ref (some value) = .revert ->
      ExecStmt cfg solm evm (.push ref (some expr)) .reverted
  | pushGrow :
      pushArray? cfg solm evm ref none = .ok evm' ->
      ExecStmt cfg solm evm (.push ref none) (.ok solm evm')
  | pushGrowRevert :
      pushArray? cfg solm evm ref none = .revert ->
      ExecStmt cfg solm evm (.push ref none) .reverted
  | pop :
      popArray? cfg solm evm ref = .ok evm' ->
      ExecStmt cfg solm evm (.pop ref) (.ok solm evm')
  | popRevert :
      popArray? cfg solm evm ref = .revert ->
      ExecStmt cfg solm evm (.pop ref) .reverted
  | delete :
      deleteStorage? cfg solm evm ref = .ok evm' ->
      ExecStmt cfg solm evm (.delete ref) (.ok solm evm')
  | deleteRevert :
      deleteStorage? cfg solm evm ref = .revert ->
      ExecStmt cfg solm evm (.delete ref) .reverted
  | requireTrue {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool true) ->
      ExecStmt cfg solm evm (.require condExpr) (.ok solm evm)
  | requireFalse {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool false) ->
      ExecStmt cfg solm evm (.require condExpr) .reverted
  | requireRevert {condExpr} :
      evalExpr? cfg solm evm condExpr = .revert ->
      ExecStmt cfg solm evm (.require condExpr) .reverted
  | whileFalse {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool false) ->
      ExecStmt cfg solm evm (.while condExpr body) (.ok solm evm)
  | whileCondRevert {condExpr} :
      evalExpr? cfg solm evm condExpr = .revert ->
      ExecStmt cfg solm evm (.while condExpr body) .reverted
  | whileTrue {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool true) ->
      ExecBlock cfg solm evm body (.ok solm' evm') ->
      ExecStmt cfg solm' evm' (.while condExpr body) result ->
      ExecStmt cfg solm evm (.while condExpr body) result
  | whileReturn {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool true) ->
      ExecBlock cfg solm evm body (.returned solm' evm' value) ->
      ExecStmt cfg solm evm (.while condExpr body) (.returned solm' evm' value)
  | whileRevert {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool true) ->
      ExecBlock cfg solm evm body .reverted ->
      ExecStmt cfg solm evm (.while condExpr body) .reverted
  | whileBreak {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool true) ->
      ExecBlock cfg solm evm body (.break solm' evm') ->
      ExecStmt cfg solm evm (.while condExpr body) (.ok solm' evm')
  | whileContinue {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool true) ->
      ExecBlock cfg solm evm body (.continue solm' evm') ->
      ExecStmt cfg solm' evm' (.while condExpr body) result ->
      ExecStmt cfg solm evm (.while condExpr body) result
  -- `for (init; cond; post) { body }`: run `init` once, then loop via `ExecForLoop`.
  | for :
      ExecBlock cfg solm evm init (.ok solm1 evm1) ->
      ExecForLoop cfg solm1 evm1 condExpr post body result ->
      ExecStmt cfg solm evm (.for init condExpr post body) result
  | forInitReturn :
      ExecBlock cfg solm evm init (.returned solm1 evm1 value) ->
      ExecStmt cfg solm evm (.for init condExpr post body) (.returned solm1 evm1 value)
  | forInitRevert :
      ExecBlock cfg solm evm init .reverted ->
      ExecStmt cfg solm evm (.for init condExpr post body) .reverted
  | iteTrue {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool true) ->
      ExecBlock cfg solm evm thenB result ->
      ExecStmt cfg solm evm (.ite condExpr thenB elseB) result
  | iteFalse {condExpr} :
      evalExpr? cfg solm evm condExpr = .ok (.bool false) ->
      ExecBlock cfg solm evm elseB result ->
      ExecStmt cfg solm evm (.ite condExpr thenB elseB) result
  | iteCondRevert {condExpr} :
      evalExpr? cfg solm evm condExpr = .revert ->
      ExecStmt cfg solm evm (.ite condExpr thenB elseB) .reverted
  | internalCallReturn :
      evalExprs? cfg solm evm args = .ok argVals ->
      lookupCallable? solm.contract name = some callee ->
      bindParams? callee.params argVals = some locals ->
      ExecFuncBody cfg { solm with locals := locals } evm callee.body
        (.returned calleeSolm calleeEvm value) ->
      ExecStmt cfg solm evm (.internalCall name args retVar)
        (.ok (resumeAfterInternalCall solm retVar value) calleeEvm)
  | internalCallRevert :
      evalExprs? cfg solm evm args = .ok argVals ->
      lookupCallable? solm.contract name = some callee ->
      bindParams? callee.params argVals = some locals ->
      ExecFuncBody cfg { solm with locals := locals } evm callee.body .reverted ->
      ExecStmt cfg solm evm (.internalCall name args retVar) .reverted
  | internalCallArgsRevert :
      evalExprs? cfg solm evm args = .revert ->
      ExecStmt cfg solm evm (.internalCall name args retVar) .reverted
  | externalCallSuccess :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = some value ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar (perm := perm))
        (.ok { solm with locals := solm.locals.insert retVar (collapseReturns value) } evm')
  | externalCallFailure :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (false, evm', out) perm ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallReturnDecodeRevert :
      -- The sub-call *succeeds* (`z = true`) but the returned bytes do not ABI-decode to the
      -- expected return value (`decode? = none`).  The caller's solc-generated return decoder then
      -- reverts (`if slt(returndatasize, 32) { revert }`), so the whole statement reverts.
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = none ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallReceiverRevert :
      evalExpr? cfg solm evm receiver = .revert ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallSendRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .revert ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | externalCallArgsRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .revert ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar (perm := perm)) .reverted
  | lowLevelCallSuccess :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExpr? cfg solm evm cdata = .ok (.bytes calldata) ->
      callViaEVM evm (EVM.address target) sendVal calldata (true, evm', out) perm ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm))
        (.ok { solm with locals := (solm.locals.insert okVar (.bool true)).insert dataVar (.bytes out) } evm')
  | lowLevelCallFailure :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExpr? cfg solm evm cdata = .ok (.bytes calldata) ->
      callViaEVM evm (EVM.address target) sendVal calldata (false, evm', out) perm ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm))
        (.ok { solm with locals := (solm.locals.insert okVar (.bool false)).insert dataVar (.bytes out) } evm')
  | lowLevelCallReceiverRevert :
      evalExpr? cfg solm evm receiver = .revert ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm)) .reverted
  | lowLevelCallSendRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .revert ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm)) .reverted
  | lowLevelCallDataRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExpr? cfg solm evm cdata = .revert ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar (perm := perm)) .reverted
  | delegateCallSuccess :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm cdata = .ok (.bytes calldata) ->
      delegateCallViaEVM evm (EVM.address target) calldata (true, evm', out) ->
      ExecStmt cfg solm evm (.delegateCall receiver cdata okVar dataVar)
        (.ok
          { solm with
              locals := (solm.locals.insert okVar (.bool true)).insert dataVar (.bytes out) }
          evm')
  | delegateCallFailure :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm cdata = .ok (.bytes calldata) ->
      delegateCallViaEVM evm (EVM.address target) calldata (false, evm', out) ->
      ExecStmt cfg solm evm (.delegateCall receiver cdata okVar dataVar)
        (.ok
          { solm with
              locals := (solm.locals.insert okVar (.bool false)).insert dataVar (.bytes out) }
          evm')
  | delegateCallReceiverRevert :
      evalExpr? cfg solm evm receiver = .revert ->
      ExecStmt cfg solm evm (.delegateCall receiver cdata okVar dataVar) .reverted
  | delegateCallDataRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm cdata = .revert ->
      ExecStmt cfg solm evm (.delegateCall receiver cdata okVar dataVar) .reverted
  | checkedCallSuccess :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = some value ->
      ExecBlock cfg { solm with locals := solm.locals.insert retVar (collapseReturns value) } evm' onSuccess result ->
      ExecStmt cfg solm evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) result
  | checkedCallFail :
      -- callee reverted: bind the raw returndata to `errVar` and run `onFail`.  The per-contract spec
      -- decides there (via `ite` on `errVar`) whether to recover or re-revert (`require false`).
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (false, evm', out) perm ->
      ExecBlock cfg { solm with locals := solm.locals.insert errVar (.bytes out) } evm' onFail result ->
      ExecStmt cfg solm evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) result
  | checkedCallReturnDecodeRevert :
      -- Call succeeds but returndata doesn't ABI-decode (`decode? = none`, e.g. codeless callee):
      -- solc's return decoder reverts *uncaught* (never enters `onFail`).  Cf. externalCall twin.
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm ->
      cfg.externalABI.decode? name out = none ->
      ExecStmt cfg solm evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | checkedCallReceiverRevert :
      evalExpr? cfg solm evm receiver = .revert ->
      ExecStmt cfg solm evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | checkedCallSendRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .revert ->
      ExecStmt cfg solm evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | checkedCallArgsRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .revert ->
      ExecStmt cfg solm evm
        (.checkedCall receiver name eth args retVar onSuccess errVar onFail (perm := perm)) .reverted
  | newSuccess :
      evalExpr? cfg solm evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      evalSalt? cfg solm evm salt = .ok saltBytes ->
      newViaEVM cfg evm name sendVal argVals saltBytes (addr, evm', true) ->
      ExecStmt cfg solm evm (.new name valExpr args retVar salt)
        (.ok { solm with locals := solm.locals.insert retVar (.address addr) } evm')
  | newRevert :
      -- A failed creation reverts the caller, unlike a low-level external call.
      evalExpr? cfg solm evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      evalSalt? cfg solm evm salt = .ok saltBytes ->
      newViaEVM cfg evm name sendVal argVals saltBytes (addr, evm', false) ->
      ExecStmt cfg solm evm (.new name valExpr args retVar salt) .reverted
  | newValueRevert :
      evalExpr? cfg solm evm valExpr = .revert ->
      ExecStmt cfg solm evm (.new name valExpr args retVar salt) .reverted
  | newArgsRevert :
      evalExpr? cfg solm evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .revert ->
      ExecStmt cfg solm evm (.new name valExpr args retVar salt) .reverted
  | return :
      evalExprs? cfg solm evm exprs = .ok values ->
      ExecStmt cfg solm evm (.return exprs) (.returned solm evm (some values))
  | returnRevert :
      evalExprs? cfg solm evm exprs = .revert ->
      ExecStmt cfg solm evm (.return exprs) .reverted
  | break :
      ExecStmt cfg solm evm .break (.break solm evm)
  | continue :
      ExecStmt cfg solm evm .continue (.continue solm evm)

/-- The loop part of a `for (init; cond; post) { body }`, after `init` has run.  Each iteration
    checks `cond`; on `true` it runs `body` then `post` and loops.  A `break` in `body` exits the
    loop with `.ok` (skipping `post`); a `continue` runs `post` and loops; `return`/`revert`
    propagate.  `post` may only fall through (`.ok`) or revert. -/
inductive ExecForLoop (cfg : Config) :
    Frame -> EVM.State -> Expr /- cond -/ -> List Stmt /- post -/ -> List Stmt /- body -/ ->
    ExecResult -> Prop where
  | falseDone {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool false) ->
      ExecForLoop cfg solm evm condExpr post body (.ok solm evm)
  | condRevert {condExpr} :
      evalExpr? cfg solm evm condExpr =.revert ->
      ExecForLoop cfg solm evm condExpr post body .reverted
  | bodyReturn {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool true) ->
      ExecBlock cfg solm evm body (.returned solm' evm' value) ->
      ExecForLoop cfg solm evm condExpr post body (.returned solm' evm' value)
  | bodyRevert {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool true) ->
      ExecBlock cfg solm evm body .reverted ->
      ExecForLoop cfg solm evm condExpr post body .reverted
  | bodyBreak {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool true) ->
      ExecBlock cfg solm evm body (.break solm' evm') ->
      ExecForLoop cfg solm evm condExpr post body (.ok solm' evm')
  | iterate {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool true) ->
      ExecBlock cfg solm evm body (.ok solm1 evm1) ->
      ExecBlock cfg solm1 evm1 post (.ok solm2 evm2) ->
      ExecForLoop cfg solm2 evm2 condExpr post body result ->
      ExecForLoop cfg solm evm condExpr post body result
  | iteratePostRevert {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool true) ->
      ExecBlock cfg solm evm body (.ok solm1 evm1) ->
      ExecBlock cfg solm1 evm1 post .reverted ->
      ExecForLoop cfg solm evm condExpr post body .reverted
  | continueIter {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool true) ->
      ExecBlock cfg solm evm body (.continue solm1 evm1) ->
      ExecBlock cfg solm1 evm1 post (.ok solm2 evm2) ->
      ExecForLoop cfg solm2 evm2 condExpr post body result ->
      ExecForLoop cfg solm evm condExpr post body result
  | continuePostRevert {condExpr} :
      evalExpr? cfg solm evm condExpr =.ok (.bool true) ->
      ExecBlock cfg solm evm body (.continue solm1 evm1) ->
      ExecBlock cfg solm1 evm1 post .reverted ->
      ExecForLoop cfg solm evm condExpr post body .reverted

inductive ExecBlock (cfg : Config) :
    Frame -> EVM.State -> List Stmt -> ExecResult -> Prop where
  | nil :
      ExecBlock cfg solm evm [] (.ok solm evm)
  | consNormal :
      ExecStmt cfg solm evm stmt (.ok solm' evm') ->
      ExecBlock cfg solm' evm' stmts result ->
      ExecBlock cfg solm evm (stmt :: stmts) result
  | consReturn :
      ExecStmt cfg solm evm stmt (.returned solm' evm' value) ->
      ExecBlock cfg solm evm (stmt :: stmts) (.returned solm' evm' value)
  | consRevert :
      ExecStmt cfg solm evm stmt .reverted ->
      ExecBlock cfg solm evm (stmt :: stmts) .reverted
  | consBreak :
      ExecStmt cfg solm evm stmt (.break solm' evm') ->
      ExecBlock cfg solm evm (stmt :: stmts) (.break solm' evm')
  | consContinue :
      ExecStmt cfg solm evm stmt (.continue solm' evm') ->
      ExecBlock cfg solm evm (stmt :: stmts) (.continue solm' evm')

inductive ExecFuncBody (cfg : Config) :
    Frame -> EVM.State -> List Stmt -> ExecResult -> Prop where
  | execBlockOK :
      ExecBlock cfg solm evm body (.ok solm' evm') ->
      ExecFuncBody cfg solm evm body (.returned solm' evm' none)
  | execBlockRet :
      ExecBlock cfg solm evm body (.returned solm' evm' value) ->
      ExecFuncBody cfg solm evm body (.returned solm' evm' value)
  | execBlockRevert :
      ExecBlock cfg solm evm body .reverted ->
      ExecFuncBody cfg solm evm body .reverted
  -- A `break`/`continue` that occurs outside a loop is malformed. We have to handle it so that ExecFuncBody is never stuck.
  | execBlockBreak :
      ExecBlock cfg solm evm body (.break solm' evm') ->
      ExecFuncBody cfg solm evm body (.returned solm' evm' none)
  | execBlockContinue :
      ExecBlock cfg solm evm body (.continue solm' evm') ->
      ExecFuncBody cfg solm evm body (.returned solm' evm' none)

end

def ExecTransitionBody (cfg : Config) (contract : ContractDecl) (evm : EVM.State)
    (locals : Store) (body : Body) (result : ExecResult) : Prop :=
  ExecFuncBody cfg { contract := contract, locals := locals } evm body result

-- Solm transaction dispatch and execution.
inductive solmExec
    (conf : Config)
    (contract : ContractDecl) /- Spec -/
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (solmRes : ExecResult)
: ReturnConvention -> Prop where
  | intro :
    /- Solm selector transition dispatch. -/
    selectorDispatchMsg contract I.calldata = .some transition →
    transitionSig = transitionSignature transition →
    decodeCalldataWithMode conf.abiDecodeMode (transition.params.map Param.name)
      transitionSig.paramTypes I.calldata = .some callargs →
    evmState =
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := createdAccounts
          machineState.gasAvailable := .ofUInt256 g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader
      } →
    ExecTransitionBody conf contract evmState callargs transition.body solmRes →
    solmExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I solmRes
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
          createdAccounts := createdAccounts
          machineState.gasAvailable := .ofUInt256 g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader
      } →
    ExecTransitionBody conf contract evmState callargs transition.body solmRes →
    solmExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I solmRes
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
          createdAccounts := createdAccounts
          machineState.gasAvailable := .ofUInt256 g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader
      } →
    ExecTransitionBody conf contract evmState ∅ transition.body solmRes →
    solmExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I solmRes (.abi [])

-- Solm constructor execution.
inductive solmCtorExec
    (conf : Config)
    (contract : ContractDecl) /- Spec -/
    (args : List Value)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv)
    (solmRes : ExecResult)
: Prop where
  | intro :
    evmState =
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := createdAccounts
          machineState.gasAvailable := .ofUInt256 g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader
      } →
    -- This may be redundant when `cfg.selfDeployment` already enforces valid constructor ABI
    -- encoding, but it keeps the parameter store from relying on `List.zip` truncation.
    args.length = contract.ctor.params.length →
    argsStore = Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args) →
    ExecTransitionBody conf contract evmState argsStore contract.ctor.body solmRes →
    solmCtorExec conf contract args createdAccounts genesisBlockHeader blocks σ σ₀ g A I solmRes

end Solm
