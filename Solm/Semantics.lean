import Solm.Storage
import Solm.Value

namespace Solm

open ABI

structure ExternalCallABI where
  encode? : Ident -> List Value -> Option EVM.Bytes
  decode? : Ident -> EVM.Bytes-> Option Value

structure Config where
  storage : StorageLayout
  externalABI : ExternalCallABI
  /- Initialisation code (creation bytecode ++ ABI-encoded constructor args) for a
     `new` of the named contract. -/
  creationCode : Ident -> List Value -> Option EVM.Bytes := fun _ _ => none

structure ContractInstance where
  contract : Ident
  contractCode : ContractDecl
  storage : Store
  balance : Int

abbrev World := Std.HashMap EVM.Address ContractInstance

structure CallEnv where
  caller : EVM.Address
  origin : EVM.Address
  callvalue : Int
  this : EVM.Address

structure Frame where
  contract : ContractDecl
  locals : Store

inductive ExecResult where
  | returned : Frame -> EVM.State -> Option Value -> ExecResult
  | ok : Frame -> EVM.State -> ExecResult
  | break : Frame -> EVM.State -> ExecResult
  | continue : Frame -> EVM.State -> ExecResult
  | reverted : ExecResult

structure CallableDecl where
  params : List Param
  returnType : Option ABIType := none
  body : Body
  deriving Repr, Inhabited


def lookupStorageDecl? (decls : List StorageDecl) (name : Ident) : Option StorageDecl :=
  match decls with
  | [] => none
  | d :: ds => if d.name = name then some d else lookupStorageDecl? ds name

def envValue (evm : EVM.State) : EnvVar -> Value
  | .caller => .address evm.executionEnv.source
  | .origin => .address evm.executionEnv.sender
  | .callvalue => .int (Int.ofNat evm.executionEnv.weiValue.val)
  | .this => .address evm.executionEnv.codeOwner
  | .timestamp => .int (Int.ofNat evm.executionEnv.header.timestamp)

def abiValueToWord? (ty : ABIType) (value : Value) : Option EVM.Word :=
  match ty, value with
  | .elem .bool, .bool b => some (b.toUInt256)
  | .elem .address, .address a => some (EVM.word a)
  | .elem (.int (.uint _)), .int i =>
      if i < 0 then none else some (EVM.wordOfInt i)
  | .elem (.int (.sint _)), .int i => some (EVM.wordOfInt i)
  | _, _ => none

def abiWordToValue? (ty : ABIType) (word : EVM.Word) : Option Value :=
  match ty with
  | .elem .bool => some (.bool (word != ⟨0⟩))
  | .elem .address => some (.address (.ofNat word.val))
  | .elem (.int (.uint _)) => some (.int (Int.ofNat word.val))
  | .elem (.int (.sint _)) => some (.int (EVM.signed word))
  | _ => none

def slotValueToWord? (ty : StorageType) (value : Value) : Option EVM.Word :=
  match ty with
  | .elem primTy => abiValueToWord? (.elem primTy) value
  | .contract _ =>
      match value with
      | .address a => some (EVM.word a)
      | _ => none
  | _ => none

def slotWordToValue? (ty : StorageType) (word : EVM.Word) : Option Value :=
  match ty with
  | .elem primTy => abiWordToValue? (.elem primTy) word
  | .contract _ => some (.address (.ofNat word.val))
  | _ => none

def slotPushStep (slot : StorageRef) (step : StorageRefStep) : StorageRef :=
  { slot with steps := slot.steps ++ [step] }

def valueToKey? (v : Value) : Option KeyValue :=
  match v with
  | .int i => pure $ .int i
  | .bool b => pure $ .bool b
  | .address a => pure $ .address a
  | _ => .none

def lookupAssoc [DecidableEq α] (entries : List (α × β)) (key : α) : Option β :=
  match entries with
  | [] => none
  | (k, v) :: rest => if k = key then some v else lookupAssoc rest key

def updateAssoc [DecidableEq α] (entries : List (α × β)) (key : α) (value : β) :
    List (α × β) :=
  match entries with
  | [] => [(key, value)]
  | (k, v) :: rest =>
      if k = key then
        (key, value) :: rest
      else
        (k, v) :: updateAssoc rest key value

def lookupValueAssoc (entries : List (Value × β)) (key : Value) : Option β :=
  match entries with
  | [] => none
  | (k, v) :: rest => if k = key then some v else lookupValueAssoc rest key

def updateValueAssoc (entries : List (Value × β)) (key : Value) (value : β) :
    List (Value × β) :=
  match entries with
  | [] => [(key, value)]
  | (k, v) :: rest =>
      if k == key then
        (key, value) :: rest
      else
        (k, v) :: updateValueAssoc rest key value

def updateNth? (xs : List α) (index : Nat) (value : α) : Option (List α) :=
  match xs, index with
  | [], _ => none
  | _ :: rest, 0 => some (value :: rest)
  | x :: rest, i + 1 => do
      let rest' <- updateNth? rest i value
      pure (x :: rest')

def lookupNth? (xs : List α) (index : Nat) : Option α :=
  match xs, index with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: rest, i + 1 => lookupNth? rest i

def intToNat? (n : Int) : Option Nat :=
  if n < 0 then none else some n.toNat

def lookupField? (v : Value) (name : Ident) : Option Value :=
  match v with
  | .struct _ fields => lookupAssoc fields name
  | _ => none

def updateField? (v : Value) (name : Ident) (value : Value) : Option Value :=
  match v with
  | .struct tag fields =>
      match lookupAssoc fields name with
      | some _ => some (.struct tag (updateAssoc fields name value))
      | none => none
  | _ => none

def lookupIndex? (container key : Value) : Option Value :=
  match container with
  | .array elems =>
      match key with
      | .int i => do
          let idx <- intToNat? i
          lookupNth? elems idx
      | _ => none
  | _ => none

def updateIndex? (container key value : Value) : Option Value :=
  match container with
  | .array elems =>
      match key with
      | .int i => do
          let idx <- intToNat? i
          let elems' <- updateNth? elems idx value
          pure (.array elems')
      | _ => none
  | _ => none

def castValue? (v : Value) (ty : StorageType) : Option Value :=
  match ty, v with
  | .elem (.bool), .bool _ => some v
  | .elem (.address), .address _ => some v
  -- `address(n)`: an integer cast to `address` (e.g. `address(0)`), truncated to the address width.
  | .elem (.address), .int n => some (.address (.ofNat n.toNat))
  | .elem (.int _), .int _ => some v
  | .contract _, .address _ => some v
  | .struct expected _, .struct actual _ =>
      if expected = actual then some v else none
  | .array _ _, .array _ => some v
  | .dynamicArray _, .array _ => some v
  | _, _ => none

/-- Solm evaluation errors. Should never happen in well-formed programs -/
inductive EvalError where
  | unboundVariable
  | typeError
  | storageError
  deriving DecidableEq, Repr, Inhabited

/-- Result of evaluating an Solm expression:
    - a value (`ok`)
    - a `revert`
    - or an error, which indicates an ill-formed program
-/
inductive EvalResult (α : Type) where
  | ok : α -> EvalResult α
  | revert : EvalResult α
  | error : EvalError -> EvalResult α
  deriving Repr

namespace EvalResult

@[inline] def bind : EvalResult α -> (α -> EvalResult β) -> EvalResult β
  | .ok a,    f => f a
  | .revert,  _ => .revert
  | .error e, _ => .error e

instance : Monad EvalResult where
  pure := .ok
  bind := bind

/-- Lift an `Option`, mapping `none` to the model-level `error e`. -/
@[inline] def ofOption (e : EvalError) : Option α -> EvalResult α
  | some a => .ok a
  | none   => .error e

/-- Sequence a list of results, short-circuiting on the first `revert`/`error`. -/
def seqList : List (EvalResult α) -> EvalResult (List α)
  | [] => .ok []
  | x :: xs => do
      let a <- x
      let as <- seqList xs
      .ok (a :: as)

end EvalResult

def evalUnaryOp? (op : UnaryOp) (v : Value) : Option Value :=
  match op, v with
  | .not, .bool b => some (.bool (!b))
  | .neg, .int i => some (.int (-i))
  | _, _ => none

def evalBinaryOp? (op : BinaryOp) (v₁ v₂ : Value) : EvalResult Value :=
  match op, v₁, v₂ with
  | .add, .int x, .int y => .ok (.int (x + y))
  | .sub, .int x, .int y => .ok (.int (x - y))
  | .mul, .int x, .int y => .ok (.int (x * y))
  -- division/modulo by zero reverts (Solidity Panic 0x12)
  | .div, .int x, .int y => if y = 0 then .revert else .ok (.int (x / y))
  | .mod, .int x, .int y => if y = 0 then .revert else .ok (.int (x % y))
  | .eq, .storageRef _ _, _ => .error .typeError
  | .eq, _, .storageRef _ _ => .error .typeError
  | .ne, .storageRef _ _, _ => .error .typeError
  | .ne, _, .storageRef _ _ => .error .typeError
  | .eq, x, y => .ok (.bool (x == y))
  | .ne, x, y => .ok (.bool (!(x == y)))
  | .lt, .int x, .int y => .ok (.bool (x < y))
  | .le, .int x, .int y => .ok (.bool (x <= y))
  | .gt, .int x, .int y => .ok (.bool (x > y))
  | .ge, .int x, .int y => .ok (.bool (x >= y))
  | .and, .bool x, .bool y => .ok (.bool (x && y))
  | .or, .bool x, .bool y => .ok (.bool (x || y))
  | _, _, _ => .error .typeError

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


-- Defining a measure for termination of the next mutual block,
-- that evaluates expressions and related types
mutual
  def exprEvalSize : Expr → Nat
    | .intLit _ => 1
    | .boolLit _ => 1
    | .bytesLit _ => 1
    | .newBytes lenExpr => exprEvalSize lenExpr + 1
    | .newArray _ lenExpr => exprEvalSize lenExpr + 1
    | .bytesSlice baseE startE endE =>
        exprEvalSize baseE + exprEvalSize startE + exprEvalSize endE + 1
    | .var _ => 1
    | .env _ => 1
    | .storage slot => slotEvalSize slot + 1
    | .arrayLength _ slot => slotEvalSize slot + 1
    | .field base _ => exprEvalSize base + 1
    | .cast expr _ => exprEvalSize expr + 1
    | .inRange _ expr => exprEvalSize expr + 1
    | .addrOf expr => exprEvalSize expr + 1
    | .unary _ expr => exprEvalSize expr + 1
    | .binary _ lhs rhs => exprEvalSize lhs + exprEvalSize rhs + 1
    | .ite cond thenExpr elseExpr =>
        exprEvalSize cond + exprEvalSize thenExpr + exprEvalSize elseExpr + 1
  termination_by expr => (sizeOf expr, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first | (cases slot; simp; omega) | decreasing_tactic

  def slotEvalSize (slot : StorageRef) : Nat :=
    slotStepsEvalSize slot.steps + 1
  termination_by (sizeOf slot.steps, 1)
  decreasing_by
    all_goals omega

  def slotStepEvalSize : StorageRefStep → Nat
    | .field _ => 1
    | .mindex expr => exprEvalSize expr + 1
    | .aindex expr => exprEvalSize expr + 1
  termination_by step => (sizeOf step, 0)
  decreasing_by
    all_goals simp_wf
    all_goals decreasing_tactic

  def slotStepsEvalSize : List StorageRefStep → Nat
    | [] => 1
    | step :: rest => slotStepEvalSize step + slotStepsEvalSize rest + 1
  termination_by steps => (sizeOf steps, 0)
  decreasing_by
    all_goals simp_wf
    all_goals decreasing_tactic
end

lemma stepSize_lt_stepsSize : ∀ (slot : StorageRef) step,
  step ∈ slot.steps →
  slotStepEvalSize step < slotStepsEvalSize slot.steps := by
    intros slot step
    induction slot.steps with
    | nil => intro hin; cases hin
    | cons head tail tail_ih =>
      intro hin
      cases hin
      · simp [slotStepsEvalSize]; omega
      · rename_i hin
        simp [slotStepsEvalSize]
        apply lt_trans (b:= slotStepsEvalSize tail) (tail_ih hin); omega

/-- The declared `StorageType` reached by following one evaled step from a value of type `t`. -/
def storageTypeStep? : StorageType -> EvaledStorageRefStep -> Option StorageType
  | .struct _ fields, .field name => (fields.find? (fun f => f.1 == name)).map (·.2)
  | .tuple ts, .tupleElem k => ts[k]?
  | .mapping _ v, .mindex _ => some v
  | .array t' _, .aindex _ => some t'
  | .dynamicArray t', .aindex _ => some t'
  | _, _ => none

/-- The declared `StorageType` of whatever the evaled ref `er` points at, walked from the contract's
    storage declarations (the type tree carried by the frame, independent of the opaque layout). -/
def storageTypeAt? (decls : List StorageDecl) (er : EvaledStorageRef) : Option StorageType := do
  let baseTy <- (decls.find? (fun d => d.name == er.base)).map (·.ty)
  er.steps.foldlM storageTypeStep? baseTy

/-- Bounds-check a single array index `i` against the array reached by the evaled prefix `pre`.
    Fixed arrays are checked against their declared static bound. Dynamic arrays are checked by
    asking the layout for the distinct `.length` ref `layout {base, pre ++ [.length]}` and reading
    the stored length. In both cases, an index outside `[0, length)` reverts, matching Solidity's
    `Panic(0x32)`.

    This is invoked from `evalStorageRefStep` as each `.aindex` is evaluated, so the check is
    interleaved with index evaluation exactly as solc emits it. -/
@[simp] def arrayIndexInBounds? (cfg : Config) (evm : EVM.State)
    (decls : List StorageDecl) (base : Ident) (pre : List EvaledStorageRefStep) (i : KeyValue) :
    EvalResult Unit :=
  match storageTypeAt? decls { base := base, steps := pre }, i with
  | some (.array _ n), .int iv =>
      if 0 ≤ iv ∧ iv < n then .ok () else .revert
  | some (.array _ _), _ => .error .typeError
  | some (.dynamicArray _), .int iv =>
      match cfg.storage.layout { base := base, steps := pre ++ [.length] } with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
          | _ => .error .storageError
      | none => .error .storageError
  | some (.dynamicArray _), _ => .error .typeError
  | some _, _ => .error .typeError
  | none, _ => .error .storageError

/- Recursively zero **every** storage slot occupied by a value of declared type `t` located at
   `er` — solc's `delete`.  Leaves are cleared through the opaque `layout`; the *structure* (struct
   fields, tuple/fixed-array elements, dynamic-array length + all data) is driven by `t`, so a
   nested dynamic array is cleared in full (its inner length is read and every inner element
   recursively cleared).  Mappings are skipped — their keys aren't enumerable, and solc's `delete`
   on a mapping is likewise a no-op. -/
mutual
def clearStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> EvalResult EVM.State
  | .elem _ | .contract _ =>
      match cfg.storage.layout er with
      | some loc => EvalResult.ofOption .storageError (storageLocStore evm loc (.int 0))
      | none => .error .storageError
  | .mapping _ _ => .ok evm
  | .struct _ fields => clearFields? cfg evm er fields
  | .tuple ts => clearTupleElems? cfg evm er 0 ts
  | .array t' n => clearArrayElems? cfg evm er t' n
  | .dynamicArray t' =>
      match cfg.storage.layout { er with steps := er.steps ++ [.length] } with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len =>
              match clearArrayElems? cfg evm er t' len.toNat with
              | .ok evm1 => EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int 0))
              | r => r
          | _ => .error .storageError
      | none => .error .storageError
  termination_by t => (sizeOf t, 0)

def clearFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult EVM.State
  | [] => .ok evm
  | (name, ft) :: rest =>
      match clearStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft with
      | .ok evm1 => clearFields? cfg evm1 er rest
      | r => r
  termination_by fields => (sizeOf fields, 0)

def clearTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> EvalResult EVM.State
  | [] => .ok evm
  | tt :: rest =>
      match clearStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt with
      | .ok evm1 => clearTupleElems? cfg evm1 er (k+1) rest
      | r => r
  termination_by ts => (sizeOf ts, 0)

def clearArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (t' : StorageType) :
    Nat -> EvalResult EVM.State
  | 0 => .ok evm
  | n+1 =>
      match clearStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int n)] } t' with
      | .ok evm1 => clearArrayElems? cfg evm1 er t' n
      | r => r
  termination_by c => (sizeOf t', c)
end

/- Recursively write a structured `Value` into the storage of declared type `t` at `er` — the dual
   of `clearStorage?`.  Leaves go through the opaque `layout` + `storageLocStore`; structure (struct
   fields, tuple/array elements) is driven by `t`, and a `dynamicArray` target also writes its
   length.  A type/value mismatch (or a mapping/`bytes` target) is an `.error`, never a partial
   write. -/
mutual
def writeStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> Value -> EvalResult EVM.State
  | .elem _, v
  | .contract _, v =>
      match cfg.storage.layout er with
      | some loc => EvalResult.ofOption .storageError (storageLocStore evm loc v)
      | none => .error .storageError
  | .struct _ ftypes, .struct _ fvals => writeFields? cfg evm er ftypes fvals
  | .tuple ts, .array vs => writeTupleElems? cfg evm er 0 ts vs
  | .array t' n, .array vs =>
      if vs.length = n then writeArrayElems? cfg evm er t' 0 vs
      else .error .typeError
  | .dynamicArray t', .array vs => do
      -- clear the existing array first, so old elements beyond the new (possibly shorter) length
      -- don't linger — matching solc's array-assignment cleanup, and preserving the
      -- zero-beyond-length invariant that grow-only `push` relies on
      let evm0 <- clearStorage? cfg evm er (.dynamicArray t')
      let evm1 <- writeArrayElems? cfg evm0 er t' 0 vs
      let lenLoc <- EvalResult.ofOption .storageError
        (cfg.storage.layout { er with steps := er.steps ++ [.length] })
      EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int vs.length))
  | _, _ => .error .typeError
  termination_by t => (sizeOf t, 0)

def writeFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> List (Ident × Value) -> EvalResult EVM.State
  | [], [] => .ok evm
  | (name, ft) :: trest, (vname, fv) :: vrest =>
      if name == vname then
        match writeStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft fv with
        | .ok evm1 => writeFields? cfg evm1 er trest vrest
        | r => r
      else .error .typeError
  | _, _ => .error .typeError
  termination_by ftypes => (sizeOf ftypes, 0)

def writeTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> List Value -> EvalResult EVM.State
  | [], [] => .ok evm
  | tt :: trest, v :: vrest =>
      match writeStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt v with
      | .ok evm1 => writeTupleElems? cfg evm1 er (k+1) trest vrest
      | r => r
  | _, _ => .error .typeError
  termination_by ts => (sizeOf ts, 0)

def writeArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (t' : StorageType)
    (k : Nat) : List Value -> EvalResult EVM.State
  | [] => .ok evm
  | v :: rest =>
      match writeStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int k)] } t' v with
      | .ok evm1 => writeArrayElems? cfg evm1 er t' (k+1) rest
      | r => r
  termination_by vs => (sizeOf t', sizeOf vs)
end

/- Recursively read a value of declared type `t` out of storage at `er` into a `Value` — the read
   dual of `writeStorage?`/`clearStorage?`.  Leaves come from the opaque `layout` + `storageLocLoad`;
   structure (struct fields, tuple/fixed-array elements, dynamic-array length + all data) is driven
   by `t`, so a nested dynamic array is read in full.  A mapping has no enumerable contents, so a
   whole-mapping read is an `.error`. -/
mutual
def readStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> EvalResult Value
  | .elem _
  | .contract _ =>
      match cfg.storage.layout er with
      | some loc => .ok (storageLocLoad evm loc)
      | none => .error .storageError
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let fvals <- readFields? cfg evm er fields
      pure (.struct name fvals)
  | .tuple ts => do
      let vs <- readTupleElems? cfg evm er 0 ts
      pure (.array vs)
  | .array t' n => do
      let vs <- readArrayElems? cfg evm er t' 0 n
      pure (.array vs)
  | .dynamicArray t' =>
      match cfg.storage.layout { er with steps := er.steps ++ [.length] } with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len => do
              let vs <- readArrayElems? cfg evm er t' 0 len.toNat
              pure (.array vs)
          | _ => .error .storageError
      | none => .error .storageError
  termination_by t => (sizeOf t, 0)

def readFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult (List (Ident × Value))
  | [] => .ok []
  | (name, ft) :: rest => do
      let v <- readStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft
      let vrest <- readFields? cfg evm er rest
      pure ((name, v) :: vrest)
  termination_by fields => (sizeOf fields, 0)

def readTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> EvalResult (List Value)
  | [] => .ok []
  | tt :: rest => do
      let v <- readStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt
      let vrest <- readTupleElems? cfg evm er (k+1) rest
      pure (v :: vrest)
  termination_by ts => (sizeOf ts, 0)

def readArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (t' : StorageType)
    (k : Nat) : Nat -> EvalResult (List Value)
  | 0 => .ok []
  | c+1 => do
      let v <- readStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int k)] } t'
      let vrest <- readArrayElems? cfg evm er t' (k+1) c
      pure (v :: vrest)
  termination_by c => (sizeOf t', c)
end

def readStorageArrayLength? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    : StorageType -> EvalResult Value
  | .array _ n => pure (.int n)
  | .dynamicArray _ =>
      match cfg.storage.layout { er with steps := er.steps ++ [.length] } with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int n => pure (.int n)
          | _ => .error .storageError
      | none => .error .storageError
  | _ => .error .typeError

mutual
def defaultValue? : StorageType -> EvalResult Value
  | .elem (.bool) => pure (.bool false)
  | .elem (.address) => pure (.address (.ofNat 0))
  | .elem _ => pure (.int 0)
  | .contract _ => pure (.address (.ofNat 0))
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let values <- defaultFields? fields
      pure (.struct name values)
  | .tuple ts => do
      let values <- defaultValues? ts
      pure (.array values)
  | .array elemTy n => do
      let value <- defaultValue? elemTy
      pure (.array (List.replicate n value))
  | .dynamicArray _ => pure (.array [])
  termination_by t => (sizeOf t, 0)

def defaultFields? : List (Ident × StorageType) -> EvalResult (List (Ident × Value))
  | [] => pure []
  | (name, ty) :: rest => do
      let value <- defaultValue? ty
      let values <- defaultFields? rest
      pure ((name, value) :: values)
  termination_by fields => (sizeOf fields, 0)

def defaultValues? : List StorageType -> EvalResult (List Value)
  | [] => pure []
  | ty :: rest => do
      let value <- defaultValue? ty
      let values <- defaultValues? rest
      pure (value :: values)
  termination_by ts => (sizeOf ts, 0)
end

mutual

def evalStorageRefStep (cfg : Config) (solm : Frame) (evm : EVM.State)
    (base : Ident) (pre : List EvaledStorageRefStep) (step : StorageRefStep) : EvalResult EvaledStorageRefStep :=
  match step with
  | .field name => pure (.field name)
  | .mindex expr => do
    let index <- evalExpr? cfg solm evm expr
    let indexKey <- EvalResult.ofOption .typeError (valueToKey? index)
    pure (.mindex indexKey)
  | .aindex expr => do
    let index <- evalExpr? cfg solm evm expr
    let indexKey <- EvalResult.ofOption .typeError (valueToKey? index)
    -- check this index in bounds against the array reached by `pre`, *before* descending —
    -- interleaved with index evaluation exactly as solc emits it
    let _ <- arrayIndexInBounds? cfg evm solm.contract.storage base pre indexKey
    pure (.aindex indexKey)
  termination_by (slotStepEvalSize step, 0)
  decreasing_by
    all_goals simp [slotStepEvalSize]
    all_goals omega

/-- Evaluate a list of storage-ref steps left to right, threading the evaled prefix so each
    `.aindex` can be bounds-checked against the array reached so far (see `evalStorageRefStep`). -/
@[simp] def evalStorageRefSteps (cfg : Config) (solm : Frame) (evm : EVM.State)
    (base : Ident) (pre : List EvaledStorageRefStep) :
    List StorageRefStep -> EvalResult (List EvaledStorageRefStep)
  | [] => pure []
  | step :: rest => do
      let estep <- evalStorageRefStep cfg solm evm base pre step
      let erest <- evalStorageRefSteps cfg solm evm base (pre ++ [estep]) rest
      pure (estep :: erest)
  termination_by steps => (slotStepsEvalSize steps, 0)
  decreasing_by
    all_goals simp [slotStepsEvalSize]
    all_goals omega

def evalStorageRef (cfg : Config) (solm : Frame) (evm : EVM.State) (slot : StorageRef) : EvalResult EvaledStorageRef := do
  let steps <- evalStorageRefSteps cfg solm evm slot.base [] slot.steps
  pure { base := slot.base, steps := steps }
  termination_by (slotEvalSize slot, 0)
  decreasing_by
    simp [slotEvalSize]
    apply Prod.Lex.left
    omega

/-- Follow unevaluated storage-ref steps from an already-evaluated storage root, threading both the
    concrete evaluated path and its declared storage type. This is the workhorse for local
    `storage` aliases. -/
def evalStorageRefFrom? (cfg : Config) (solm : Frame) (evm : EVM.State)
    (er : EvaledStorageRef) (ty : StorageType) :
    List StorageRefStep -> EvalResult (EvaledStorageRef × StorageType)
  | [] => pure (er, ty)
  | step :: rest => do
      let estep <- evalStorageRefStep cfg solm evm er.base er.steps step
      let ty' <- EvalResult.ofOption .typeError (storageTypeStep? ty estep)
      evalStorageRefFrom? cfg solm evm { er with steps := er.steps ++ [estep] } ty' rest
  termination_by steps => (slotStepsEvalSize steps, 0)
  decreasing_by
    all_goals simp [slotStepsEvalSize]
    all_goals omega

/-- Resolve a storage lvalue. The base may be a contract storage declaration or a local
    `Value.storageRef` alias; in the latter case we append the unevaluated suffix to the stored,
    already-evaluated reference. -/
def resolveStorageRef? (cfg : Config) (solm : Frame) (evm : EVM.State)
    (slot : StorageRef) : EvalResult (EvaledStorageRef × StorageType) :=
  match solm.locals.get? slot.base with
  | some (.storageRef er ty) => evalStorageRefFrom? cfg solm evm er ty slot.steps
  | _ =>
      match evalStorageRef cfg solm evm slot with
      | .ok er => do
          let ty <- EvalResult.ofOption .storageError (storageTypeAt? solm.contract.storage er)
          pure (er, ty)
      | .revert => .revert
      | .error e => .error e
  termination_by (slotEvalSize slot, 1)
  decreasing_by
    all_goals simp [slotEvalSize]
    all_goals omega

def resolveDynamicArrayRef? (cfg : Config) (solm : Frame) (evm : EVM.State)
    (ref : StorageRef) : EvalResult (EvaledStorageRef × StorageType) := do
  let (er, ty) <- resolveStorageRef? cfg solm evm ref
  match ty with
  | .dynamicArray elemTy => pure (er, elemTy)
  | _ => .error .storageError

def readLocalPath? (cfg : Config) (solm : Frame) (evm : EVM.State)
    (root : Value) : List StorageRefStep -> EvalResult Value
  | [] => pure root
  | .field name :: rest => do
      let child <- EvalResult.ofOption .typeError (lookupField? root name)
      readLocalPath? cfg solm evm child rest
  | .mindex expr :: rest => do
      let idx <- evalExpr? cfg solm evm expr
      let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
      readLocalPath? cfg solm evm child rest
  | .aindex expr :: rest => do
      let idx <- evalExpr? cfg solm evm expr
      match root, idx with
      | .array elems, .int i =>
          -- memory array index read: out of bounds reverts (solc's `Panic(0x32)`)
          if 0 ≤ i ∧ i < elems.length then
            let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
            readLocalPath? cfg solm evm child rest
          else .revert
      | _, _ =>
          let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
          readLocalPath? cfg solm evm child rest
  termination_by steps => (slotStepsEvalSize steps, 0)
  decreasing_by
    all_goals simp [slotStepsEvalSize, slotStepEvalSize]
    all_goals omega

def updateLocalPath? (cfg : Config) (solm : Frame) (evm : EVM.State)
    (root : Value) (steps : List StorageRefStep) (value : Value) : EvalResult Value :=
  match steps with
  | [] => pure value
  | .field name :: rest => do
      let child <- EvalResult.ofOption .typeError (lookupField? root name)
      let child' <- updateLocalPath? cfg solm evm child rest value
      EvalResult.ofOption .typeError (updateField? root name child')
  | .mindex expr :: rest => do
      let idx <- evalExpr? cfg solm evm expr
      let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
      let child' <- updateLocalPath? cfg solm evm child rest value
      EvalResult.ofOption .typeError (updateIndex? root idx child')
  | .aindex expr :: rest => do
      let idx <- evalExpr? cfg solm evm expr
      match root, idx with
      | .array elems, .int i =>
          -- memory array index write: out of bounds reverts (solc's `Panic(0x32)`)
          if 0 ≤ i ∧ i < elems.length then
            let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
            let child' <- updateLocalPath? cfg solm evm child rest value
            EvalResult.ofOption .typeError (updateIndex? root idx child')
          else .revert
      | _, _ =>
          let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
          let child' <- updateLocalPath? cfg solm evm child rest value
          EvalResult.ofOption .typeError (updateIndex? root idx child')
  termination_by (slotStepsEvalSize steps, 0)
  decreasing_by
    all_goals simp [slotStepsEvalSize, slotStepEvalSize]
    all_goals omega

def assignStorageRef? (cfg : Config) (solm : Frame) (evm : EVM.State)
    (origin : VarOrigin) (slot : StorageRef) (value : Value) : EvalResult (Frame × EVM.State) :=
  match origin with
  | .localVar =>
    -- in-memory local: functionally update the bound `Value` along the path
    match solm.locals.get? slot.base with
    | some root => do
        let root' <- updateLocalPath? cfg solm evm root slot.steps value
        pure ({ solm with locals := solm.locals.insert slot.base root' }, evm)
    | none => .error .unboundVariable
  | .storage => do
    let (evaledStorageRef, ty) <- resolveStorageRef? cfg solm evm slot
    match value with
    | .struct _ _ | .array _ => do
      -- whole-array / whole-struct assignment: write every slot by the declared type
      let evm' <- writeStorage? cfg evm evaledStorageRef ty value
      pure (solm, evm')
    | _ => do
      -- scalar leaf: a single whole/partial-slot store
      let loc <- EvalResult.ofOption .storageError (cfg.storage.layout evaledStorageRef)
      let evm' <- EvalResult.ofOption .storageError (storageLocStore evm loc value)
      pure (solm, evm')

def evalExpr? (cfg : Config) (solm : Frame) (evm : EVM.State) :
    Expr -> EvalResult Value
  | .intLit n => pure (.int n)
  | .boolLit b => pure (.bool b)
  | .bytesLit b => pure (.bytes b)
  | .newBytes lenExpr => do
      let lenVal <- evalExpr? cfg solm evm lenExpr
      match lenVal with
      | .int n => if n < 0 then .error .typeError
                  else pure (.bytes (ByteArray.mk (Array.replicate n.toNat (0 : UInt8))))
      | _ => .error .typeError
  | .newArray elemTy lenExpr => do
      let lenVal <- evalExpr? cfg solm evm lenExpr
      match lenVal with
      | .int n =>
          if n < 0 then .error .typeError
          else do
            let defaultValue <- defaultValue? elemTy
            pure (.array (List.replicate n.toNat defaultValue))
      | _ => .error .typeError
  | .bytesSlice baseE startE endE => do
      let baseV <- evalExpr? cfg solm evm baseE
      let startV <- evalExpr? cfg solm evm startE
      let endV <- evalExpr? cfg solm evm endE
      match baseV, startV, endV with
      | .bytes ba, .int s, .int e =>
          if s < 0 || e < 0 then .error .typeError
          else pure (.bytes (ba.extract s.toNat e.toNat))
      | _, _, _ => .error .typeError
  | .var name => EvalResult.ofOption .unboundVariable (solm.locals.get? name)
  | .env var => pure (envValue evm var)
  | .storage slot => do
      let (evaledStorageRef, ty) <- resolveStorageRef? cfg solm evm slot
      readStorage? cfg evm evaledStorageRef ty
  | .arrayLength origin slot => do
      match origin with
      | .storage => do
          let (er, ty) <- resolveStorageRef? cfg solm evm slot
          readStorageArrayLength? cfg evm er ty
      | .localVar =>
          match solm.locals.get? slot.base with
          | some root => do
              let v <- readLocalPath? cfg solm evm root slot.steps
              match v with
              | .array vs => pure (.int vs.length)
              | .bytes b => pure (.int (Int.ofNat b.size))
              | _ => .error .typeError
          | none => .error .unboundVariable
  | .field base name => do
      let baseValue <- evalExpr? cfg solm evm base
      match baseValue with
      | .storageRef er ty => do
          let step := EvaledStorageRefStep.field name
          let ty' <- EvalResult.ofOption .typeError (storageTypeStep? ty step)
          readStorage? cfg evm { er with steps := er.steps ++ [step] } ty'
      | _ => EvalResult.ofOption .typeError (lookupField? baseValue name)
  | .cast expr ty => do /- TODO do we really need to have casting? -/
      let value <- evalExpr? cfg solm evm expr
      EvalResult.ofOption .typeError (castValue? value ty)
  | .addrOf expr => do
      let value <- evalExpr? cfg solm evm expr
      match value with
      | .address a => pure (.address a)
      | _ => .error .typeError
  | .unary op expr => do
      let value <- evalExpr? cfg solm evm expr
      EvalResult.ofOption .typeError (evalUnaryOp? op value)
  | .binary op lhs rhs => do
      let lhsValue <- evalExpr? cfg solm evm lhs
      let rhsValue <- evalExpr? cfg solm evm rhs
      evalBinaryOp? op lhsValue rhsValue
  | .ite cond thenExpr elseExpr => do
      let condValue <- evalExpr? cfg solm evm cond
      match condValue with
      | .bool true => evalExpr? cfg solm evm thenExpr
      | .bool false => evalExpr? cfg solm evm elseExpr
      | _ => .error .typeError
  | .inRange intType expr => do
      let value <- evalExpr? cfg solm evm expr
      match value, intType with
      | .int i, .uint n =>
          if i < 0 || i >= 2^(n.val) then .revert else pure value
      | .int i, .sint n =>
          let bound : Int := 2^(n.val - 1)
          if i < -bound || i >= bound then .revert else pure value
      | _, _ => .error .typeError
  termination_by expr => (exprEvalSize expr, 0)
decreasing_by
  all_goals simp [exprEvalSize, slotEvalSize]
  all_goals omega

end

def evalExprs? (cfg : Config) (solm : Frame) (evm : EVM.State)
    (exprs : List Expr) : EvalResult (List Value) :=
  match exprs with
  | [] => pure []
  | expr :: rest => do
      let value <- evalExpr? cfg solm evm expr
      let values <- evalExprs? cfg solm evm rest
      pure (value :: values)

def externalValueToWord? : Value -> Option EVM.Word
  | .int i => some (EVM.wordOfInt i)
  | .bool b => some b.toUInt256
  | .address a => some (EVM.word a)
  | .unit => some ⟨0⟩
  | _ => none

def wordsOfValues? (values : List Value) : Option (List EVM.Word) :=
  match values with
  | [] => some []
  | value :: rest => do
      let word <- externalValueToWord? value
      let words <- wordsOfValues? rest
      some (word :: words)

def defaultEncodeCall? (_name : Ident) (args : List Value) : Option EVM.Bytes := do
  let words <- wordsOfValues? args
  some (words.foldl (fun bytes word => bytes ++ (Ethereum.UInt256.toByteArray word)) ByteArray.empty)

def defaultDecodeReturn? (_name : Ident) (bytes : EVM.Bytes) : Option Value :=
  -- The solc-generated ABI return decoder for an `int`/`uint` value reverts unless at least one
  -- full word (32 bytes) of return data is present (`if slt(returndatasize, 32) { revert }`).  We
  -- mirror that *partiality*: under-length return data decodes to `none`, which the
  -- `externalCallReturnDecodeRevert` rule turns into a revert — matching the bytecode.
  if bytes.size < 32 then
    none
  else
    some (.int (Ethereum.fromByteArrayBigEndian (bytes.extract 0 32)))

def defaultExternalCallABI : ExternalCallABI :=
  { encode? := defaultEncodeCall?, decode? := defaultDecodeReturn? }

/-- A raw message call to `target` with the given `value` and `calldata`, bridged directly to the
    EVM `Θ`.  No ABI encoding — calldata is supplied verbatim — and the boolean result is the raw
    `CALL` success flag.  Both the low-level `.call` and (via `typedCallViaEVM`) typed external calls
    are built on this. -/
inductive callViaEVM (evm : EVM.State) (target : EVM.Address)
    (value : ℤ) (calldata : EVM.Bytes) :
    (Bool × EVM.State × EVM.Bytes) → Prop where
  | callMade :
      valueWord = EVM.wordOfInt value
      → (∃ (callGas : Ethereum.UInt256) (A_in : Ethereum.Substate),
        -- The external call bridges directly to the EVM `Θ`.  Solm tracks neither gas nor the
        -- substate, so — exactly as `callGas` is already existential — the *entire* input
        -- substate `A_in` is existentially quantified: the call "behaves as `Θ` would for some
        -- gas and substate".  (The result substate `A'` is discarded; `execResultsEquiv` ignores
        -- it.)  `g'` is the (discarded) returned gas; named so it is a plain implicit.
          (cA', σ', g', A', z, o)
            = Ethereum.EVM.Θ
            evm.executionEnv.blobVersionedHashes
            evm.createdAccounts
            evm.genesisBlockHeader
            evm.blocks
            evm.accountMap
            evm.σ₀
            A_in
            evm.executionEnv.codeOwner  -- sender (msg.sender): `this`, as a CALL does
            evm.executionEnv.sender      -- original transactor (tx.origin)
            target
            (Ethereum.toExecute evm.accountMap target) -- this is the code
            callGas
            (.ofNat evm.executionEnv.gasPrice)
            valueWord -- actual value sent
            valueWord -- value reported to queries
            calldata
            (evm.executionEnv.depth + 1)
            evm.executionEnv.header
            true -- permission to modify state;
                 -- true for call/delegatecall/callcode, false for staticcall
        )

      -- let machine := -- We don't track machine state anyway
      --   { evm.machineState with
      --     gasAvailable := evm.machineState.gasAvailable + g' -- is this correct?
      --     returnData := o }
      → evm' = { evm with accountMap := σ', substate := A', createdAccounts := cA' }

      → valueWord ≤ (evm.accountMap.find? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
      → evm.executionEnv.depth ≠ 1024
      → callViaEVM evm target value calldata (z, evm', o)

  | callNotMade :
      A' = ((evm.addAccessedAccount target) |>.substate )
      → evm' = { evm with substate := A' }
      → (¬ (EVM.wordOfInt value ≤ (evm.accountMap.find? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
         ∧ evm.executionEnv.depth ≠ 1024))
      → callViaEVM evm target value calldata (false, evm', ByteArray.empty)

/-- A typed external call: ABI-encode `name`/`args` into calldata, then make a raw `callViaEVM`.
    This is the call form `externalCall` uses.  The return *decode* (and its failure) stays in the
    `ExecStmt` rules over the raw output bytes `o`, so decode-failure handling is unchanged. -/
def typedCallViaEVM (cfg : Config) (evm : EVM.State) (target : EVM.Address)
    (name : Ident) (value : ℤ) (args : List Value)
    (result : Bool × EVM.State × EVM.Bytes) : Prop :=
  ∃ calldata, cfg.externalABI.encode? name args = some calldata
            ∧ callViaEVM evm target value calldata result

-- Contract creation (`new`) via the EVM `Λ` (Lambda) function. The result triple is
-- `(addr, evm', success)`: the created contract's address, the resulting EVM state,
-- and whether creation succeeded. Mirrors `externalCallViaEVM`, but `Λ` runs the
-- initialisation code instead of a message call and returns the new address.
-- TODO Lefteris check

-- Preconditions under which a `new` (the `CREATE` opcode) actually runs the init code,
-- mirroring the guards the opcode checks before calling `Lambda`.
def newCanCreate (evm : EVM.State) (value : ℤ) (initCode : EVM.Bytes) : Prop :=
  let creator := evm.accountMap.find? evm.executionEnv.codeOwner |>.getD default
  EVM.wordOfInt value ≤ creator.balance        -- creator can afford the endowment
    ∧ evm.executionEnv.depth ≠ 1024            -- call-depth limit not reached
    ∧ creator.nonce.toNat < 2 ^ 64 - 1         -- creator nonce below the cap (EIP-2681)
    ∧ initCode.size ≤ 49152                     -- init code within the limit (EIP-3860)

inductive newViaEVM (cfg : Config) (evm : EVM.State)
    (name : Ident) (value : ℤ) (args : List Value) :
    (EVM.Address × EVM.State × Bool) → Prop where
  | created :
      cfg.creationCode name args = .some initCode
      → newCanCreate evm value initCode
      → valueWord = EVM.wordOfInt value
      → (∃ createGas refunds accessedStorageKeys,
          -- As in `externalCallViaEVM`, existentially quantify over substate fields
          -- whose value we do not track accurately but which creation can change.
          let A_exist := { evm.substate with
                      refundBalance := refunds
                      accessedStorageKeys := accessedStorageKeys }
          -- Mirror the CREATE opcode: bump the creator's nonce before calling `Lambda`,
          -- which derives the new address from `sender.nonce - 1` and so expects the
          -- already-incremented nonce.
          let creator := evm.accountMap.find? evm.executionEnv.codeOwner |>.getD default
          let σStar := evm.accountMap.insert evm.executionEnv.codeOwner
                        { creator with nonce := creator.nonce + ⟨1⟩ }
          (addr, cA', σ', _, A', z, _)
            = Ethereum.EVM.Lambda
            evm.executionEnv.blobVersionedHashes
            evm.createdAccounts
            evm.genesisBlockHeader
            evm.blocks
            σStar
            evm.σ₀
            A_exist
            evm.executionEnv.codeOwner  -- sender (msg.sender): `this`, as CREATE does
            evm.executionEnv.sender     -- original transactor (tx.origin)
            createGas
            (.ofNat evm.executionEnv.gasPrice)
            valueWord                   -- endowment
            initCode                    -- initialisation EVM code
            (evm.executionEnv.depth + 1)
            .none                       -- salt: `none` ⇒ CREATE (not CREATE2)
            evm.executionEnv.header
            true)                       -- permission to modify state
      → evm' = { evm with accountMap := σ', substate := A', createdAccounts := cA' }
      → newViaEVM cfg evm name value args (addr, evm', z)
  | notCreated :
      cfg.creationCode name args = .some initCode
      → ¬ newCanCreate evm value initCode
      → newViaEVM cfg evm name value args (EVM.address 0, evm, false)


def resumeAfterInternalCall (caller : Frame) (retVar : Ident) (value : Option Value) :
    Frame :=
  let valueToWrite := match value with | some v => v | none => .unit
  { caller with locals := caller.locals.insert retVar valueToWrite }

/-- `arr.push(v?)`: grow the dynamic array named by `ref` by one.  Reads the current length `L`
    (the layout's `.length` query); `some v` writes the value `v` at element `L` via `writeStorage?`
    — so scalar **and** compound (struct / nested array) elements are written in full, bypassing the
    bounds check (appending at the currently-out-of-range index `L` is the point).  `none` is a
    grow-only push (the new slots are already zero by storage default).  Then sets length to `L+1`.
    `.revert`s only if evaluating the array ref does.  It `.error`s (a stuck, ill-formed program)
    when the target isn't a dynamic array, the layout has no `.length`/element slot for it, the
    length slot doesn't hold an integer, or a compound value's shape doesn't match the element type —
    i.e. for a well-formed layout + matching value, `.revert` is the only non-`.ok` outcome. -/
def pushArray? (cfg : Config) (solm : Frame) (evm : EVM.State) (ref : StorageRef)
    (value : Option Value) : EvalResult EVM.State := do
  let (er, elemTy) <- resolveDynamicArrayRef? cfg solm evm ref
  let lenLoc <- EvalResult.ofOption .storageError
    (cfg.storage.layout { er with steps := er.steps ++ [.length] })
  match storageLocLoad evm lenLoc with
  | .int len => do
      let evm1 <- match value with
        | some v =>
            writeStorage? cfg evm
              { er with steps := er.steps ++ [.aindex (.int len)] } elemTy v
        | none => pure evm
      EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int (len + 1)))
  | _ => .error .storageError

/-- `arr.pop()`: remove the last element of the dynamic array named by `ref`.  Reverts when the
    array is empty (solc's `Panic(0x31)`).  Otherwise recursively clears the whole last element
    (per its declared type, via `clearStorage?` — so nested arrays/structs are fully zeroed) and
    sets the length to `L-1`. -/
def popArray? (cfg : Config) (solm : Frame) (evm : EVM.State) (ref : StorageRef)
    : EvalResult EVM.State := do
  let (er, elemTy) <- resolveDynamicArrayRef? cfg solm evm ref
  let lenLoc <- EvalResult.ofOption .storageError
    (cfg.storage.layout { er with steps := er.steps ++ [.length] })
  match storageLocLoad evm lenLoc with
  | .int len =>
      if len ≤ 0 then .revert
      else do
        let evm1 <- clearStorage? cfg evm
          { er with steps := er.steps ++ [.aindex (.int (len - 1))] } elemTy
        EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int (len - 1)))
  | _ => .error .storageError

/-- `delete x`: reset the storage at `ref` to its zero value, recursively per its declared type
    (`clearStorage?` — a dynamic array becomes empty, a struct/array is fully zeroed).  `.revert`s
    only if evaluating the ref does; `.error`s on an ill-formed layout/type. -/
def deleteStorage? (cfg : Config) (solm : Frame) (evm : EVM.State) (ref : StorageRef)
    : EvalResult EVM.State := do
  let (er, ty) <- resolveStorageRef? cfg solm evm ref
  clearStorage? cfg evm er ty

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
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals (true, evm', out) ->
      cfg.externalABI.decode? name out = some value ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar)
        (.ok { solm with locals := solm.locals.insert retVar value } evm')
  | externalCallFailure :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals (false, evm', out) ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar) .reverted
  | externalCallReturnDecodeRevert :
      -- The sub-call *succeeds* (`z = true`) but the returned bytes do not ABI-decode to the
      -- expected return value (`decode? = none`).  The caller's solc-generated return decoder then
      -- reverts (`if slt(returndatasize, 32) { revert }`), so the whole statement reverts.
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals (true, evm', out) ->
      cfg.externalABI.decode? name out = none ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar) .reverted
  | externalCallReceiverRevert :
      evalExpr? cfg solm evm receiver = .revert ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar) .reverted
  | externalCallSendRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .revert ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar) .reverted
  | externalCallArgsRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .revert ->
      ExecStmt cfg solm evm (.externalCall receiver name eth args retVar) .reverted
  | lowLevelCallSuccess :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExpr? cfg solm evm cdata = .ok (.bytes calldata) ->
      callViaEVM evm (EVM.address target) sendVal calldata (true, evm', out) ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar)
        (.ok { solm with locals := (solm.locals.insert okVar (.bool true)).insert dataVar (.bytes out) } evm')
  | lowLevelCallFailure :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExpr? cfg solm evm cdata = .ok (.bytes calldata) ->
      callViaEVM evm (EVM.address target) sendVal calldata (false, evm', out) ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar)
        (.ok { solm with locals := (solm.locals.insert okVar (.bool false)).insert dataVar (.bytes out) } evm')
  | lowLevelCallReceiverRevert :
      evalExpr? cfg solm evm receiver = .revert ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar) .reverted
  | lowLevelCallSendRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .revert ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar) .reverted
  | lowLevelCallDataRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExpr? cfg solm evm cdata = .revert ->
      ExecStmt cfg solm evm (.lowLevelCall receiver eth cdata okVar dataVar) .reverted
  | checkedCallSuccess :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals (true, evm', out) ->
      cfg.externalABI.decode? name out = some value ->
      ExecBlock cfg { solm with locals := solm.locals.insert retVar value } evm' onSuccess result ->
      ExecStmt cfg solm evm (.checkedCall receiver name eth args retVar onSuccess errVar onFail) result
  | checkedCallFail :
      -- callee reverted: bind the raw returndata to `errVar` and run `onFail`.  The per-contract spec
      -- decides there (via `ite` on `errVar`) whether to recover or re-revert (`require false`).
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals (false, evm', out) ->
      ExecBlock cfg { solm with locals := solm.locals.insert errVar (.bytes out) } evm' onFail result ->
      ExecStmt cfg solm evm (.checkedCall receiver name eth args retVar onSuccess errVar onFail) result
  | checkedCallReceiverRevert :
      evalExpr? cfg solm evm receiver = .revert ->
      ExecStmt cfg solm evm (.checkedCall receiver name eth args retVar onSuccess errVar onFail) .reverted
  | checkedCallSendRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .revert ->
      ExecStmt cfg solm evm (.checkedCall receiver name eth args retVar onSuccess errVar onFail) .reverted
  | checkedCallArgsRevert :
      evalExpr? cfg solm evm receiver = .ok (.address target) ->
      evalExpr? cfg solm evm eth = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .revert ->
      ExecStmt cfg solm evm (.checkedCall receiver name eth args retVar onSuccess errVar onFail) .reverted
  | newSuccess :
      evalExpr? cfg solm evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      newViaEVM cfg evm name sendVal argVals (addr, evm', true) ->
      ExecStmt cfg solm evm (.new name valExpr args retVar)
        (.ok { solm with locals := solm.locals.insert retVar (.address addr) } evm')
  | newRevert :
      -- A failed creation reverts the caller, unlike a low-level external call.
      evalExpr? cfg solm evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .ok argVals ->
      newViaEVM cfg evm name sendVal argVals (addr, evm', false) ->
      ExecStmt cfg solm evm (.new name valExpr args retVar) .reverted
  | newValueRevert :
      evalExpr? cfg solm evm valExpr = .revert ->
      ExecStmt cfg solm evm (.new name valExpr args retVar) .reverted
  | newArgsRevert :
      evalExpr? cfg solm evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg solm evm args = .revert ->
      ExecStmt cfg solm evm (.new name valExpr args retVar) .reverted
  | return :
      evalExpr? cfg solm evm expr = .ok value ->
      ExecStmt cfg solm evm (.return expr) (.returned solm evm (some value))
  | returnRevert :
      evalExpr? cfg solm evm expr = .revert ->
      ExecStmt cfg solm evm (.return expr) .reverted
  | break :
      ExecStmt cfg solm evm .break (.break solm evm)
  | continue :
      ExecStmt cfg solm evm .continue (.continue solm evm)

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
