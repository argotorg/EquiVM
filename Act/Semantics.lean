import Act.Storage
import Act.Value

namespace Act

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

inductive VarOrigin where
  | local
  | storage
  deriving DecidableEq, Repr, Inhabited

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
  | .elem (.int _), .int _ => some v
  | .contract _, .address _ => some v
  | .struct expected _, .struct actual _ =>
      if expected = actual then some v else none
  | .array _ _, .array _ => some v
  | .dynamicArray _, .array _ => some v
  | _, _ => none

/-- Act evaluation errors. Should never happen in well-formed programs -/
inductive EvalError where
  | unboundVariable
  | typeError
  | storageError
  deriving DecidableEq, Repr, Inhabited

/-- Result of evaluating an Act expression:
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
    | .var _ => 1
    | .env _ => 1
    | .storage slot => slotEvalSize slot + 1
    | .field base _ => exprEvalSize base + 1
    | .aindex base idx => exprEvalSize base + exprEvalSize idx + 1
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

mutual

def evalStorageRefStep (cfg : Config) (act : Frame) (evm : EVM.State) (step : StorageRefStep) : EvalResult EvaledStorageRefStep :=
  match step with
  | .field name => pure (.field name)
  | .mindex expr => do
    let index <- evalExpr? cfg act evm expr
    let indexKey <- EvalResult.ofOption .typeError (valueToKey? index)
    pure (.mindex indexKey)
  | .aindex expr => do
    let index <- evalExpr? cfg act evm expr
    let indexKey <- EvalResult.ofOption .typeError (valueToKey? index)
    pure (.aindex indexKey)
  termination_by (slotStepEvalSize step, 0)
  decreasing_by
    all_goals simp [slotStepEvalSize]
    all_goals omega

def evalStorageRef (cfg : Config) (act : Frame) (evm : EVM.State) (slot : StorageRef) : EvalResult EvaledStorageRef := do
  let steps <- EvalResult.seqList (slot.steps.map (evalStorageRefStep cfg act evm))
  pure { base := slot.base, steps := steps }
  termination_by (slotEvalSize slot, 0)
  decreasing_by
    rename_i step hin
    all_goals simp [slotEvalSize]
    apply Prod.Lex.left
    apply lt_trans (stepSize_lt_stepsSize slot step (hin))
    omega

def updateLocalPath? (cfg : Config) (act : Frame) (evm : EVM.State)
    (root : Value) (steps : List StorageRefStep) (value : Value) : EvalResult Value :=
  match steps with
  | [] => pure value
  | .field name :: rest => do
      let child <- EvalResult.ofOption .typeError (lookupField? root name)
      let child' <- updateLocalPath? cfg act evm child rest value
      EvalResult.ofOption .typeError (updateField? root name child')
  | .mindex expr :: rest => do
      let idx <- evalExpr? cfg act evm expr
      let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
      let child' <- updateLocalPath? cfg act evm child rest value
      EvalResult.ofOption .typeError (updateIndex? root idx child')
  | .aindex expr :: rest => do
      let idx <- evalExpr? cfg act evm expr
      let child <- EvalResult.ofOption .typeError (lookupIndex? root idx)
      let child' <- updateLocalPath? cfg act evm child rest value
      EvalResult.ofOption .typeError (updateIndex? root idx child')
  termination_by (slotStepsEvalSize steps, 0)
  decreasing_by
    all_goals simp [slotStepsEvalSize, slotStepEvalSize]
    all_goals omega

def assignStorageRef? (cfg : Config) (act : Frame) (evm : EVM.State)
    (slot : StorageRef) (value : Value) : EvalResult (Frame × EVM.State) :=
  match act.locals.get? slot.base with
  | some root => do
      let root' <- updateLocalPath? cfg act evm root slot.steps value
      pure ({ act with locals := act.locals.insert slot.base root' }, evm)
  | none =>
    match evalStorageRef cfg act evm slot with
    | .ok evaledStorageRef => do
      let loc <- EvalResult.ofOption .storageError (cfg.storage.layout evaledStorageRef)
      let evm' <- EvalResult.ofOption .storageError (storageLocStore evm loc value)
      pure (act, evm')
    | .revert => .revert
    | .error e => .error e

def evalExpr? (cfg : Config) (act : Frame) (evm : EVM.State) :
    Expr -> EvalResult Value
  | .intLit n => pure (.int n)
  | .boolLit b => pure (.bool b)
  | .var name => EvalResult.ofOption .unboundVariable (act.locals.get? name)
  | .env var => pure (envValue evm var)
  | .storage slot =>
      match evalStorageRef cfg act evm slot with
      | .ok evaledStorageRef => do
          let loc <- EvalResult.ofOption .storageError (cfg.storage.layout evaledStorageRef)
          pure (storageLocLoad evm loc)
      | .revert => .revert
      | .error e => .error e
  | .field base name => do
      let baseValue <- evalExpr? cfg act evm base
      EvalResult.ofOption .typeError (lookupField? baseValue name)
  | .aindex base idxExpr => do
      let baseValue <- evalExpr? cfg act evm base
      let idx <- evalExpr? cfg act evm idxExpr
      EvalResult.ofOption .typeError (lookupIndex? baseValue idx)
  | .cast expr ty => do /- TODO do we really need to have casting? -/
      let value <- evalExpr? cfg act evm expr
      EvalResult.ofOption .typeError (castValue? value ty)
  | .addrOf expr => do
      let value <- evalExpr? cfg act evm expr
      match value with
      | .address a => pure (.address a)
      | _ => .error .typeError
  | .unary op expr => do
      let value <- evalExpr? cfg act evm expr
      EvalResult.ofOption .typeError (evalUnaryOp? op value)
  | .binary op lhs rhs => do
      let lhsValue <- evalExpr? cfg act evm lhs
      let rhsValue <- evalExpr? cfg act evm rhs
      evalBinaryOp? op lhsValue rhsValue
  | .ite cond thenExpr elseExpr => do
      let condValue <- evalExpr? cfg act evm cond
      match condValue with
      | .bool true => evalExpr? cfg act evm thenExpr
      | .bool false => evalExpr? cfg act evm elseExpr
      | _ => .error .typeError
  | .inRange intType expr => do
      let value <- evalExpr? cfg act evm expr
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

def evalExprs? (cfg : Config) (act : Frame) (evm : EVM.State)
    (exprs : List Expr) : EvalResult (List Value) :=
  match exprs with
  | [] => pure []
  | expr :: rest => do
      let value <- evalExpr? cfg act evm expr
      let values <- evalExprs? cfg act evm rest
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
  if bytes.isEmpty then
    some .unit
  else
    some (.int (Ethereum.fromByteArrayBigEndian (bytes.extract 0 32)))
    -- Check if fromByteArrayBigEndian is correct here

def defaultExternalCallABI : ExternalCallABI :=
  { encode? := defaultEncodeCall?, decode? := defaultDecodeReturn? }

inductive externalCallViaEVM (cfg : Config) (evm : EVM.State) (target : EVM.Address)
    (name : Ident) (value : ℤ) (args : List Value) :
    (Bool × EVM.State × EVM.Bytes) → Prop where
  | callMade :
      Except.ok calldata = (cfg.externalABI.encode? name args).elim (.error Ethereum.EVM.ExecutionException.InvalidInstruction) pure
      → valueWord = EVM.wordOfInt value
      → (∃ callGas refunds accessedStorageKeys,
        -- We need to existentially quantify over fields whose value we
        -- do not track accurately but which the bytecode can change.
        -- The rest of substate fields we should be able to track by act as well,
        -- but we may decide not to
          let A_exist := { ((evm.addAccessedAccount target) |>.substate ) with
                      refundBalance := refunds
                      accessedStorageKeys := accessedStorageKeys }
          (cA', σ', _, A', z, o)
            = Ethereum.EVM.Θ
            evm.executionEnv.blobVersionedHashes
            evm.createdAccounts
            evm.genesisBlockHeader
            evm.blocks
            evm.accountMap
            evm.σ₀
            A_exist
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
      → externalCallViaEVM cfg evm target name value args (z, evm', o)

  | callNotMade :
      A' = ((evm.addAccessedAccount target) |>.substate )
      → evm' = { evm with substate := A' }
      → (¬ (EVM.wordOfInt value ≤ (evm.accountMap.find? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
         ∧ evm.executionEnv.depth ≠ 1024))
      → externalCallViaEVM cfg evm target name value args (false, evm', ByteArray.empty)

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

mutual

inductive ExecStmt (cfg : Config) :
    Frame -> EVM.State -> Stmt -> ExecResult -> Prop where
  | letDecl :
      evalExpr? cfg act evm expr = .ok value ->
      ExecStmt cfg act evm (.letDecl name ty expr)
        (.ok { act with locals := act.locals.insert name value } evm)
  | letDeclRevert :
      evalExpr? cfg act evm expr = .revert ->
      ExecStmt cfg act evm (.letDecl name ty expr) .reverted
  | assign :
      evalExpr? cfg act evm expr = .ok value ->
      assignStorageRef? cfg act evm slot value = .ok (act', evm') ->
      ExecStmt cfg act evm (.assign slot expr) (.ok act' evm')
  | assignExprRevert :
      evalExpr? cfg act evm expr = .revert ->
      ExecStmt cfg act evm (.assign slot expr) .reverted
  | assignStoreRevert :
      evalExpr? cfg act evm expr = .ok value ->
      assignStorageRef? cfg act evm slot value = .revert ->
      ExecStmt cfg act evm (.assign slot expr) .reverted
  | requireTrue {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool true) ->
      ExecStmt cfg act evm (.require condExpr) (.ok act evm)
  | requireFalse {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool false) ->
      ExecStmt cfg act evm (.require condExpr) .reverted
  | requireRevert {condExpr} :
      evalExpr? cfg act evm condExpr = .revert ->
      ExecStmt cfg act evm (.require condExpr) .reverted
  | whileFalse {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool false) ->
      ExecStmt cfg act evm (.while condExpr body) (.ok act evm)
  | whileCondRevert {condExpr} :
      evalExpr? cfg act evm condExpr = .revert ->
      ExecStmt cfg act evm (.while condExpr body) .reverted
  | whileTrue {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool true) ->
      ExecBlock cfg act evm body (.ok act' evm') ->
      ExecStmt cfg act' evm' (.while condExpr body) result ->
      ExecStmt cfg act evm (.while condExpr body) result
  | whileReturn {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool true) ->
      ExecBlock cfg act evm body (.returned act' evm' value) ->
      ExecStmt cfg act evm (.while condExpr body) (.returned act' evm' value)
  | whileRevert {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool true) ->
      ExecBlock cfg act evm body .reverted ->
      ExecStmt cfg act evm (.while condExpr body) .reverted
  | whileBreak {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool true) ->
      ExecBlock cfg act evm body (.break act' evm') ->
      ExecStmt cfg act evm (.while condExpr body) (.ok act' evm')
  | whileContinue {condExpr} :
      evalExpr? cfg act evm condExpr = .ok (.bool true) ->
      ExecBlock cfg act evm body (.continue act' evm') ->
      ExecStmt cfg act' evm' (.while condExpr body) result ->
      ExecStmt cfg act evm (.while condExpr body) result
  | internalCallReturn :
      evalExprs? cfg act evm args = .ok argVals ->
      lookupCallable? act.contract name = some callee ->
      bindParams? callee.params argVals = some locals ->
      ExecFuncBody cfg { act with locals := locals } evm callee.body
        (.returned calleeAct calleeEvm value) ->
      ExecStmt cfg act evm (.internalCall name args retVar)
        (.ok (resumeAfterInternalCall act retVar value) calleeEvm)
  | internalCallRevert :
      evalExprs? cfg act evm args = .ok argVals ->
      lookupCallable? act.contract name = some callee ->
      bindParams? callee.params argVals = some locals ->
      ExecFuncBody cfg { act with locals := locals } evm callee.body .reverted ->
      ExecStmt cfg act evm (.internalCall name args retVar) .reverted
  | internalCallArgsRevert :
      evalExprs? cfg act evm args = .revert ->
      ExecStmt cfg act evm (.internalCall name args retVar) .reverted
  | externalCallSuccess :
      evalExpr? cfg act evm receiver = .ok (.address target) ->
      evalExpr? cfg act evm eth = .ok (.int sendVal) ->
      evalExprs? cfg act evm args = .ok argVals ->
      externalCallViaEVM cfg evm (EVM.address target) name sendVal argVals (true, evm', out) ->
      cfg.externalABI.decode? name out = some value ->
      ExecStmt cfg act evm (.externalCall receiver name eth args retVar)
        (.ok { act with locals := act.locals.insert retVar value } evm')
  | externalCallFailure :
      evalExpr? cfg act evm receiver = .ok (.address target) ->
      evalExpr? cfg act evm eth = .ok (.int sendVal) ->
      evalExprs? cfg act evm args = .ok argVals ->
      externalCallViaEVM cfg evm (EVM.address target) name sendVal argVals (false, evm', out) ->
      ExecStmt cfg act evm (.externalCall receiver name eth args retVar) .reverted
  | externalCallReceiverRevert :
      evalExpr? cfg act evm receiver = .revert ->
      ExecStmt cfg act evm (.externalCall receiver name eth args retVar) .reverted
  | externalCallSendRevert :
      evalExpr? cfg act evm receiver = .ok (.address target) ->
      evalExpr? cfg act evm eth = .revert ->
      ExecStmt cfg act evm (.externalCall receiver name eth args retVar) .reverted
  | externalCallArgsRevert :
      evalExpr? cfg act evm receiver = .ok (.address target) ->
      evalExpr? cfg act evm eth = .ok (.int sendVal) ->
      evalExprs? cfg act evm args = .revert ->
      ExecStmt cfg act evm (.externalCall receiver name eth args retVar) .reverted
      /- do we want to express a low-level .call? -/
  | newSuccess :
      evalExpr? cfg act evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg act evm args = .ok argVals ->
      newViaEVM cfg evm name sendVal argVals (addr, evm', true) ->
      ExecStmt cfg act evm (.new name valExpr args retVar)
        (.ok { act with locals := act.locals.insert retVar (.address addr) } evm')
  | newRevert :
      -- A failed creation reverts the caller, unlike a low-level external call.
      evalExpr? cfg act evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg act evm args = .ok argVals ->
      newViaEVM cfg evm name sendVal argVals (addr, evm', false) ->
      ExecStmt cfg act evm (.new name valExpr args retVar) .reverted
  | newValueRevert :
      evalExpr? cfg act evm valExpr = .revert ->
      ExecStmt cfg act evm (.new name valExpr args retVar) .reverted
  | newArgsRevert :
      evalExpr? cfg act evm valExpr = .ok (.int sendVal) ->
      evalExprs? cfg act evm args = .revert ->
      ExecStmt cfg act evm (.new name valExpr args retVar) .reverted
  | return :
      evalExpr? cfg act evm expr = .ok value ->
      ExecStmt cfg act evm (.return expr) (.returned act evm (some value))
  | returnRevert :
      evalExpr? cfg act evm expr = .revert ->
      ExecStmt cfg act evm (.return expr) .reverted
  | break :
      ExecStmt cfg act evm .break (.break act evm)
  | continue :
      ExecStmt cfg act evm .continue (.continue act evm)

inductive ExecBlock (cfg : Config) :
    Frame -> EVM.State -> List Stmt -> ExecResult -> Prop where
  | nil :
      ExecBlock cfg act evm [] (.ok act evm)
  | consNormal :
      ExecStmt cfg act evm stmt (.ok act' evm') ->
      ExecBlock cfg act' evm' stmts result ->
      ExecBlock cfg act evm (stmt :: stmts) result
  | consReturn :
      ExecStmt cfg act evm stmt (.returned act' evm' value) ->
      ExecBlock cfg act evm (stmt :: stmts) (.returned act' evm' value)
  | consRevert :
      ExecStmt cfg act evm stmt .reverted ->
      ExecBlock cfg act evm (stmt :: stmts) .reverted
  | consBreak :
      ExecStmt cfg act evm stmt (.break act' evm') ->
      ExecBlock cfg act evm (stmt :: stmts) (.break act' evm')
  | consContinue :
      ExecStmt cfg act evm stmt (.continue act' evm') ->
      ExecBlock cfg act evm (stmt :: stmts) (.continue act' evm')

inductive ExecFuncBody (cfg : Config) :
    Frame -> EVM.State -> List Stmt -> ExecResult -> Prop where
  | execBlockOK :
      ExecBlock cfg act evm body (.ok act' evm') ->
      ExecFuncBody cfg act evm body (.returned act' evm' none)
  | execBlockRet :
      ExecBlock cfg act evm body (.returned act' evm' value) ->
      ExecFuncBody cfg act evm body (.returned act' evm' value)
  | execBlockRevert :
      ExecBlock cfg act evm body .reverted ->
      ExecFuncBody cfg act evm body .reverted
  -- A `break`/`continue` that occurs outside a loop is malformed. We have to handle it so that ExecFuncBody is never stuck.
  | execBlockBreak :
      ExecBlock cfg act evm body (.break act' evm') ->
      ExecFuncBody cfg act evm body (.returned act' evm' none)
  | execBlockContinue :
      ExecBlock cfg act evm body (.continue act' evm') ->
      ExecFuncBody cfg act evm body (.returned act' evm' none)

end

def ExecContractBody (cfg : Config) (contract : ContractDecl) (evm : EVM.State)
    (locals : Store) (body : Body) (result : ExecResult) : Prop :=
  ExecFuncBody cfg { contract := contract, locals := locals } evm body result
