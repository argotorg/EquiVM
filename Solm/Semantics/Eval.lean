import ABI.Decode
import Solm.Semantics.StorageOps

/-! The expression evaluator: termination measures and the `evalExpr?` mutual block. -/

namespace Solm

open ABI

mutual
  /-- Termination measure for the expression-evaluating mutual block below
      (`evalExpr?` and related helpers). -/
  def exprEvalSize : Expr → Nat
    | .intLit _ => 1
    | .boolLit _ => 1
    | .bytesLit _ => 1
    | .newBytes lenExpr => exprEvalSize lenExpr + 1
    | .newArray _ lenExpr => exprEvalSize lenExpr + 1
    | .structLit _ fields => structFieldsEvalSize fields + 1
    | .arrayLit elems => exprListEvalSize elems + 1
    | .tupleLit elems => exprListEvalSize elems + 1
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
    | .index base idx => exprEvalSize base + exprEvalSize idx + 1
    | .ite cond thenExpr elseExpr =>
        exprEvalSize cond + exprEvalSize thenExpr + exprEvalSize elseExpr + 1
    | .keccak256 e => exprEvalSize e + 1
    | .abiEncodePacked args => typedArgsEvalSize args + 1
    | .abiEncodeCall _ args => exprListEvalSize args + 1
    | .abiDecode _ e => exprEvalSize e + 1
    | .extCodeSize e => exprEvalSize e + 1
    | .extCodePrefix addrE lenE => exprEvalSize addrE + exprEvalSize lenE + 1
    | .tupleGet e _ => exprEvalSize e + 1
    | .blockhash e => exprEvalSize e + 1
    | .balanceOf e => exprEvalSize e + 1
    | .extCodeHash e => exprEvalSize e + 1
    | .fixedBytesLit _ _ => 1
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

  def exprListEvalSize : List Expr → Nat
    | [] => 1
    | e :: rest => exprEvalSize e + exprListEvalSize rest + 1
  termination_by es => (sizeOf es, 0)
  decreasing_by
    all_goals simp_wf
    all_goals decreasing_tactic

  def structFieldsEvalSize : List (Ident × Expr) → Nat
    | [] => 1
    | (_, e) :: rest => exprEvalSize e + structFieldsEvalSize rest + 1
  termination_by fs => (sizeOf fs, 0)
  decreasing_by
    all_goals simp_wf
    all_goals decreasing_tactic

  def typedArgsEvalSize : List (ABIType × Expr) → Nat
    | [] => 1
    | (_, e) :: rest => exprEvalSize e + typedArgsEvalSize rest + 1
  termination_by as => (sizeOf as, 0)
  decreasing_by
    all_goals simp_wf
    all_goals decreasing_tactic
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
      | .fixedBytes n bytes, .int i =>
          match evalFixedBytesIndex? n bytes i with
          | .ok child => readLocalPath? cfg solm evm child rest
          | .revert => .revert
          | .error e => .error e
      | .bytes bytes, .int i =>
          match evalByteIndex? bytes.toList i with
          | .ok child => readLocalPath? cfg solm evm child rest
          | .revert => .revert
          | .error e => .error e
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
    | .struct _ _ | .array _ | .bytes _ => do
      -- whole-array / whole-struct assignment: write every slot by the declared type
      let evm' <- writeStorage? cfg evm evaledStorageRef ty value
      pure (solm, evm')
    | _ => do
      -- scalar leaf: a single whole/partial-slot store
      let loc <- EvalResult.ofOption .storageError (cfg.storage.layout evaledStorageRef evm)
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
  | .structLit name fields => do
      let fvals <- evalStructFields? cfg solm evm fields
      pure (.struct name fvals)
  | .arrayLit elems => do
      let vals <- evalExprList? cfg solm evm elems
      pure (.array vals)
  | .tupleLit elems => do
      let vals <- evalExprList? cfg solm evm elems
      pure (.tuple vals)
  | .bytesSlice baseE startE endE => do
      let baseV <- evalExpr? cfg solm evm baseE
      let startV <- evalExpr? cfg solm evm startE
      let endV <- evalExpr? cfg solm evm endE
      match baseV, startV, endV with
      | .bytes ba, .int s, .int e => sliceBytes? ba s e
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
              | .fixedBytes n _ => pure (.int (fixedBytesSize n))
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
  | .binary .and lhs rhs => do
      match <- evalExpr? cfg solm evm lhs with
      | .bool false => pure (.bool false)
      | .bool true =>
          (match <- evalExpr? cfg solm evm rhs with
           | .bool b => pure (.bool b)
           | _ => .error .typeError)
      | _ => .error .typeError
  | .binary .or lhs rhs => do
      match <- evalExpr? cfg solm evm lhs with
      | .bool true => pure (.bool true)
      | .bool false =>
          (match <- evalExpr? cfg solm evm rhs with
           | .bool b => pure (.bool b)
           | _ => .error .typeError)
      | _ => .error .typeError
  | .binary op lhs rhs => do
      let lhsValue <- evalExpr? cfg solm evm lhs
      let rhsValue <- evalExpr? cfg solm evm rhs
      evalBinaryOp? op lhsValue rhsValue
  | .index base idx => do
      let baseValue <- evalExpr? cfg solm evm base
      let idxValue <- evalExpr? cfg solm evm idx
      evalIndex? baseValue idxValue
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
  | .keccak256 e => do
      let value <- evalExpr? cfg solm evm e
      match value with
      -- Keccak-256 of the dynamic bytes, as a `bytes32` value; same `ffi.KEC` as the EVM opcode.
      | .bytes ba => pure (.fixedBytes ⟨31, by decide⟩ (ffi.KEC ba).toList)
      | _ => .error .typeError
  | .abiEncodePacked args => do
      let bytes <- evalPackedArgs? cfg solm evm args
      pure (.bytes (ByteArray.mk bytes.toArray))
  | .abiEncodeCall name args => do
      let values <- evalExprList? cfg solm evm args
      let bytes <- EvalResult.ofOption .typeError (cfg.externalABI.encode? name values)
      pure (.bytes bytes)
  | .abiDecode ty e => do
      let value <- evalExpr? cfg solm evm e
      match value with
      | .bytes bytes =>
          match ABI.decodeReturnValueWithMode? cfg.abiDecodeMode ty bytes with
          | some decoded => pure decoded
          | none => .revert
      | _ => .error .typeError
  | .extCodeSize e => do
      let value <- evalExpr? cfg solm evm e
      match value with
      -- EXTCODESIZE: the deployed code size at `a`; 0 for a non-existent account or an EOA.
      -- Mirrors `Ethereum.State.extCodeSize` (which the EVM's EXTCODESIZE opcode dispatches to).
      | .address a =>
          pure (.int (Int.ofNat
            (EVM.Word.ofNat ((evm.lookupAccount a).option 0 (fun acc => acc.code.size))).toNat))
      | _ => .error .typeError
  | .extCodePrefix addrE lenE => do
      let addrV <- evalExpr? cfg solm evm addrE
      let lenV <- evalExpr? cfg solm evm lenE
      match addrV, lenV with
      | .address a, .int n =>
          if n < 0 then .error .typeError
          else
            let code := (evm.lookupAccount a).option .empty (fun acc => acc.code)
            let codePrefix := code.extract 0 n.toNat
            pure (.bytes (codePrefix ++
              ByteArray.mk (Array.replicate (n.toNat - codePrefix.size) (0 : UInt8))))
      | _, _ => .error .typeError
  | .tupleGet e i => do
      let v <- evalExpr? cfg solm evm e
      tupleGetValue? v i
  -- BLOCKHASH: mirrors `Ethereum.State.blockHash` (256-block window; current/future → 0), as bytes32.
  | .blockhash e => do
      let v <- evalExpr? cfg solm evm e
      match v with
      | .int n => if n < 0 then .error .typeError
                  else pure (.fixedBytes ⟨31, by decide⟩
                    (EVM.Word.toBytesBE (evm.blockHash (EVM.Word.ofNat n.toNat))))
      | _ => .error .typeError
  -- BALANCE: mirrors `Ethereum.State.balance` (absent account → 0).
  | .balanceOf e => do
      let v <- evalExpr? cfg solm evm e
      match v with
      | .address a =>
          pure (.int (Int.ofNat ((evm.lookupAccount a).option (EVM.Word.ofNat 0) (·.balance)).toNat))
      | _ => .error .typeError
  -- EXTCODEHASH: mirrors `Ethereum.State.extCodeHash` (dead account → 0), as bytes32.
  | .extCodeHash e => do
      let v <- evalExpr? cfg solm evm e
      match v with
      | .address a =>
          let h : EVM.Word :=
            if Ethereum.State.dead evm.accountMap a then ⟨0⟩
            else (evm.lookupAccount a).option ⟨0⟩ Ethereum.Account.codeHash
          pure (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE h))
      | _ => .error .typeError
  | .fixedBytesLit n bs => pure (.fixedBytes n bs)
  termination_by expr => (exprEvalSize expr, 0)
decreasing_by
  all_goals simp [exprEvalSize, slotEvalSize]
  all_goals omega

/-- Evaluate a list of expressions left to right (for `arrayLit` / tuple returns), short-circuiting
    on the first `revert`/`error`. -/
def evalExprList? (cfg : Config) (solm : Frame) (evm : EVM.State) :
    List Expr -> EvalResult (List Value)
  | [] => pure []
  | e :: rest => do
      let v <- evalExpr? cfg solm evm e
      let vs <- evalExprList? cfg solm evm rest
      pure (v :: vs)
termination_by es => (exprListEvalSize es, 0)
decreasing_by
  all_goals simp [exprListEvalSize]
  all_goals omega

/-- Evaluate a struct literal's named field expressions left to right (for `structLit`),
    short-circuiting on the first `revert`/`error`. -/
def evalStructFields? (cfg : Config) (solm : Frame) (evm : EVM.State) :
    List (Ident × Expr) -> EvalResult (List (Ident × Value))
  | [] => pure []
  | (name, e) :: rest => do
      let v <- evalExpr? cfg solm evm e
      let vs <- evalStructFields? cfg solm evm rest
      pure ((name, v) :: vs)
termination_by fs => (structFieldsEvalSize fs, 0)
decreasing_by
  all_goals simp [structFieldsEvalSize]
  all_goals omega

/-- Evaluate each `abi.encodePacked` operand left to right and concatenate its packed encoding,
    short-circuiting on the first `revert`/`error` (or a `.typeError` if a value cannot be packed). -/
def evalPackedArgs? (cfg : Config) (solm : Frame) (evm : EVM.State) :
    List (ABIType × Expr) -> EvalResult (List UInt8)
  | [] => pure []
  | (ty, e) :: rest => do
      let v <- evalExpr? cfg solm evm e
      let head <- EvalResult.ofOption .typeError (encodePackedValue? ty v)
      let tail <- evalPackedArgs? cfg solm evm rest
      pure (head ++ tail)
termination_by as => (typedArgsEvalSize as, 0)
decreasing_by
  all_goals simp [typedArgsEvalSize]
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

end Solm
