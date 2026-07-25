import Solm.Semantics.Types
import Solm.Semantics.ValueOps

/-! Structured storage operations: typed read/write/clear/default over the opaque layout. -/

namespace Solm

open ABI

/-- The declared `StorageType` reached by following one evaled step from a value of type `t`. -/
def storageTypeStep? : StorageType -> EvaledStorageRefStep -> Option StorageType
  | .struct _ fields, .field name => (fields.find? (fun f => f.1 == name)).map (·.2)
  | .tuple ts, .tupleElem k => ts[k]?
  | .mapping _ v, .mindex _ => some v
  | .array t' _, .aindex _ => some t'
  | .dynamicArray t', .aindex _ => some t'
  | .bytes, .aindex _ => some (.elem (.int (.uint ⟨8, by decide⟩)))
  | .string, .aindex _ => some (.elem (.int (.uint ⟨8, by decide⟩)))
  | _, _ => none

/-- The declared `StorageType` of whatever the evaled ref `er` points at, walked from the contract's
    storage declarations (the type tree carried by the frame, independent of the opaque layout). -/
def storageTypeAt? (decls : List StorageDecl) (er : EvaledStorageRef) : Option StorageType := do
  let baseTy <- (decls.find? (fun d => d.name == er.base)).map (·.ty)
  er.steps.foldlM storageTypeStep? baseTy

def storageNatResultToEval : StorageReadResult Nat -> EvalResult Nat
  | .ok n => .ok n
  | .revert => .revert
  | .error => .error .storageError

def readStorageBytesLength? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    EvalResult Nat :=
  match cfg.storage.readBytesLength er evm with
  | some result => storageNatResultToEval result
  | none => .error .storageError

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
      match cfg.storage.layout { base := base, steps := pre ++ [.length] } evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
          | _ => .error .storageError
      | none => .error .storageError
  | some (.dynamicArray _), _ => .error .typeError
  | some (.bytes), .int iv
  | some (.string), .int iv =>
      match readStorageBytesLength? cfg evm { base := base, steps := pre } with
      | .ok len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
      | .revert => .revert
      | .error e => .error e
  | some (.bytes), _ | some (.string), _ => .error .typeError
  | some _, _ => .error .typeError
  | none, _ => .error .storageError

def storagePrepareResultToEval : StorageReadResult EVM.State -> EvalResult EVM.State
  | .ok evm => .ok evm
  | .revert => .revert
  | .error => .error .storageError

def storageValueResultToEval : StorageReadResult Value -> EvalResult Value
  | .ok v => .ok v
  | .revert => .revert
  | .error => .error .storageError

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
      match cfg.storage.layout er evm with
      | some loc => EvalResult.ofOption .storageError (storageLocStore evm loc (.int 0))
      | none => .error .storageError
  | .mapping _ _ => .ok evm
  | .struct _ fields => clearFields? cfg evm er fields
  | .tuple ts => clearTupleElems? cfg evm er 0 ts
  | .array t' n => clearArrayElems? cfg evm er t' n
  | .dynamicArray t' =>
      match cfg.storage.layout { er with steps := er.steps ++ [.length] } evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len =>
              match clearArrayElems? cfg evm er t' len.toNat with
              | .ok evm1 => EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int 0))
              | r => r
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes =>
      match cfg.storage.clearValue? er .bytes evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | .string =>
      match cfg.storage.clearValue? er .string evm with
      | some result => storagePrepareResultToEval result
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
      match cfg.storage.layout er evm with
      | some loc => EvalResult.ofOption .storageError (storageLocStore evm loc v)
      | none => .error .storageError
  | .struct _ ftypes, .struct _ fvals => writeFields? cfg evm er ftypes fvals
  | .tuple ts, .tuple vs => writeTupleElems? cfg evm er 0 ts vs
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
        (cfg.storage.layout { er with steps := er.steps ++ [.length] } evm)
      EvalResult.ofOption .storageError (storageLocStore evm1 lenLoc (.int vs.length))
  | .bytes, .bytes bs =>
      match cfg.storage.writeValue? er .bytes (.bytes bs) evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | .string, .bytes bs =>
      match cfg.storage.writeValue? er .string (.bytes bs) evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
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
      match cfg.storage.layout er evm with
      | some loc => .ok (storageLocLoad evm loc)
      | none => .error .storageError
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let fvals <- readFields? cfg evm er fields
      pure (.struct name fvals)
  | .tuple ts => do
      let vs <- readTupleElems? cfg evm er 0 ts
      pure (.tuple vs)
  | .array t' n => do
      let vs <- readArrayElems? cfg evm er t' 0 n
      pure (.array vs)
  | .dynamicArray t' =>
      match cfg.storage.layout { er with steps := er.steps ++ [.length] } evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int len => do
              let vs <- readArrayElems? cfg evm er t' 0 len.toNat
              pure (.array vs)
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes =>
      match cfg.storage.readValue? er .bytes evm with
      | some result => storageValueResultToEval result
      | none => .error .storageError
  | .string =>
      match cfg.storage.readValue? er .string evm with
      | some result => storageValueResultToEval result
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
  | .elem (.bytes n) => pure (.int (fixedBytesSize n))
  | .dynamicArray _ =>
      match cfg.storage.layout { er with steps := er.steps ++ [.length] } evm with
      | some lenLoc =>
          match storageLocLoad evm lenLoc with
          | .int n => pure (.int n)
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes | .string => do
      let len <- readStorageBytesLength? cfg evm er
      pure (.int len)
  | _ => .error .typeError

mutual
def defaultValue? : StorageType -> EvalResult Value
  | .elem (.bool) => pure (.bool false)
  | .elem (.address) => pure (.address (.ofNat 0))
  | .elem (.bytes n) => pure (.fixedBytes n (List.replicate (n.val + 1) 0))
  | .elem _ => pure (.int 0)
  | .contract _ => pure (.address (.ofNat 0))
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let values <- defaultFields? fields
      pure (.struct name values)
  | .tuple ts => do
      let values <- defaultValues? ts
      pure (.tuple values)
  | .array elemTy n => do
      let value <- defaultValue? elemTy
      pure (.array (List.replicate n value))
  | .dynamicArray _ => pure (.array [])
  | .bytes | .string => pure (.bytes ByteArray.empty)
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

end Solm
