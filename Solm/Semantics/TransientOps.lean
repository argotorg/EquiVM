import Solm.Semantics.StorageOps

/-! Structured reads and writes against `Account.tstorage`.

Slot layout comes from `cfg.transient`.  Packed words go through `transientLocLoad` and
`transientLocStore`.  The operations follow the same cases as `StorageOps.lean`. -/

namespace Solm

open ABI

def declaredTransient (c : ContractDecl) (name : Ident) : Bool :=
  c.transient.any (fun d => d.name == name)

def readTransientBytesLength? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    EvalResult Nat :=
  match cfg.transient.readBytesLength er evm with
  | some result => storageNatResultToEval result
  | none => .error .storageError

/-- Bounds check for an index into a transient array, using `cfg.transient`. -/
def transientArrayIndexInBounds? (cfg : Config) (evm : EVM.State)
    (decls : List StorageDecl) (base : Ident) (pre : List EvaledStorageRefStep) (i : KeyValue) :
    EvalResult Unit :=
  match storageTypeAt? decls { base := base, steps := pre }, i with
  | some (.array _ n), .int iv =>
      if 0 ≤ iv ∧ iv < n then .ok () else .revert
  | some (.array _ _), _ => .error .typeError
  | some (.dynamicArray _), .int iv =>
      match cfg.transient.layout { base := base, steps := pre ++ [.length] } evm with
      | some lenLoc =>
          match transientLocLoad evm lenLoc with
          | .int len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
          | _ => .error .storageError
      | none => .error .storageError
  | some (.dynamicArray _), _ => .error .typeError
  | some (.bytes), .int iv
  | some (.string), .int iv =>
      match readTransientBytesLength? cfg evm { base := base, steps := pre } with
      | .ok len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
      | .revert => .revert
      | .error e => .error e
  | some (.bytes), _ | some (.string), _ => .error .typeError
  | some _, _ => .error .typeError
  | none, _ => .error .storageError

mutual
def clearTransientStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> EvalResult EVM.State
  | .elem _ | .contract _ =>
      match cfg.transient.layout er evm with
      | some loc => EvalResult.ofOption .storageError (transientLocStore evm loc (.int 0))
      | none => .error .storageError
  | .mapping _ _ => .ok evm
  | .struct _ fields => clearTransientFields? cfg evm er fields
  | .tuple ts => clearTransientTupleElems? cfg evm er 0 ts
  | .array t' n => clearTransientArrayElems? cfg evm er t' n
  | .dynamicArray t' =>
      match cfg.transient.layout { er with steps := er.steps ++ [.length] } evm with
      | some lenLoc =>
          match transientLocLoad evm lenLoc with
          | .int len =>
              match clearTransientArrayElems? cfg evm er t' len.toNat with
              | .ok evm1 =>
                  EvalResult.ofOption .storageError (transientLocStore evm1 lenLoc (.int 0))
              | r => r
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes =>
      match cfg.transient.clearValue? er .bytes evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | .string =>
      match cfg.transient.clearValue? er .string evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  termination_by t => (sizeOf t, 0)

def clearTransientFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult EVM.State
  | [] => .ok evm
  | (name, ft) :: rest =>
      match clearTransientStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft with
      | .ok evm1 => clearTransientFields? cfg evm1 er rest
      | r => r
  termination_by fields => (sizeOf fields, 0)

def clearTransientTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> EvalResult EVM.State
  | [] => .ok evm
  | tt :: rest =>
      match clearTransientStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt with
      | .ok evm1 => clearTransientTupleElems? cfg evm1 er (k+1) rest
      | r => r
  termination_by ts => (sizeOf ts, 0)

def clearTransientArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    (t' : StorageType) : Nat -> EvalResult EVM.State
  | 0 => .ok evm
  | n+1 =>
      match clearTransientStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int n)] } t'
        with
      | .ok evm1 => clearTransientArrayElems? cfg evm1 er t' n
      | r => r
  termination_by c => (sizeOf t', c)
end

mutual
def writeTransientStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> Value -> EvalResult EVM.State
  | .elem _, v
  | .contract _, v =>
      match cfg.transient.layout er evm with
      | some loc => EvalResult.ofOption .storageError (transientLocStore evm loc v)
      | none => .error .storageError
  | .struct _ ftypes, .struct _ fvals => writeTransientFields? cfg evm er ftypes fvals
  | .tuple ts, .tuple vs => writeTransientTupleElems? cfg evm er 0 ts vs
  | .array t' n, .array vs =>
      if vs.length = n then writeTransientArrayElems? cfg evm er t' 0 vs
      else .error .typeError
  | .dynamicArray t', .array vs => do
      let evm0 <- clearTransientStorage? cfg evm er (.dynamicArray t')
      let evm1 <- writeTransientArrayElems? cfg evm0 er t' 0 vs
      let lenLoc <- EvalResult.ofOption .storageError
        (cfg.transient.layout { er with steps := er.steps ++ [.length] } evm)
      EvalResult.ofOption .storageError (transientLocStore evm1 lenLoc (.int vs.length))
  | .bytes, .bytes bs =>
      match cfg.transient.writeValue? er .bytes (.bytes bs) evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | .string, .bytes bs =>
      match cfg.transient.writeValue? er .string (.bytes bs) evm with
      | some result => storagePrepareResultToEval result
      | none => .error .storageError
  | _, _ => .error .typeError
  termination_by t => (sizeOf t, 0)

def writeTransientFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> List (Ident × Value) -> EvalResult EVM.State
  | [], [] => .ok evm
  | (name, ft) :: trest, (vname, fv) :: vrest =>
      if name == vname then
        match writeTransientStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft fv
          with
        | .ok evm1 => writeTransientFields? cfg evm1 er trest vrest
        | r => r
      else .error .typeError
  | _, _ => .error .typeError
  termination_by ftypes => (sizeOf ftypes, 0)

def writeTransientTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> List Value -> EvalResult EVM.State
  | [], [] => .ok evm
  | tt :: trest, v :: vrest =>
      match writeTransientStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt v
        with
      | .ok evm1 => writeTransientTupleElems? cfg evm1 er (k+1) trest vrest
      | r => r
  | _, _ => .error .typeError
  termination_by ts => (sizeOf ts, 0)

def writeTransientArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    (t' : StorageType) (k : Nat) : List Value -> EvalResult EVM.State
  | [] => .ok evm
  | v :: rest =>
      match writeTransientStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int k)] } t' v
        with
      | .ok evm1 => writeTransientArrayElems? cfg evm1 er t' (k+1) rest
      | r => r
  termination_by vs => (sizeOf t', sizeOf vs)
end

mutual
def readTransientStorage? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> EvalResult Value
  | .elem _
  | .contract _ =>
      match cfg.transient.layout er evm with
      | some loc => .ok (transientLocLoad evm loc)
      | none => .error .storageError
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let fvals <- readTransientFields? cfg evm er fields
      pure (.struct name fvals)
  | .tuple ts => do
      let vs <- readTransientTupleElems? cfg evm er 0 ts
      pure (.tuple vs)
  | .array t' n => do
      let vs <- readTransientArrayElems? cfg evm er t' 0 n
      pure (.array vs)
  | .dynamicArray t' =>
      match cfg.transient.layout { er with steps := er.steps ++ [.length] } evm with
      | some lenLoc =>
          match transientLocLoad evm lenLoc with
          | .int len => do
              let vs <- readTransientArrayElems? cfg evm er t' 0 len.toNat
              pure (.array vs)
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes =>
      match cfg.transient.readValue? er .bytes evm with
      | some result => storageValueResultToEval result
      | none => .error .storageError
  | .string =>
      match cfg.transient.readValue? er .string evm with
      | some result => storageValueResultToEval result
      | none => .error .storageError
  termination_by t => (sizeOf t, 0)

def readTransientFields? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult (List (Ident × Value))
  | [] => .ok []
  | (name, ft) :: rest => do
      let v <- readTransientStorage? cfg evm { er with steps := er.steps ++ [.field name] } ft
      let vrest <- readTransientFields? cfg evm er rest
      pure ((name, v) :: vrest)
  termination_by fields => (sizeOf fields, 0)

def readTransientTupleElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (k : Nat) :
    List StorageType -> EvalResult (List Value)
  | [] => .ok []
  | tt :: rest => do
      let v <- readTransientStorage? cfg evm { er with steps := er.steps ++ [.tupleElem k] } tt
      let vrest <- readTransientTupleElems? cfg evm er (k+1) rest
      pure (v :: vrest)
  termination_by ts => (sizeOf ts, 0)

def readTransientArrayElems? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    (t' : StorageType) (k : Nat) : Nat -> EvalResult (List Value)
  | 0 => .ok []
  | c+1 => do
      let v <- readTransientStorage? cfg evm { er with steps := er.steps ++ [.aindex (.int k)] } t'
      let vrest <- readTransientArrayElems? cfg evm er t' (k+1) c
      pure (v :: vrest)
  termination_by c => (sizeOf t', c)
end

def readTransientArrayLength? (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    StorageType -> EvalResult Value
  | .array _ n => pure (.int n)
  | .elem (.bytes n) => pure (.int (fixedBytesSize n))
  | .dynamicArray _ =>
      match cfg.transient.layout { er with steps := er.steps ++ [.length] } evm with
      | some lenLoc =>
          match transientLocLoad evm lenLoc with
          | .int n => pure (.int n)
          | _ => .error .storageError
      | none => .error .storageError
  | .bytes | .string => do
      let len <- readTransientBytesLength? cfg evm er
      pure (.int len)
  | _ => .error .typeError

end Solm
