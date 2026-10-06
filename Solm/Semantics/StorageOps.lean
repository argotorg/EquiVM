import Solm.Semantics.Types
import Solm.Semantics.ValueOps

/-! Storage type resolution, default values, and bounds checks. -/

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

/-- Check an array or bytes index using the selected backend's length operation. -/
@[simp] def arrayIndexInBounds? (cfg : Config) (evm : EVM.State)
    (decls : List StorageDecl) (base : Ident) (pre : List EvaledStorageRefStep)
    (i : KeyValue) : EvalResult Unit :=
  match storageTypeAt? decls { base := base, steps := pre }, i with
  | some (.array _ n), .int iv =>
      if 0 ≤ iv ∧ iv < n then .ok () else .revert
  | some (.array _ _), _ => .error .typeError
  | some ty@(.dynamicArray _), .int iv
  | some ty@(.bytes), .int iv
  | some ty@(.string), .int iv =>
      match cfg.storageBackend.length { base := base, steps := pre } ty evm with
      | .ok len => if 0 ≤ iv ∧ iv < len then .ok () else .revert
      | .revert => .revert
      | .error e => .error e
  | some (.dynamicArray _), _ | some (.bytes), _ | some (.string), _ => .error .typeError
  | some _, _ => .error .typeError
  | none, _ => .error .storageError

end Solm
