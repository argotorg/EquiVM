import Solidity.Syntax
import ABI.Signature

/-!
# Static type information

`TypeEnv` collects the user-defined types visible to a contract; `abiTypeOf` projects a Solidity
type onto the ABI type grammar (enum ↦ `uint8`, contract ↦ `address`, struct ↦ tuple, mapping ↦
none), which fixes canonical signatures (`sigStrOf`) for selectors, events and errors.
-/

namespace Solidity

structure StructInfo where
  /-- Declaring contract, `none` for a file-level struct. -/
  qual : Option Ident
  name : Ident
  fields : List (Ty × Ident)
  deriving DecidableEq, Repr, Inhabited

structure EnumInfo where
  qual : Option Ident
  name : Ident
  members : List Ident
  deriving DecidableEq, Repr, Inhabited

/-- User-defined types, most-derived contract's declarations first. -/
structure TypeEnv where
  structs : List StructInfo := []
  enums : List EnumInfo := []
  contracts : List (Ident × ContractKind) := []
  deriving Repr, Inhabited

namespace TypeEnv

def struct? (env : TypeEnv) (qual : Option Ident) (name : Ident) : Option StructInfo :=
  env.structs.find? fun s => s.name == name && (qual.isNone || s.qual == qual)

def enum? (env : TypeEnv) (qual : Option Ident) (name : Ident) : Option EnumInfo :=
  env.enums.find? fun e => e.name == name && (qual.isNone || e.qual == qual)

def contractKind? (env : TypeEnv) (name : Ident) : Option ContractKind :=
  (env.contracts.find? (·.1 == name)).map (·.2)

end TypeEnv

def uint8Elem : ABI.ElemType := .int (.uint ⟨8, by decide⟩)

/-- `abiTypeOf` with explicit fuel for struct unfolding (structs cannot be recursive). -/
def abiTypeOfFuel (env : TypeEnv) : Nat → Ty → Option ABI.ABIType
  | 0, _ => none
  | fuel + 1, ty =>
    match ty with
    | .uint w => some (.elem (.int (.uint w)))
    | .int w => some (.elem (.int (.sint w)))
    | .bool => some (.elem .bool)
    | .address _ => some (.elem .address)
    | .fixedBytes n => some (.elem (.bytes n))
    | .bytes => some .bytes
    | .string => some .string
    | .mapping .. => none
    | .array e n => (abiTypeOfFuel env fuel e).map (.array · n)
    | .dynArray e => (abiTypeOfFuel env fuel e).map .dynamicArray
    | .user q n =>
      match env.struct? q n with
      | some s => (s.fields.mapM fun f => abiTypeOfFuel env fuel f.1).map .tuple
      | none =>
        if (env.enum? q n).isSome then some (.elem uint8Elem)
        else if (env.contractKind? n).isSome then some (.elem .address)
        else none

/-- The ABI type of a Solidity type, if it has one. -/
def abiTypeOf (env : TypeEnv) (ty : Ty) : Option ABI.ABIType :=
  abiTypeOfFuel env 256 ty

def sigOf (env : TypeEnv) (name : Ident) (tys : List Ty) : Option ABI.Signature := do
  let abis ← tys.mapM (abiTypeOf env)
  pure ⟨name, abis⟩

/-- Canonical signature string, e.g. `transfer(address,uint256)`. -/
def sigStrOf (env : TypeEnv) (name : Ident) (tys : List Ty) : Option String :=
  (sigOf env name tys).map ABI.printSignature

/-- The elementary type a value type is stored as (storage packing leaf). -/
def leafElemType (env : TypeEnv) : Ty → Option ABI.ElemType
  | .uint w => some (.int (.uint w))
  | .int w => some (.int (.sint w))
  | .bool => some .bool
  | .address _ => some .address
  | .fixedBytes n => some (.bytes n)
  | .user q n =>
    if (env.enum? q n).isSome then some uint8Elem
    else if (env.contractKind? n).isSome then some .address
    else none
  | _ => none

def isValueType (env : TypeEnv) (ty : Ty) : Bool :=
  (leafElemType env ty).isSome

/-- Kept as struct-getter members: everything except mappings and arrays (byte arrays stay). -/
def isGetterMemberType : Ty → Bool
  | .mapping .. => false
  | .array .. => false
  | .dynArray _ => false
  | _ => true

end Solidity
