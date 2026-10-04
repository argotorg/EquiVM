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
  /-- Declaring unit (`some ""` for a file-level struct). -/
  qual : Option Ident
  name : Ident
  fields : List (Ty × Ident)
  deriving DecidableEq, Repr, Inhabited

structure EnumInfo where
  qual : Option Ident
  name : Ident
  members : List Ident
  deriving DecidableEq, Repr, Inhabited

/-- User-defined types of a program.  A struct or enum is identified by its declaring unit and its
    name; the file is the unit `""`. -/
structure TypeEnv where
  structs : List StructInfo := []
  enums : List EnumInfo := []
  contracts : List (Ident × ContractKind) := []
  /-- Every contract-like unit with its bases, most derived first. -/
  lins : List (Ident × List Ident) := []
  deriving Repr, Inhabited

/-- Rewrite the qualifier of every user type in a type. -/
def Ty.mapUser (f : Option Ident → Ident → Option Ident) : Ty → Ty
  | .user q n => .user (f q n) n
  | .mapping k v => .mapping (k.mapUser f) (v.mapUser f)
  | .array e n => .array (e.mapUser f) n
  | .dynArray e => .dynArray (e.mapUser f)
  | t => t

namespace TypeEnv

def struct? (env : TypeEnv) (qual : Option Ident) (name : Ident) : Option StructInfo :=
  env.structs.find? fun s => s.name == name && s.qual == qual

def enum? (env : TypeEnv) (qual : Option Ident) (name : Ident) : Option EnumInfo :=
  env.enums.find? fun e => e.name == name && e.qual == qual

def contractKind? (env : TypeEnv) (name : Ident) : Option ContractKind :=
  (env.contracts.find? (·.1 == name)).map (·.2)

/-- The unit `u` and its bases, most derived first. -/
def unitLin (env : TypeEnv) (u : Ident) : List Ident :=
  ((env.lins.find? (·.1 == u)).map (·.2)).getD [u]

/-- Units whose declarations code of `here` sees without a qualifier: `here`, its bases, the file. -/
def scope (env : TypeEnv) (here : Ident) : List Ident := env.unitLin here ++ [""]

/-- The first of `units` that declares a struct or an enum named `n`. -/
def typeOwner (env : TypeEnv) (units : List Ident) (n : Ident) : Option Ident :=
  units.find? fun u => (env.struct? (some u) n).isSome || (env.enum? (some u) n).isSome

/-- The struct `n` names in code of `here`. -/
def structIn (env : TypeEnv) (here n : Ident) : Option StructInfo :=
  (env.scope here).findSome? fun u => env.struct? (some u) n

/-- The enum `n` names in code of `here`. -/
def enumIn (env : TypeEnv) (here n : Ident) : Option EnumInfo :=
  (env.scope here).findSome? fun u => env.enum? (some u) n

/-- The struct `q.n`: declared in `q` or inherited by it. -/
def structOf (env : TypeEnv) (q n : Ident) : Option StructInfo :=
  (env.unitLin q).findSome? fun u => env.struct? (some u) n

/-- The enum `q.n`. -/
def enumOf (env : TypeEnv) (q n : Ident) : Option EnumInfo :=
  (env.unitLin q).findSome? fun u => env.enum? (some u) n

/-- The type as the semantics identifies it: a user type written in code of `here` gets the unit
    that declares it (`S` in its library and `L.S` outside are one type; a contract type and an
    unknown name keep their spelling).  Applying it twice changes nothing. -/
def canonTy (env : TypeEnv) (here : Ident) (ty : Ty) : Ty :=
  ty.mapUser fun q n =>
    match q with
    | some u => match env.typeOwner (env.unitLin u) n with
      | some o => some o
      | none => some u
    | none => env.typeOwner (env.scope here) n

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
