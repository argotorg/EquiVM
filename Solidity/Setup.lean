import Solidity.Semantics

/-!
# Default configuration of a flattened contract

The canonical storage layout, modern ABI decoding, no immutables, and solc's constructor
deployment scheme (creation code followed by the ABI-encoded constructor arguments).
-/

namespace Solidity

/-- ABI types of the most-derived constructor's parameters. -/
def ctorAbiTys (fc : FlatContract) : Option (List ABI.ABIType) :=
  match topCtor? fc with
  | some f => f.decl.params.mapM fun p => abiTypeOf fc.types p.ty
  | none => some []

/-- `initcode ++ abi.encode(args)`. -/
def solcDeployment (fc : FlatContract) (initcode : EVM.Bytes) (args : List ABI.ABIValue) : Option EVM.Bytes := do
  let tys ← ctorAbiTys fc
  let enc ← ABI.encodeABIValues? tys args
  pure (initcode ++ enc.toByteArray)

/-- Creation code for `new C(args)` from a table of creation bytecodes: `code ++ abi.encode(args)`
    with the constructor parameter types of `C`. -/
def creationFor (fc : FlatContract) (codes : List (Ident × EVM.Bytes)) (name : Ident) (args : List ABI.ABIValue) :
    Option EVM.Bytes := do
  let code ← (codes.find? (·.1 == name)).map (·.2)
  let tys ← fc.ctorTys? name
  let atys ← tys.mapM (abiTypeOf fc.types)
  let enc ← ABI.encodeABIValues? atys args
  pure (code ++ enc.toByteArray)

def defaultConfig (fc : FlatContract) (immutables : List (Ident × Value) := []) : Option Config := do
  let table ← fc.layoutTable?
  pure { storage := storageLayout table, immutables := immutables, selfDeployment := solcDeployment fc }

/-- Elaborate and configure in one step. -/
def setup (p : Program) (target : Ident) (immutables : List (Ident × Value) := [])
    (creations : List (Ident × EVM.Bytes) := []) : Except String (FlatContract × Config) := do
  let fc ← elabProgram p target
  match defaultConfig fc immutables with
  | some cfg => pure (fc, { cfg with creationCode := creationFor fc creations })
  | none => throw s!"no storage layout for `{target}`"

end Solidity
