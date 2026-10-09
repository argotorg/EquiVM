import Solidity.Semantics

/-!
# Default configuration of a flattened contract

The canonical storage layout as a Sol⁻ storage backend, modern ABI decoding, and solc's constructor
deployment scheme (creation code followed by the ABI-encoded constructor arguments).
-/

namespace Solidity

/-- ABI types of the most-derived constructor's parameters. -/
def ctorAbiTys (fc : FlatContract) : Option (List ABI.ABIType) :=
  match topCtor? fc with
  | some f => f.decl.params.mapM fun p => abiTypeOf fc.types p.ty
  | none => some []

/-- `initcode ++ abi.encode(args)`. -/
def solcDeployment (fc : FlatContract) (initcode : EVM.Bytes) (args : List Solm.Value) : Option EVM.Bytes := do
  let tys ← ctorAbiTys fc
  let enc ← ABI.encodeABIValues? tys args
  pure (initcode ++ enc.toByteArray)

/-- Creation code for `new C(args)` from a table of creation bytecodes: `code ++ abi.encode(args)`
    with the constructor parameter types of `C`. -/
def creationFor (fc : FlatContract) (codes : List (Ident × EVM.Bytes)) (name : Ident) (args : List Solm.Value) :
    Option EVM.Bytes := do
  let code ← (codes.find? (·.1 == name)).map (·.2)
  let tys ← fc.ctorTys? name
  let atys ← tys.mapM (abiTypeOf fc.types)
  let enc ← ABI.encodeABIValues? atys args
  pure (code ++ enc.toByteArray)

def defaultConfig (fc : FlatContract) : Option Config := do
  let table ← fc.layoutTable?
  pure { storageBackend := storageBackend table, selfDeployment := solcDeployment fc }

/-- The immutables store of a deployed contract from the values of its immutables by name
    (`imm_<name>` locals of the declared types). -/
def immutableStore (fc : FlatContract) (vals : List (Ident × Value)) : Store :=
  fc.immutableVars.foldl (fun st v =>
    match vals.find? (·.1 == v.name) with
    | some (_, x) => st.insert (immName v.name) { ty := v.ty, val := x }
    | none => st) ∅

/-- Elaborate and configure in one step.  `creations` / `runtimes`: creation and runtime bytecode
    of the contracts the spec deploys with `new` or names in `type(C).creationCode` /
    `type(C).runtimeCode`. -/
def setup (p : Program) (target : Ident)
    (creations : List (Ident × EVM.Bytes) := []) (runtimes : List (Ident × EVM.Bytes) := []) :
    Except String (FlatContract × Config) := do
  let fc ← elabProgram p target
  match defaultConfig fc with
  | some cfg =>
    pure (fc, { cfg with
      creationCode := creationFor fc creations
      typeCreationCode := fun c => (creations.find? (·.1 == c)).map (·.2)
      typeRuntimeCode := fun c => (runtimes.find? (·.1 == c)).map (·.2) })
  | none => throw s!"no storage layout for `{target}`"

end Solidity
