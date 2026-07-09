import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS LinearDecrease benchmark spec

Faithful Solm benchmark scaffold for upstream `dss/src/abaci.sol` contract `LinearDecrease`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI

namespace Benchmarks.Dss.LinearDecrease

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def RAY : Int := 1000000000000000000000000000

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)

def zeroPad29 : List UInt8 := List.replicate 29 0
def zeroPad28 : List UInt8 := List.replicate 28 0

def tauParamLit : Expr :=
  .fixedBytesLit bytes32Width ([116, 97, 117] ++ zeroPad29)

def cutParamLit : Expr :=
  .fixedBytesLit bytes32Width ([99, 117, 116] ++ zeroPad29)

def stepParamLit : Expr :=
  .fixedBytesLit bytes32Width ([115, 116, 101, 112] ++ zeroPad28)

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def tauRef : StorageRef := { base := "tau" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "tau", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "tau", steps := [] }, _ => some (wordLoc ⟨1⟩)
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def auth : List Stmt :=
  [ .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]

def checkedAddUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (add256 x y),
    .require (.binary .ge (.var name) x) ]

def checkedMulUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (mul256 x y),
    .require
      (.binary .or
        (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body := nonpayable ++ [ .assign .storage (wardsRef sender) (.intLit 1) ] }

/-! ## Internal functions -/

def addFunction : FunctionDecl :=
  { name := "add"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedAddUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def mulFunction : FunctionDecl :=
  { name := "mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedMulUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def rmulFunction : FunctionDecl :=
  { name := "rmul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      checkedMulUintInto "z" (.var "x") (.var "y") ++
      [ .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit RAY)),
        .return [.var "z"] ] }

def functions : List FunctionDecl :=
  [addFunction, mulFunction, rmulFunction]

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def tauTransition : TransitionDecl :=
  { name := "tau", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage tauRef] ] }

/-! ## External transitions -/

def relyTransition : TransitionDecl :=
  { name := "rely"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "usr")) (.intLit 1) ] }

def denyTransition : TransitionDecl :=
  { name := "deny"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "usr")) (.intLit 0) ] }

def fileTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") tauParamLit)
          [ .assign .storage tauRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def priceTransition : TransitionDecl :=
  { name := "price"
    params := [{ name := "top", ty := uint256 }, { name := "dur", ty := uint256 }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .ite
          (.binary .ge (.var "dur") (.storage tauRef))
          [ .return [.intLit 0] ]
          [ .letDecl "left" (some uint256) (sub256 (.storage tauRef) (.var "dur")),
            .internalCall "mul" [.var "left", .intLit RAY] "scaled",
            .letDecl "ratio" (some uint256) (.binary .div (.var "scaled") (.storage tauRef)),
            .internalCall "rmul" [.var "top", .var "ratio"] "out",
            .return [.var "out"] ] ] }

def transitions : List TransitionDecl :=
  [denyTransition, fileTransition, priceTransition, relyTransition, tauTransition, wardsTransition]

def contract : ContractDecl :=
  { name := "LinearDecrease"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.LinearDecrease
