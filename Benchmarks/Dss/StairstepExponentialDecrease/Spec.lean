import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS StairstepExponentialDecrease benchmark spec

Faithful Solm benchmark scaffold for upstream `dss/src/abaci.sol` contract `StairstepExponentialDecrease`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI

namespace Benchmarks.Dss.StairstepExponentialDecrease

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

def stepRef : StorageRef := { base := "step" }
def cutRef : StorageRef := { base := "cut" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "step", ty := uint256St },
    { name := "cut", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "step", steps := [] }, _ => some (wordLoc ⟨1⟩)
  | { base := "cut", steps := [] }, _ => some (wordLoc ⟨2⟩)
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

def rmulFunction : FunctionDecl :=
  { name := "rmul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      checkedMulUintInto "z" (.var "x") (.var "y") ++
      [ .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit RAY)),
        .return [.var "z"] ] }

def rpowLoopBody : List Stmt :=
  checkedMulUintInto "xx" (.var "x") (.var "x") ++
  checkedAddUintInto "xxRound" (.var "xx") (.var "half") ++
  [ .assign .localVar { base := "x" } (.binary .div (.var "xxRound") (.var "b")),
    .ite
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
      (checkedMulUintInto "zx" (.var "z") (.var "x") ++
        checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
        [ .assign .localVar { base := "z" } (.binary .div (.var "zxRound") (.var "b")) ])
      [],
    .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)) ]

def rpowFunction : FunctionDecl :=
  { name := "rpow"
    params :=
      [ { name := "x", ty := uint256 }, { name := "n", ty := uint256 },
        { name := "b", ty := uint256 } ]
    returnType := [uint256]
    body :=
      [ .ite
          (.binary .eq (.var "n") (.intLit 0))
          [ .return [.var "b"] ]
          [ .ite
              (.binary .eq (.var "x") (.intLit 0))
              [ .return [.intLit 0] ]
              [ .letDecl "z" (some uint256)
                  (.ite
                    (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
                    (.var "b")
                    (.var "x")),
                .letDecl "half" (some uint256) (.binary .div (.var "b") (.intLit 2)),
                .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
                .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
                .return [.var "z"] ] ] ] }

def functions : List FunctionDecl :=
  [rmulFunction, rpowFunction]

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def stepTransition : TransitionDecl :=
  { name := "step", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage stepRef] ] }

def cutTransition : TransitionDecl :=
  { name := "cut", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage cutRef] ] }

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
          (.binary .eq (.var "what") cutParamLit)
          [ .assign .storage cutRef (.var "data"),
            .require (.binary .le (.storage cutRef) (.intLit RAY)) ]
          [ .ite
              (.binary .eq (.var "what") stepParamLit)
              [ .assign .storage stepRef (.var "data") ]
              [ .require (.boolLit false) ] ] ] }

def priceTransition : TransitionDecl :=
  { name := "price"
    params := [{ name := "top", ty := uint256 }, { name := "dur", ty := uint256 }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .letDecl "n" (some uint256) (.binary .div (.var "dur") (.storage stepRef)),
        .internalCall "rpow" [.storage cutRef, .var "n", .intLit RAY] "pow",
        .internalCall "rmul" [.var "top", .var "pow"] "out",
        .return [.var "out"] ] }

def transitions : List TransitionDecl :=
  [cutTransition, denyTransition, fileTransition, priceTransition, relyTransition, stepTransition, wardsTransition]

def contract : ContractDecl :=
  { name := "StairstepExponentialDecrease"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.StairstepExponentialDecrease
