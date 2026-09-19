import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Pot benchmark spec

Solm benchmark scaffold for upstream `dss/src/pot.sol`.

The source includes the same hand-written assembly `_rpow` loop shape as `Jug`; the scaffold models
that loop structurally. Events are omitted.
-/

open Solm ABI

namespace Benchmarks.Dss.Pot

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def one : Int := 1000000000000000000000000000

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)

def dsrParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [100, 115, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def vowParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [118, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## External ABI for VatLike -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def vatMoveSelector : ByteArray := selectorBytes 0xbb 0x35 0x78 0x3b
def vatSuckSelector : ByteArray := selectorBytes 0xf2 0x4e 0x23 0xeb

def potExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "move" then
      ABI.encodeCallWithSelector? vatMoveSelector [addr, addr, uint256] args
    else if name = "suck" then
      ABI.encodeCallWithSelector? vatSuckSelector [addr, addr, uint256] args
    else
      none
  decode? := fun name _out =>
    if name = "move" then some []
    else if name = "suck" then some []
    else none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def pieRef (usr : Expr) : StorageRef :=
  { base := "pie", steps := [.mindex usr] }

def PieRef : StorageRef := { base := "Pie" }
def dsrRef : StorageRef := { base := "dsr" }
def chiRef : StorageRef := { base := "chi" }
def vatRef : StorageRef := { base := "vat" }
def vowRef : StorageRef := { base := "vow" }
def rhoRef : StorageRef := { base := "rho" }
def liveRef : StorageRef := { base := "live" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "pie", ty := .mapping .address uint256St },
    { name := "Pie", ty := uint256St },
    { name := "dsr", ty := uint256St },
    { name := "chi", ty := uint256St },
    { name := "vat", ty := addrSt },
    { name := "vow", ty := addrSt },
    { name := "rho", ty := uint256St },
    { name := "live", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def pieSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨1⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "pie", steps := [.mindex usr] }, _ => some (wordLoc (pieSlot usr))
  | { base := "Pie", steps := [] }, _ => some (wordLoc ⟨2⟩)
  | { base := "dsr", steps := [] }, _ => some (wordLoc ⟨3⟩)
  | { base := "chi", steps := [] }, _ => some (wordLoc ⟨4⟩)
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨5⟩)
  | { base := "vow", steps := [] }, _ => some (addrLoc ⟨6⟩)
  | { base := "rho", steps := [] }, _ => some (wordLoc ⟨7⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨8⟩)
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def auth : List Stmt :=
  [ .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]

def checkedExternalCallStmts (receiver : Expr) (name : Ident) (eth : Expr)
    (args : List Expr) (retVar : Ident) (perm : Bool := true) : List Stmt :=
  [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
    .externalCall receiver name eth args retVar (perm := perm) ]

def checkedAddUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (add256 x y),
    .require (.binary .ge (.var name) x) ]

def checkedSubUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (sub256 x y),
    .require (.binary .le (.var name) x) ]

def checkedMulUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (mul256 x y),
    .require
      (.binary .or
        (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) ]

/-! ## Internal functions -/

def addFunction : FunctionDecl :=
  { name := "_add"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedAddUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def subFunction : FunctionDecl :=
  { name := "_sub"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedSubUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def mulFunction : FunctionDecl :=
  { name := "_mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedMulUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def rmulFunction : FunctionDecl :=
  { name := "_rmul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .internalCall "_mul" [.var "x", .var "y"] "z",
        .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit one)),
        .return [.var "z"] ] }

def rpowLoopBody : List Stmt :=
  checkedMulUintInto "xx" (.var "x") (.var "x") ++
  checkedAddUintInto "xxRound" (.var "xx") (.var "half") ++
  [ .assign .localVar { base := "x" } (.binary .div (.var "xxRound") (.var "base")),
    .ite
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
      (checkedMulUintInto "zx" (.var "z") (.var "x") ++
        checkedAddUintInto "zxRound" (.var "zx") (.var "half") ++
        [ .assign .localVar { base := "z" } (.binary .div (.var "zxRound") (.var "base")) ])
      [],
    .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)) ]

def rpowFunction : FunctionDecl :=
  { name := "_rpow"
    params :=
      [ { name := "x", ty := uint256 }, { name := "n", ty := uint256 },
        { name := "base", ty := uint256 } ]
    returnType := [uint256]
    body :=
      [ .ite
          (.binary .eq (.var "x") (.intLit 0))
          [ .ite
              (.binary .eq (.var "n") (.intLit 0))
              [ .return [.var "base"] ]
              [ .return [.intLit 0] ] ]
          [ .letDecl "z" (some uint256)
              (.ite
                (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
                (.var "base")
                (.var "x")),
            .letDecl "half" (some uint256) (.binary .div (.var "base") (.intLit 2)),
            .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
            .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
            .return [.var "z"] ] ] }

def functions : List FunctionDecl :=
  [addFunction, subFunction, mulFunction, rmulFunction, rpowFunction]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "vat_", ty := addr }]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage dsrRef (.intLit one),
        .assign .storage chiRef (.intLit one),
        .assign .storage rhoRef (.env .timestamp),
        .assign .storage liveRef (.intLit 1) ] }

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def pieTransition : TransitionDecl :=
  { name := "pie"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (pieRef (.var "arg0"))] ] }

def PieTransition : TransitionDecl :=
  { name := "Pie", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage PieRef] ] }

def dsrTransition : TransitionDecl :=
  { name := "dsr", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage dsrRef] ] }

def chiTransition : TransitionDecl :=
  { name := "chi", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage chiRef] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def vowTransition : TransitionDecl :=
  { name := "vow", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vowRef] ] }

def rhoTransition : TransitionDecl :=
  { name := "rho", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage rhoRef] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

/-! ## External transitions -/

def relyTransition : TransitionDecl :=
  { name := "rely"
    params := [{ name := "guy", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "guy")) (.intLit 1) ] }

def denyTransition : TransitionDecl :=
  { name := "deny"
    params := [{ name := "guy", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "guy")) (.intLit 0) ] }

def fileDsrTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .require (.binary .eq (.env .timestamp) (.storage rhoRef)),
        .ite
          (.binary .eq (.var "what") dsrParamLit)
          [ .assign .storage dsrRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def fileVowTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "addr", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") vowParamLit)
          [ .assign .storage vowRef (.var "addr") ]
          [ .require (.boolLit false) ] ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .assign .storage liveRef (.intLit 0),
        .assign .storage dsrRef (.intLit one) ] }

def dripTransition : TransitionDecl :=
  { name := "drip"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .require (.binary .ge (.env .timestamp) (.storage rhoRef)),
        .internalCall "_rpow"
          [ .storage dsrRef, sub256 (.env .timestamp) (.storage rhoRef), .intLit one ] "pow",
        .internalCall "_rmul" [.var "pow", .storage chiRef] "tmp",
        .internalCall "_sub" [.var "tmp", .storage chiRef] "chi_",
        .assign .storage chiRef (.var "tmp"),
        .assign .storage rhoRef (.env .timestamp),
        .internalCall "_mul" [.storage PieRef, .var "chi_"] "rad" ] ++
      checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [.storage vowRef, .env .this, .var "rad"] "_suckRet" ++
      [ .return [.var "tmp"] ] }

def joinTransition : TransitionDecl :=
  { name := "join"
    params := [{ name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.env .timestamp) (.storage rhoRef)) ] ++
      checkedAddUintInto "pieNew" (.storage (pieRef sender)) (.var "wad") ++
      [ .assign .storage (pieRef sender) (.var "pieNew") ] ++
      checkedAddUintInto "PieNew" (.storage PieRef) (.var "wad") ++
      [ .assign .storage PieRef (.var "PieNew"),
        .internalCall "_mul" [.storage chiRef, .var "wad"] "rad" ] ++
      checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
        [sender, .env .this, .var "rad"] "_moveRet" }

def exitTransition : TransitionDecl :=
  { name := "exit"
    params := [{ name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      checkedSubUintInto "pieNew" (.storage (pieRef sender)) (.var "wad") ++
      [ .assign .storage (pieRef sender) (.var "pieNew") ] ++
      checkedSubUintInto "PieNew" (.storage PieRef) (.var "wad") ++
      [ .assign .storage PieRef (.var "PieNew"),
        .internalCall "_mul" [.storage chiRef, .var "wad"] "rad" ] ++
      checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
        [.env .this, sender, .var "rad"] "_moveRet" }

def transitions : List TransitionDecl :=
  [ PieTransition,
    cageTransition,
    chiTransition,
    denyTransition,
    dripTransition,
    dsrTransition,
    exitTransition,
    fileDsrTransition,
    fileVowTransition,
    joinTransition,
    liveTransition,
    pieTransition,
    relyTransition,
    rhoTransition,
    vatTransition,
    vowTransition,
    wardsTransition ]

def contract : ContractDecl :=
  { name := "Pot"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := potExternalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Pot
