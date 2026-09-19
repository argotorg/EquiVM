import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Jug benchmark spec

Solm benchmark scaffold for upstream `dss/src/jug.sol`.

The source includes a hand-written assembly `_rpow` loop. The scaffold models that loop
structurally with Solm statements instead of replacing it by an abstract exponentiation. Events are
omitted.
-/

open Solm ABI

namespace Benchmarks.Dss.Jug

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def int256Int : IntType := .sint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def int256 : ABIType := .elem (.int int256Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def one : Int := 1000000000000000000000000000
def maxInt256 : Int := (2 : Int) ^ 255 - 1

def u256 (e : Expr) : Expr := .inRange uint256Int e
def s256 (e : Expr) : Expr := .inRange int256Int e

def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def checkedSub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def sub256 (x y : Expr) : Expr :=
  .ite (.binary .le y x)
    (checkedSub256 x y)
    (u256 (.binary .sub (.binary .add (.intLit (Int.ofNat Ethereum.UInt256.size)) x) y))
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)

def dutyParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [100, 117, 116, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def baseParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [98, 97, 115, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def vowParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [118, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## External ABI for VatLike -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def vatIlksSelector : ByteArray := selectorBytes 0xd9 0x63 0x8d 0x36
def vatFoldSelector : ByteArray := selectorBytes 0xb6 0x53 0x37 0xdf

def jugExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "ilks" then
      ABI.encodeCallWithSelector? vatIlksSelector [bytes32] args
    else if name = "fold" then
      ABI.encodeCallWithSelector? vatFoldSelector [bytes32, addr, int256] args
    else
      none
  decode? := fun name out =>
    if name = "ilks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out
    else if name = "fold" then
      some []
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def ilksF (ilk : Expr) (field : Ident) : StorageRef :=
  { base := "ilks", steps := [.mindex ilk, .field field] }

def vatRef : StorageRef := { base := "vat" }
def vowRef : StorageRef := { base := "vow" }
def baseRef : StorageRef := { base := "base" }

/-! ## Storage declarations and layout -/

def IlkStructTy : StorageType :=
  .struct "Ilk" [("duty", uint256St), ("rho", uint256St)]

def IlkStructDecl : StructDecl :=
  { name := "Ilk"
    fields := [ { name := "duty", ty := uint256St }, { name := "rho", ty := uint256St } ] }

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "vat", ty := addrSt },
    { name := "vow", ty := addrSt },
    { name := "base", ty := uint256St } ]

def structs : List StructDecl := [IlkStructDecl]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def ilksBase (ilk : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord ilk) ⟨1⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "ilks", steps := [.mindex ilk, .field "duty"] }, _ =>
      some (wordLoc (ilksBase ilk))
  | { base := "ilks", steps := [.mindex ilk, .field "rho"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨1⟩))
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "vow", steps := [] }, _ => some (addrLoc ⟨3⟩)
  | { base := "base", steps := [] }, _ => some (wordLoc ⟨4⟩)
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

def diffFunction : FunctionDecl :=
  { name := "_diff"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [int256]
    body :=
      [ .letDecl "z" (some int256) (s256 (.binary .sub (.var "x") (.var "y"))),
        .require (.binary .le (.var "x") (.intLit maxInt256)),
        .require (.binary .le (.var "y") (.intLit maxInt256)),
        .return [.var "z"] ] }

def rmulFunction : FunctionDecl :=
  { name := "_rmul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      checkedMulUintInto "z" (.var "x") (.var "y") ++
      [ .assign .localVar { base := "z" } (.binary .div (.var "z") (.intLit one)),
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
  { name := "_rpow"
    params :=
      [ { name := "x", ty := uint256 }, { name := "n", ty := uint256 },
        { name := "b", ty := uint256 } ]
    returnType := [uint256]
    body :=
      [ .ite
          (.binary .eq (.var "x") (.intLit 0))
          [ .ite
              (.binary .eq (.var "n") (.intLit 0))
              [ .return [.var "b"] ]
              [ .return [.intLit 0] ] ]
          [ .letDecl "z" (some uint256)
              (.ite
                (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
                (.var "b")
                (.var "x")),
            .letDecl "half" (some uint256) (.binary .div (.var "b") (.intLit 2)),
            .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
            .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
            .return [.var "z"] ] ] }

def functions : List FunctionDecl := [addFunction, diffFunction, rmulFunction, rpowFunction]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "vat_", ty := addr }]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage vatRef (.var "vat_") ] }

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def ilksTransition : TransitionDecl :=
  { name := "ilks"
    params := [{ name := "arg0", ty := bytes32 }]
    returnType := [uint256, uint256]
    body :=
      nonpayable ++
      [ .return
          [ .storage (ilksF (.var "arg0") "duty"),
            .storage (ilksF (.var "arg0") "rho") ] ] }

def vatTransition : TransitionDecl :=
  { name := "vat"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def vowTransition : TransitionDecl :=
  { name := "vow"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [.storage vowRef] ] }

def baseTransition : TransitionDecl :=
  { name := "base"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage baseRef] ] }

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

def initTransition : TransitionDecl :=
  { name := "init"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage (ilksF (.var "ilk") "duty")) (.intLit 0)),
        .assign .storage (ilksF (.var "ilk") "duty") (.intLit one),
        .assign .storage (ilksF (.var "ilk") "rho") (.env .timestamp) ] }

def fileDutyTransition : TransitionDecl :=
  { name := "file"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "what", ty := bytes32 },
        { name := "data", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))),
        .ite
          (.binary .eq (.var "what") dutyParamLit)
          [ .assign .storage (ilksF (.var "ilk") "duty") (.var "data") ]
          [ .require (.boolLit false) ] ] }

def fileBaseTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") baseParamLit)
          [ .assign .storage baseRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def fileVowTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") vowParamLit)
          [ .assign .storage vowRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def dripTransition : TransitionDecl :=
  { name := "drip"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .require (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) ] ++
      checkedExternalCallStmts (.storage vatRef) "ilks" (.intLit 0) [.var "ilk"] "vatIlk" ++
      [ .letDecl "prev" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "_add"
          [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] "fee",
        .internalCall "_rpow"
          [ .var "fee",
            sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
            .intLit one ] "pow",
        .internalCall "_rmul" [.var "pow", .var "prev"] "rate",
        .internalCall "_diff" [.var "rate", .var "prev"] "delta" ] ++
      checkedExternalCallStmts (.storage vatRef) "fold" (.intLit 0)
        [.var "ilk", .storage vowRef, .var "delta"] "_foldRet" ++
      [
        .assign .storage (ilksF (.var "ilk") "rho") (.env .timestamp),
        .return [.var "rate"] ] }

def transitions : List TransitionDecl :=
  [ baseTransition,
    denyTransition,
    dripTransition,
    fileBaseTransition,
    fileDutyTransition,
    fileVowTransition,
    ilksTransition,
    initTransition,
    relyTransition,
    vatTransition,
    vowTransition,
    wardsTransition ]

def contract : ContractDecl :=
  { name := "Jug"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := jugExternalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Jug
