import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Spotter benchmark spec

Solm benchmark scaffold for upstream `dss/src/spot.sol`.

The storage layout and public ABI surface follow solc `0.6.12`. Events are omitted. `poke` keeps
the source-level oracle call and conditional arithmetic evaluation shape.
-/

open Solm ABI

namespace Benchmarks.Dss.Spot

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def one : Int := 1000000000000000000000000000
def billion : Int := 1000000000

def u256 (e : Expr) : Expr := .inRange uint256Int e
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)

def pipParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [112, 105, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def parParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [112, 97, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def matParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [109, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def spotParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [115, 112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## External ABI for VatLike and PipLike -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def vatFileSelector : ByteArray := selectorBytes 0x1a 0x0b 0x28 0x7e
def pipPeekSelector : ByteArray := selectorBytes 0x59 0xe0 0x2d 0xd7

def spotExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "file" then
      ABI.encodeCallWithSelector? vatFileSelector [bytes32, bytes32, uint256] args
    else if name = "peek" then
      match args with
      | [] => some pipPeekSelector
      | _ => none
    else
      none
  decode? := fun name out =>
    if name = "file" then
      some []
    else if name = "peek" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [bytes32, boolTy] out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def ilksF (ilk : Expr) (field : Ident) : StorageRef :=
  { base := "ilks", steps := [.mindex ilk, .field field] }

def vatRef : StorageRef := { base := "vat" }
def parRef : StorageRef := { base := "par" }
def liveRef : StorageRef := { base := "live" }

/-! ## Storage declarations and layout -/

def IlkStructTy : StorageType :=
  .struct "Ilk" [("pip", addrSt), ("mat", uint256St)]

def IlkStructDecl : StructDecl :=
  { name := "Ilk"
    fields := [ { name := "pip", ty := addrSt }, { name := "mat", ty := uint256St } ] }

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "vat", ty := addrSt },
    { name := "par", ty := uint256St },
    { name := "live", ty := uint256St } ]

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
  | { base := "ilks", steps := [.mindex ilk, .field "pip"] }, _ =>
      some (addrLoc (ilksBase ilk))
  | { base := "ilks", steps := [.mindex ilk, .field "mat"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨1⟩))
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "par", steps := [] }, _ => some (wordLoc ⟨3⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨4⟩)
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def auth : List Stmt :=
  [ .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]

def requireLive : List Stmt :=
  [ .require (.binary .eq (.storage liveRef) (.intLit 1)) ]

def checkedMulUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (mul256 x y),
    .require
      (.binary .or
        (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "vat_", ty := addr }]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage parRef (.intLit one),
        .assign .storage liveRef (.intLit 1) ] }

/-! ## Internal functions -/

def mulFunction : FunctionDecl :=
  { name := "mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedMulUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def rdivFunction : FunctionDecl :=
  { name := "rdiv"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .internalCall "mul" [.var "x", .intLit one] "z",
        .assign .localVar { base := "z" } (.binary .div (.var "z") (.var "y")),
        .return [.var "z"] ] }

def functions : List FunctionDecl :=
  [mulFunction, rdivFunction]

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def ilksTransition : TransitionDecl :=
  { name := "ilks"
    params := [{ name := "arg0", ty := bytes32 }]
    returnType := [addr, uint256]
    body :=
      nonpayable ++
      [ .return
          [ .storage (ilksF (.var "arg0") "pip"),
            .storage (ilksF (.var "arg0") "mat") ] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def parTransition : TransitionDecl :=
  { name := "par", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage parRef] ] }

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

def filePipTransition : TransitionDecl :=
  { name := "file"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "what", ty := bytes32 },
        { name := "pip_", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      [ .ite
          (.binary .eq (.var "what") pipParamLit)
          [ .assign .storage (ilksF (.var "ilk") "pip") (.var "pip_") ]
          [ .require (.boolLit false) ] ] }

def fileParTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      [ .ite
          (.binary .eq (.var "what") parParamLit)
          [ .assign .storage parRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def fileMatTransition : TransitionDecl :=
  { name := "file"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "what", ty := bytes32 },
        { name := "data", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      [ .ite
          (.binary .eq (.var "what") matParamLit)
          [ .assign .storage (ilksF (.var "ilk") "mat") (.var "data") ]
          [ .require (.boolLit false) ] ] }

def pokeTransition : TransitionDecl :=
  { name := "poke"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++
      [ .externalCall (.storage (ilksF (.var "ilk") "pip")) "peek" (.intLit 0) [] "peekRet",
        .letDecl "val" (some bytes32) (.tupleGet (.var "peekRet") 0),
        .letDecl "has" (some boolTy) (.tupleGet (.var "peekRet") 1),
        .letDecl "spot" (some uint256) (.intLit 0),
        .ite (.var "has")
          (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
            [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
              .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")] "spot2",
              .assign .localVar { base := "spot" } (.var "spot2") ])
          [],
        .externalCall (.storage vatRef) "file" (.intLit 0)
          [.var "ilk", spotParamLit, .var "spot"] "_fileRet" ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage liveRef (.intLit 0) ] }

def transitions : List TransitionDecl :=
  [ cageTransition,
    denyTransition,
    fileMatTransition,
    fileParTransition,
    filePipTransition,
    ilksTransition,
    liveTransition,
    parTransition,
    pokeTransition,
    relyTransition,
    vatTransition,
    wardsTransition ]

def contract : ContractDecl :=
  { name := "Spotter"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := spotExternalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Spot
