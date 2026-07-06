import Solm.Semantics
import Solm.SolidityLayout
import Benchmarks.Dss.Dog.Immutables

/-!
# MakerDAO/Sky DSS Dog benchmark spec

Faithful Solm benchmark spec for upstream `dss/src/dog.sol`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def int256Int : IntType := .sint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def int256 : ABIType := .elem (.int int256Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def int256St : StorageType := .elem (.int int256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def WAD : Int := 1000000000000000000
def int256Limit : Int := 57896044618658097711785492504343953926634992332820282019728792003956564819968

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)
def asInt256 (e : Expr) : Expr := .cast e int256St

def zeroPad28 : List UInt8 := List.replicate 28 0

def vowParamLit : Expr :=
  .fixedBytesLit bytes32Width ([118, 111, 119] ++ List.replicate 29 0)

def HoleParamLit : Expr :=
  .fixedBytesLit bytes32Width ([72, 111, 108, 101] ++ zeroPad28)

def chopParamLit : Expr :=
  .fixedBytesLit bytes32Width ([99, 104, 111, 112] ++ zeroPad28)

def holeParamLit : Expr :=
  .fixedBytesLit bytes32Width ([104, 111, 108, 101] ++ zeroPad28)

def clipParamLit : Expr :=
  .fixedBytesLit bytes32Width ([99, 108, 105, 112] ++ zeroPad28)

/-! ## External ABI for VatLike, VowLike, and ClipperLike -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def vatGrabSelector : ByteArray := selectorBytes 0x7b 0xab 0x3f 0x40
def vatIlksSelector : ByteArray := selectorBytes 0xd9 0x63 0x8d 0x36
def vatUrnsSelector : ByteArray := selectorBytes 0x24 0x24 0xbe 0x5c
def vowFessSelector : ByteArray := selectorBytes 0x69 0x7e 0xfb 0x78
def clipperIlkSelector : ByteArray := selectorBytes 0xc5 0xce 0x28 0x1e
def clipperKickSelector : ByteArray := selectorBytes 0x89 0x8e 0xb2 0x67

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "grab" then
      ABI.encodeCallWithSelector? vatGrabSelector
        [bytes32, addr, addr, addr, int256, int256] args
    else if name = "ilks" then
      ABI.encodeCallWithSelector? vatIlksSelector [bytes32] args
    else if name = "urns" then
      ABI.encodeCallWithSelector? vatUrnsSelector [bytes32, addr] args
    else if name = "fess" then
      ABI.encodeCallWithSelector? vowFessSelector [uint256] args
    else if name = "ilk" then
      match args with
      | [] => some clipperIlkSelector
      | _ => none
    else if name = "kick" then
      ABI.encodeCallWithSelector? clipperKickSelector [uint256, uint256, addr, addr] args
    else
      none
  decode? := fun name out =>
    if name = "ilks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out
    else if name = "urns" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out
    else if name = "grab" then
      decodeVoid? out
    else if name = "fess" then
      decodeVoid? out
    else if name = "ilk" then
      decodeReturn? bytes32 out
    else if name = "kick" then
      decodeReturn? uint256 out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def ilksF (ilk : Expr) (field : Ident) : StorageRef :=
  { base := "ilks", steps := [.mindex ilk, .field field] }

def vowRef : StorageRef := { base := "vow" }
def liveRef : StorageRef := { base := "live" }
def HoleRef : StorageRef := { base := "Hole" }
def DirtRef : StorageRef := { base := "Dirt" }
def vowAddr : Expr := .storage vowRef
def varRef (name : Ident) : StorageRef := { base := name }

/-! ## Storage declarations and layout -/

def IlkStructTy : StorageType :=
  .struct "Ilk"
    [("clip", addrSt), ("chop", uint256St), ("hole", uint256St), ("dirt", uint256St)]

def IlkStructDecl : StructDecl :=
  { name := "Ilk"
    fields :=
      [ { name := "clip", ty := addrSt },
        { name := "chop", ty := uint256St },
        { name := "hole", ty := uint256St },
        { name := "dirt", ty := uint256St } ] }

def structs : List StructDecl := [IlkStructDecl]

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "vow", ty := addrSt },
    { name := "live", ty := uint256St },
    { name := "Hole", ty := uint256St },
    { name := "Dirt", ty := uint256St } ]

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
  | { base := "ilks", steps := [.mindex ilk, .field "clip"] }, _ =>
      some (addrLoc (ilksBase ilk))
  | { base := "ilks", steps := [.mindex ilk, .field "chop"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨1⟩))
  | { base := "ilks", steps := [.mindex ilk, .field "hole"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨2⟩))
  | { base := "ilks", steps := [.mindex ilk, .field "dirt"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨3⟩))
  | { base := "vow", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨3⟩)
  | { base := "Hole", steps := [] }, _ => some (wordLoc ⟨4⟩)
  | { base := "Dirt", steps := [] }, _ => some (wordLoc ⟨5⟩)
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

/-! ## Constructor and internal functions -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "vat_", ty := addr }]
    body :=
      nonpayable ++
      [ .letDecl "imm_vat" (some addr) (.var "vat_"),
        .assign .storage liveRef (.intLit 1),
        .assign .storage (wardsRef sender) (.intLit 1) ] }

def minFunction : FunctionDecl :=
  { name := "min"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .ite
          (.binary .le (.var "x") (.var "y"))
          [ .return [.var "x"] ]
          [ .return [.var "y"] ] ] }

def addFunction : FunctionDecl :=
  { name := "add"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedAddUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def subFunction : FunctionDecl :=
  { name := "sub"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedSubUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def mulFunction : FunctionDecl :=
  { name := "mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedMulUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def functions : List FunctionDecl :=
  [minFunction, addFunction, subFunction, mulFunction]

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def ilksTransition : TransitionDecl :=
  { name := "ilks"
    params := [{ name := "arg0", ty := bytes32 }]
    returnType := [addr, uint256, uint256, uint256]
    body :=
      nonpayable ++
      [ .return
          [ .storage (ilksF (.var "arg0") "clip"),
            .storage (ilksF (.var "arg0") "chop"),
            .storage (ilksF (.var "arg0") "hole"),
            .storage (ilksF (.var "arg0") "dirt") ] ] }

def vowTransition : TransitionDecl :=
  { name := "vow", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vowRef] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

def HoleTransition : TransitionDecl :=
  { name := "Hole", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage HoleRef] ] }

def DirtTransition : TransitionDecl :=
  { name := "Dirt", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage DirtRef] ] }

def vatTransition (v : DogImmutables) : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [vatExpr v] ] }

def chopTransition : TransitionDecl :=
  { name := "chop"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (ilksF (.var "ilk") "chop")] ] }

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

def fileAddressTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") vowParamLit)
          [ .assign .storage vowRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def fileUintTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") HoleParamLit)
          [ .assign .storage HoleRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def fileIlkUintTransition : TransitionDecl :=
  { name := "file"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "what", ty := bytes32 },
        { name := "data", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") chopParamLit)
          [ .require (.binary .ge (.var "data") (.intLit WAD)),
            .assign .storage (ilksF (.var "ilk") "chop") (.var "data") ]
          [ .ite
              (.binary .eq (.var "what") holeParamLit)
              [ .assign .storage (ilksF (.var "ilk") "hole") (.var "data") ]
              [ .require (.boolLit false) ] ] ] }

def fileIlkClipTransition : TransitionDecl :=
  { name := "file"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "what", ty := bytes32 },
        { name := "clip", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") clipParamLit)
          (checkedExternalCallStmts (.var "clip") "ilk" (.intLit 0) [] "clipIlk" (perm := false) ++
            [ .require (.binary .eq (.var "ilk") (.var "clipIlk")),
              .assign .storage (ilksF (.var "ilk") "clip") (.var "clip") ])
          [ .require (.boolLit false) ] ] }

def barkTransition (v : DogImmutables) : TransitionDecl :=
  { name := "bark"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "urn", ty := addr },
        { name := "kpr", ty := addr } ]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)) ] ++
      checkedExternalCallStmts (vatExpr v) "urns" (.intLit 0)
        [.var "ilk", .var "urn"] "vatUrn" (perm := false) ++
      [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
        .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
        .letDecl "milkClip" (some addr) (.storage (ilksF (.var "ilk") "clip")),
        .letDecl "milkChop" (some uint256) (.storage (ilksF (.var "ilk") "chop")),
        .letDecl "milkHole" (some uint256) (.storage (ilksF (.var "ilk") "hole")),
        .letDecl "milkDirt" (some uint256) (.storage (ilksF (.var "ilk") "dirt")) ] ++
      checkedExternalCallStmts (vatExpr v) "ilks" (.intLit 0)
        [.var "ilk"] "vatIlk" (perm := false) ++
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2),
        .letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4) ] ++
      checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
      checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
      [ .require
          (.binary .and
            (.binary .gt (.var "spot") (.intLit 0))
            (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))),
        .require
          (.binary .and
            (.binary .gt (.storage HoleRef) (.storage DirtRef))
            (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
      checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
      checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
      [ .internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room" ] ++
      checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
      [ .letDecl "dartByRate" (some uint256) (.binary .div (.var "roomWad") (.var "rate")),
        .letDecl "dartCandidate" (some uint256)
          (.binary .div (.var "dartByRate") (.var "milkChop")),
        .internalCall "min" [.var "art", .var "dartCandidate"] "dart",
        .ite
          (.binary .gt (.var "art") (.var "dart"))
          (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
            checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
            [ .ite
                (.binary .lt (.var "leftoverDue") (.var "dust"))
                [ .assign .localVar (varRef "dart") (.var "art") ]
                (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                  [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
          [] ] ++
      checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
      [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
        .require (.binary .gt (.var "dink") (.intLit 0)),
        .require
          (.binary .and
            (.binary .le (.var "dart") (.intLit int256Limit))
            (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
      checkedExternalCallStmts (vatExpr v) "grab" (.intLit 0)
        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
          .unary .neg (asInt256 (.var "dink")),
          .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
      checkedMulUintInto "due" (.var "dart") (.var "rate") ++
      checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
      checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
      [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
      checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
      [ .assign .storage DirtRef (.var "DirtNew") ] ++
      checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
      [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
      checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
        [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
      [ .return [.var "id"] ] }

def digsTransition : TransitionDecl :=
  { name := "digs"
    params := [{ name := "ilk", ty := bytes32 }, { name := "rad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .internalCall "sub" [.storage DirtRef, .var "rad"] "DirtNew",
        .assign .storage DirtRef (.var "DirtNew"),
        .internalCall "sub" [.storage (ilksF (.var "ilk") "dirt"), .var "rad"] "ilkDirtNew",
        .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage liveRef (.intLit 0) ] }

def transitions (v : DogImmutables) : List TransitionDecl :=
  [DirtTransition,
   HoleTransition,
   barkTransition v,
   cageTransition,
   chopTransition,
   denyTransition,
   digsTransition,
   fileIlkUintTransition,
   fileUintTransition,
   fileAddressTransition,
   fileIlkClipTransition,
   ilksTransition,
   liveTransition,
   relyTransition,
   vatTransition v,
   vowTransition,
   wardsTransition]

def contract (v : DogImmutables) : ContractDecl :=
  { name := "Dog"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := functions
    transitions := transitions v }

def config (_v : DogImmutables) : Config :=
  { storage := storageLayout
    externalABI := externalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment constructorDecl.params }

end Benchmarks.Dss.Dog
