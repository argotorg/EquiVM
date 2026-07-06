import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Cat benchmark spec

Faithful Solm benchmark scaffold for upstream `dss/src/cat.sol`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI

namespace Benchmarks.Dss.Cat

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
def vowAddr : Expr := .storage { base := "vow" }
def WAD : Int := 1000000000000000000
def int256Limit : Int := 57896044618658097711785492504343953926634992332820282019728792003956564819968

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)
def asInt256 (e : Expr) : Expr := .cast e int256St

def zeroPad29 : List UInt8 := List.replicate 29 0
def zeroPad28 : List UInt8 := List.replicate 28 0

def vowParamLit : Expr :=
  .fixedBytesLit bytes32Width ([118, 111, 119] ++ zeroPad29)

def boxParamLit : Expr :=
  .fixedBytesLit bytes32Width ([98, 111, 120] ++ zeroPad29)

def chopParamLit : Expr :=
  .fixedBytesLit bytes32Width ([99, 104, 111, 112] ++ zeroPad28)

def dunkParamLit : Expr :=
  .fixedBytesLit bytes32Width ([100, 117, 110, 107] ++ zeroPad28)

def flipParamLit : Expr :=
  .fixedBytesLit bytes32Width ([102, 108, 105, 112] ++ zeroPad28)

/-! ## External ABI for VatLike, VowLike, and Kicker -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def vatGrabSelector : ByteArray := selectorBytes 0x7b 0xab 0x3f 0x40
def vatHopeSelector : ByteArray := selectorBytes 0xa3 0xb2 0x2f 0xc4
def vatIlksSelector : ByteArray := selectorBytes 0xd9 0x63 0x8d 0x36
def vatNopeSelector : ByteArray := selectorBytes 0xdc 0x4d 0x20 0xfa
def vatUrnsSelector : ByteArray := selectorBytes 0x24 0x24 0xbe 0x5c
def vowFessSelector : ByteArray := selectorBytes 0x69 0x7e 0xfb 0x78
def kickerKickSelector : ByteArray := selectorBytes 0x35 0x1d 0xe6 0x00

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "grab" then
      ABI.encodeCallWithSelector? vatGrabSelector
        [bytes32, addr, addr, addr, int256, int256] args
    else if name = "hope" then
      ABI.encodeCallWithSelector? vatHopeSelector [addr] args
    else if name = "ilks" then
      ABI.encodeCallWithSelector? vatIlksSelector [bytes32] args
    else if name = "nope" then
      ABI.encodeCallWithSelector? vatNopeSelector [addr] args
    else if name = "urns" then
      ABI.encodeCallWithSelector? vatUrnsSelector [bytes32, addr] args
    else if name = "fess" then
      ABI.encodeCallWithSelector? vowFessSelector [uint256] args
    else if name = "kick" then
      ABI.encodeCallWithSelector? kickerKickSelector [addr, addr, uint256, uint256, uint256] args
    else
      none
  decode? := fun name out =>
    if name = "ilks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out
    else if name = "urns" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out
    else if name = "kick" then
      decodeReturn? uint256 out
    else if name = "grab" then
      decodeVoid? out
    else if name = "hope" then
      decodeVoid? out
    else if name = "nope" then
      decodeVoid? out
    else if name = "fess" then
      decodeVoid? out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def ilksF (ilk : Expr) (field : Ident) : StorageRef :=
  { base := "ilks", steps := [.mindex ilk, .field field] }

def liveRef : StorageRef := { base := "live" }
def vatRef : StorageRef := { base := "vat" }
def vowRef : StorageRef := { base := "vow" }
def boxRef : StorageRef := { base := "box" }
def litterRef : StorageRef := { base := "litter" }

/-! ## Storage declarations and layout -/

def IlkStructTy : StorageType :=
  .struct "Ilk" [("flip", addrSt), ("chop", uint256St), ("dunk", uint256St)]

def IlkStructDecl : StructDecl :=
  { name := "Ilk"
    fields :=
      [ { name := "flip", ty := addrSt },
        { name := "chop", ty := uint256St },
        { name := "dunk", ty := uint256St } ] }

def structs : List StructDecl := [IlkStructDecl]

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "live", ty := uint256St },
    { name := "vat", ty := addrSt },
    { name := "vow", ty := addrSt },
    { name := "box", ty := uint256St },
    { name := "litter", ty := uint256St } ]

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
  | { base := "ilks", steps := [.mindex ilk, .field "flip"] }, _ =>
      some (addrLoc (ilksBase ilk))
  | { base := "ilks", steps := [.mindex ilk, .field "chop"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨1⟩))
  | { base := "ilks", steps := [.mindex ilk, .field "dunk"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨2⟩))
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨2⟩)
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨3⟩)
  | { base := "vow", steps := [] }, _ => some (addrLoc ⟨4⟩)
  | { base := "box", steps := [] }, _ => some (wordLoc ⟨5⟩)
  | { base := "litter", steps := [] }, _ => some (wordLoc ⟨6⟩)
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

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "vat_", ty := addr }]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage liveRef (.intLit 1) ] }

/-! ## Internal functions -/

def minFunction : FunctionDecl :=
  { name := "min"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .ite
          (.binary .gt (.var "x") (.var "y"))
          [ .return [.var "y"] ]
          [ .return [.var "x"] ] ] }

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
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def ilksTransition : TransitionDecl :=
  { name := "ilks"
    params := [{ name := "arg0", ty := bytes32 }]
    returnType := [addr, uint256, uint256]
    body :=
      nonpayable ++
      [ .return
          [ .storage (ilksF (.var "arg0") "flip"),
            .storage (ilksF (.var "arg0") "chop"),
            .storage (ilksF (.var "arg0") "dunk") ] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def vowTransition : TransitionDecl :=
  { name := "vow", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vowRef] ] }

def boxTransition : TransitionDecl :=
  { name := "box", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage boxRef] ] }

def litterTransition : TransitionDecl :=
  { name := "litter", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage litterRef] ] }

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
          (.binary .eq (.var "what") boxParamLit)
          [ .assign .storage boxRef (.var "data") ]
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
          [ .assign .storage (ilksF (.var "ilk") "chop") (.var "data") ]
          [ .ite
              (.binary .eq (.var "what") dunkParamLit)
              [ .assign .storage (ilksF (.var "ilk") "dunk") (.var "data") ]
              [ .require (.boolLit false) ] ] ] }

def fileIlkFlipTransition : TransitionDecl :=
  { name := "file"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "what", ty := bytes32 },
        { name := "flip", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") flipParamLit)
          (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
              [.storage (ilksF (.var "ilk") "flip")] "_nopeRet" ++
            [ .assign .storage (ilksF (.var "ilk") "flip") (.var "flip") ] ++
            checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
              [.var "flip"] "_hopeRet")
          [ .require (.boolLit false) ] ] }

def biteTransition : TransitionDecl :=
  { name := "bite"
    params := [{ name := "ilk", ty := bytes32 }, { name := "urn", ty := addr }]
    returnType := [uint256]
    body :=
      nonpayable ++
      -- VatLike.ilks/urns are `view` in cat.sol → STATICCALL (perm := false)
      checkedExternalCallStmts (.storage vatRef) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
        (perm := false) ++
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2),
        .letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4) ] ++
      checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
        [.var "ilk", .var "urn"] "vatUrn" (perm := false) ++
      [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
        .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ] ++
      checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
      checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
      [ .require
          (.binary .and
            (.binary .gt (.var "spot") (.intLit 0))
            (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))),
        .letDecl "milkFlip" (some addr) (.storage (ilksF (.var "ilk") "flip")),
        .letDecl "milkChop" (some uint256) (.storage (ilksF (.var "ilk") "chop")),
        .letDecl "milkDunk" (some uint256) (.storage (ilksF (.var "ilk") "dunk")) ] ++
      checkedSubUintInto "room" (.storage boxRef) (.storage litterRef) ++
      [ .require
          (.binary .and
            (.binary .lt (.storage litterRef) (.storage boxRef))
            (.binary .ge (.var "room") (.var "dust"))),
        .internalCall "min" [.var "milkDunk", .var "room"] "dunkRoom" ] ++
      checkedMulUintInto "dunkRoomWad" (.var "dunkRoom") (.intLit WAD) ++
      [ .letDecl "dartDenomRate" (some uint256)
          (.binary .div (.var "dunkRoomWad") (.var "rate")),
        .letDecl "dartCandidate" (some uint256)
          (.binary .div (.var "dartDenomRate") (.var "milkChop")),
        .internalCall "min" [.var "art", .var "dartCandidate"] "dart" ] ++
      checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
      [ .letDecl "dinkCandidate" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
        .internalCall "min" [.var "ink", .var "dinkCandidate"] "dink",
        .require
          (.binary .and
            (.binary .gt (.var "dart") (.intLit 0))
            (.binary .gt (.var "dink") (.intLit 0))),
        .require
          (.binary .and
            (.binary .le (.var "dart") (.intLit int256Limit))
            (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
      checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [ .var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "dink")),
          .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
      checkedMulUintInto "dartRate" (.var "dart") (.var "rate") ++
      checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "dartRate"] "_fessRet" ++
      checkedMulUintInto "tabBase" (.var "dartRate") (.var "milkChop") ++
      [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
      checkedAddUintInto "litterNew" (.storage litterRef) (.var "tab") ++
      [ .assign .storage litterRef (.var "litterNew") ] ++
      checkedExternalCallStmts (.var "milkFlip") "kick" (.intLit 0)
        [.var "urn", vowAddr, .var "tab", .var "dink", .intLit 0] "id" ++
      [ .return [.var "id"] ] }

def clawTransition : TransitionDecl :=
  { name := "claw"
    params := [{ name := "rad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .internalCall "sub" [.storage litterRef, .var "rad"] "litterNew",
        .assign .storage litterRef (.var "litterNew") ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage liveRef (.intLit 0) ] }

def transitions : List TransitionDecl :=
  [biteTransition,
   boxTransition,
   cageTransition,
   clawTransition,
   denyTransition,
   fileAddressTransition,
   fileIlkFlipTransition,
   fileIlkUintTransition,
   fileUintTransition,
   ilksTransition,
   litterTransition,
   liveTransition,
   relyTransition,
   vatTransition,
   vowTransition,
   wardsTransition]

def contract : ContractDecl :=
  { name := "Cat"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Cat
