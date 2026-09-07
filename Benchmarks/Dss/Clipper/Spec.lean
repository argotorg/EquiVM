import Solm.Semantics
import Solm.SolidityLayout
import Benchmarks.Dss.Clipper.Immutables

/-!
# MakerDAO/Sky DSS Clipper benchmark spec

Faithful Solm benchmark spec for upstream `dss/src/clip.sol`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint192Int : IntType := .uint ⟨192, by decide⟩
def uint96Int : IntType := .uint ⟨96, by decide⟩
def uint64Int : IntType := .uint ⟨64, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def uint192 : ABIType := .elem (.int uint192Int)
def uint96 : ABIType := .elem (.int uint96Int)
def uint64 : ABIType := .elem (.int uint64Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def bytesDyn : ABIType := .bytes
def uint256Array : ABIType := .dynamicArray uint256

def uint256St : StorageType := .elem (.int uint256Int)
def uint192St : StorageType := .elem (.int uint192Int)
def uint96St : StorageType := .elem (.int uint96Int)
def uint64St : StorageType := .elem (.int uint64Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def BLN : Int := 1000000000
def WAD : Int := 1000000000000000000
def RAY : Int := 1000000000000000000000000000
def wordModulus : Int := (2 : Int) ^ 256
def uint96Modulus : Int := (2 : Int) ^ 96
def uint64Modulus : Int := (2 : Int) ^ 64
def uint192Modulus : Int := (2 : Int) ^ 192

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)
def wrap256 (e : Expr) : Expr := .binary .mod e (.intLit wordModulus)
def wrap96 (e : Expr) : Expr := .binary .mod e (.intLit uint96Modulus)
def wrap64 (e : Expr) : Expr := .binary .mod e (.intLit uint64Modulus)
def wrap192 (e : Expr) : Expr := .binary .mod e (.intLit uint192Modulus)
def tuple0 (e : Expr) : Expr := .tupleGet e 0
def tuple1 (e : Expr) : Expr := .tupleGet e 1

def zeroPad29 : List UInt8 := List.replicate 29 0
def zeroPad28 : List UInt8 := List.replicate 28 0
def zeroPad26 : List UInt8 := List.replicate 26 0
def zeroPad25 : List UInt8 := List.replicate 25 0

def bufParamLit : Expr := .fixedBytesLit bytes32Width ([98, 117, 102] ++ zeroPad29)
def tailParamLit : Expr := .fixedBytesLit bytes32Width ([116, 97, 105, 108] ++ zeroPad28)
def cuspParamLit : Expr := .fixedBytesLit bytes32Width ([99, 117, 115, 112] ++ zeroPad28)
def chipParamLit : Expr := .fixedBytesLit bytes32Width ([99, 104, 105, 112] ++ zeroPad28)
def tipParamLit : Expr := .fixedBytesLit bytes32Width ([116, 105, 112] ++ zeroPad29)
def stoppedParamLit : Expr := .fixedBytesLit bytes32Width ([115, 116, 111, 112, 112, 101, 100] ++ zeroPad25)
def spotterParamLit : Expr := .fixedBytesLit bytes32Width ([115, 112, 111, 116, 116, 101, 114] ++ zeroPad25)
def dogParamLit : Expr := .fixedBytesLit bytes32Width ([100, 111, 103] ++ zeroPad29)
def vowParamLit : Expr := .fixedBytesLit bytes32Width ([118, 111, 119] ++ zeroPad29)
def calcParamLit : Expr := .fixedBytesLit bytes32Width ([99, 97, 108, 99] ++ zeroPad28)

def localRef (name : Ident) : StorageRef := { base := name }
def bytesLength (name : Ident) : Expr := .arrayLength .localVar (localRef name)

/-! ## External ABI -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def priceSelector : ByteArray := selectorBytes 0x48 0x7a 0x23 0x95
def clipperCallSelector : ByteArray := selectorBytes 0x84 0x52 0xc1 0x0e
def dogChopSelector : ByteArray := selectorBytes 0xd7 0x92 0x65 0x38
def dogDigsSelector : ByteArray := selectorBytes 0xc8 0x71 0x93 0xf4
def pipPeekSelector : ByteArray := selectorBytes 0x59 0xe0 0x2d 0xd7
def spotterIlksSelector : ByteArray := selectorBytes 0xd9 0x63 0x8d 0x36
def spotterParSelector : ByteArray := selectorBytes 0x49 0x5d 0x32 0xcb
def vatFluxSelector : ByteArray := selectorBytes 0x61 0x11 0xbe 0x2e
def vatIlksSelector : ByteArray := selectorBytes 0xd9 0x63 0x8d 0x36
def vatMoveSelector : ByteArray := selectorBytes 0xbb 0x35 0x78 0x3b
def vatSuckSelector : ByteArray := selectorBytes 0xf2 0x4e 0x23 0xeb

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) := some []

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "price" then
      ABI.encodeCallWithSelector? priceSelector [uint256, uint256] args
    else if name = "clipperCall" then
      ABI.encodeCallWithSelector? clipperCallSelector [addr, uint256, uint256, bytesDyn] args
    else if name = "chop" then
      ABI.encodeCallWithSelector? dogChopSelector [bytes32] args
    else if name = "digs" then
      ABI.encodeCallWithSelector? dogDigsSelector [bytes32, uint256] args
    else if name = "peek" then
      match args with | [] => some pipPeekSelector | _ => none
    else if name = "spotterIlks" then
      ABI.encodeCallWithSelector? spotterIlksSelector [bytes32] args
    else if name = "par" then
      match args with | [] => some spotterParSelector | _ => none
    else if name = "flux" then
      ABI.encodeCallWithSelector? vatFluxSelector [bytes32, addr, addr, uint256] args
    else if name = "vatIlks" then
      ABI.encodeCallWithSelector? vatIlksSelector [bytes32] args
    else if name = "move" then
      ABI.encodeCallWithSelector? vatMoveSelector [addr, addr, uint256] args
    else if name = "suck" then
      ABI.encodeCallWithSelector? vatSuckSelector [addr, addr, uint256] args
    else
      none
  decode? := fun name out =>
    if name = "price" then
      decodeReturn? uint256 out
    else if name = "clipperCall" then
      decodeVoid? out
    else if name = "chop" then
      decodeReturn? uint256 out
    else if name = "digs" then
      decodeVoid? out
    else if name = "peek" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [bytes32, boolTy] out
    else if name = "spotterIlks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256] out
    else if name = "par" then
      decodeReturn? uint256 out
    else if name = "flux" then
      decodeVoid? out
    else if name = "vatIlks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out
    else if name = "move" then
      decodeVoid? out
    else if name = "suck" then
      decodeVoid? out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef := { base := "wards", steps := [.mindex usr] }
def activeRef : StorageRef := { base := "active" }
def activeElemRef (idx : Expr) : StorageRef := { base := "active", steps := [.aindex idx] }
def saleRef (id : Expr) : StorageRef := { base := "sales", steps := [.mindex id] }
def salesF (id : Expr) (field : Ident) : StorageRef :=
  { base := "sales", steps := [.mindex id, .field field] }

def dogRef : StorageRef := { base := "dog" }
def vowRef : StorageRef := { base := "vow" }
def spotterRef : StorageRef := { base := "spotter" }
def calcRef : StorageRef := { base := "calc" }
def bufRef : StorageRef := { base := "buf" }
def tailRef : StorageRef := { base := "tail" }
def cuspRef : StorageRef := { base := "cusp" }
def chipRef : StorageRef := { base := "chip" }
def tipRef : StorageRef := { base := "tip" }
def chostRef : StorageRef := { base := "chost" }
def kicksRef : StorageRef := { base := "kicks" }
def lockedRef : StorageRef := { base := "locked" }
def stoppedRef : StorageRef := { base := "stopped" }
def varRef (name : Ident) : StorageRef := { base := name }

/-! ## Storage declarations and layout -/

def SaleStructTy : StorageType :=
  .struct "Sale"
    [ ("pos", uint256St), ("tab", uint256St), ("lot", uint256St),
      ("usr", addrSt), ("tic", uint96St), ("top", uint256St) ]

def SaleStructDecl : StructDecl :=
  { name := "Sale"
    fields :=
      [ { name := "pos", ty := uint256St },
        { name := "tab", ty := uint256St },
        { name := "lot", ty := uint256St },
        { name := "usr", ty := addrSt },
        { name := "tic", ty := uint96St },
        { name := "top", ty := uint256St } ] }

def structs : List StructDecl := [SaleStructDecl]

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "dog", ty := addrSt },
    { name := "vow", ty := addrSt },
    { name := "spotter", ty := addrSt },
    { name := "calc", ty := addrSt },
    { name := "buf", ty := uint256St },
    { name := "tail", ty := uint256St },
    { name := "cusp", ty := uint256St },
    { name := "chip", ty := uint64St },
    { name := "tip", ty := uint192St },
    { name := "chost", ty := uint256St },
    { name := "kicks", ty := uint256St },
    { name := "active", ty := .dynamicArray uint256St },
    { name := "sales", ty := .mapping (.int uint256Int) SaleStructTy },
    { name := "locked", ty := uint256St },
    { name := "stopped", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord usr) ⟨0⟩
def activeDataSlot : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (Ethereum.UInt256.toByteArray ⟨11⟩))
def activeSlot (idx : KeyValue) : Ethereum.UInt256 := activeDataSlot + keyValueToWord idx
def salesBase (id : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord id) ⟨12⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }
def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }
def uint64Loc (slot : Ethereum.UInt256) (offset : Fin 32)
    (hbound : offset.val + 8 - 1 < 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 8, hbound := hbound, type := .int uint64Int }
def uint96Loc (slot : Ethereum.UInt256) (offset : Fin 32)
    (hbound : offset.val + 12 - 1 < 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 12, hbound := hbound, type := .int uint96Int }
def uint192Loc (slot : Ethereum.UInt256) (offset : Fin 32)
    (hbound : offset.val + 24 - 1 < 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 24, hbound := hbound, type := .int uint192Int }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "dog", steps := [] }, _ => some (addrLoc ⟨1⟩)
  | { base := "vow", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "spotter", steps := [] }, _ => some (addrLoc ⟨3⟩)
  | { base := "calc", steps := [] }, _ => some (addrLoc ⟨4⟩)
  | { base := "buf", steps := [] }, _ => some (wordLoc ⟨5⟩)
  | { base := "tail", steps := [] }, _ => some (wordLoc ⟨6⟩)
  | { base := "cusp", steps := [] }, _ => some (wordLoc ⟨7⟩)
  | { base := "chip", steps := [] }, _ => some (uint64Loc ⟨8⟩ ⟨0, by decide⟩ (by decide))
  | { base := "tip", steps := [] }, _ => some (uint192Loc ⟨8⟩ ⟨8, by decide⟩ (by decide))
  | { base := "chost", steps := [] }, _ => some (wordLoc ⟨9⟩)
  | { base := "kicks", steps := [] }, _ => some (wordLoc ⟨10⟩)
  | { base := "active", steps := [.length] }, _ => some (wordLoc ⟨11⟩)
  | { base := "active", steps := [.aindex idx] }, _ => some (wordLoc (activeSlot idx))
  | { base := "sales", steps := [.mindex id, .field "pos"] }, _ => some (wordLoc (salesBase id))
  | { base := "sales", steps := [.mindex id, .field "tab"] }, _ => some (wordLoc (salesBase id + ⟨1⟩))
  | { base := "sales", steps := [.mindex id, .field "lot"] }, _ => some (wordLoc (salesBase id + ⟨2⟩))
  | { base := "sales", steps := [.mindex id, .field "usr"] }, _ => some (addrLoc (salesBase id + ⟨3⟩))
  | { base := "sales", steps := [.mindex id, .field "tic"] }, _ =>
      some (uint96Loc (salesBase id + ⟨3⟩) ⟨20, by decide⟩ (by decide))
  | { base := "sales", steps := [.mindex id, .field "top"] }, _ => some (wordLoc (salesBase id + ⟨4⟩))
  | { base := "locked", steps := [] }, _ => some (wordLoc ⟨13⟩)
  | { base := "stopped", steps := [] }, _ => some (wordLoc ⟨14⟩)
  | _, _ => none

def storageLayout : StorageLayout := solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt := [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]
def auth : List Stmt := [ .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]
def lockPrefix : List Stmt :=
  [ .require (.binary .eq (.storage lockedRef) (.intLit 0)),
    .assign .storage lockedRef (.intLit 1) ]
def unlock : List Stmt := [ .assign .storage lockedRef (.intLit 0) ]
def isStopped (level : Int) : List Stmt :=
  [ .require (.binary .lt (.storage stoppedRef) (.intLit level)) ]

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
-- Built-in wrapping `+`/`-` (bare solc `ADD`/`SUB`), unlike the reverting DSMath `add`/`sub` above.
def wrappingSubInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (wrap256 (.binary .sub x y)) ]
def wrappingAddInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (wrap256 (.binary .add x y)) ]

/-! ## Constructor and internal functions -/

def constructorDecl : ConstructorDecl :=
  { params :=
      [ { name := "vat_", ty := addr }, { name := "spotter_", ty := addr },
        { name := "dog_", ty := addr }, { name := "ilk_", ty := bytes32 } ]
    body :=
      [ .assign .storage stoppedRef (.intLit 0) ] ++ nonpayable ++
      [ .letDecl "imm_vat" (some addr) (.var "vat_"),
        .letDecl "imm_ilk" (some bytes32) (.var "ilk_"),
        .assign .storage spotterRef (.var "spotter_"),
        .assign .storage dogRef (.var "dog_"),
        .assign .storage bufRef (.intLit RAY),
        .assign .storage (wardsRef sender) (.intLit 1) ] }

def minFunction : FunctionDecl :=
  { name := "min", params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }],
    returnType := [uint256],
    body := [ .ite (.binary .le (.var "x") (.var "y")) [ .return [.var "x"] ] [ .return [.var "y"] ] ] }
def addFunction : FunctionDecl :=
  { name := "add", params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }],
    returnType := [uint256],
    body := checkedAddUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }
def subFunction : FunctionDecl :=
  { name := "sub", params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }],
    returnType := [uint256],
    body := checkedSubUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }
def mulFunction : FunctionDecl :=
  { name := "mul", params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }],
    returnType := [uint256],
    body := checkedMulUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }
def wmulFunction : FunctionDecl :=
  { name := "wmul", params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }],
    returnType := [uint256],
    body := [ .internalCall "mul" [.var "x", .var "y"] "xy", .return [.binary .div (.var "xy") (.intLit WAD)] ] }
def rmulFunction : FunctionDecl :=
  { name := "rmul", params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }],
    returnType := [uint256],
    body := [ .internalCall "mul" [.var "x", .var "y"] "xy", .return [.binary .div (.var "xy") (.intLit RAY)] ] }
def rdivFunction : FunctionDecl :=
  { name := "rdiv", params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }],
    returnType := [uint256],
    body := [ .internalCall "mul" [.var "x", .intLit RAY] "xray", .return [.binary .div (.var "xray") (.var "y")] ] }

def getFeedPriceFunction (v : ClipperImmutables) : FunctionDecl :=
  { name := "getFeedPrice"
    params := []
    returnType := [uint256]
    body :=
      checkedExternalCallStmts (.storage spotterRef) "spotterIlks" (.intLit 0)
        [ilkExpr v] "spotterIlk" ++
      [ .letDecl "pip" (some addr) (tuple0 (.var "spotterIlk")) ] ++
      checkedExternalCallStmts (.var "pip") "peek" (.intLit 0) [] "peekRet" ++
      [ .letDecl "val" (some bytes32) (tuple0 (.var "peekRet")),
        .letDecl "has" (some boolTy) (tuple1 (.var "peekRet")),
        .require (.var "has") ] ++
      checkedMulUintInto "valBln" (.cast (.var "val") uint256St) (.intLit BLN) ++
      checkedExternalCallStmts (.storage spotterRef) "par" (.intLit 0) [] "par" ++
      [ .internalCall "rdiv" [.var "valBln", .var "par"] "feedPrice",
        .return [.var "feedPrice"] ] }

def statusFunction : FunctionDecl :=
  { name := "status"
    params := [{ name := "tic", ty := uint96 }, { name := "top", ty := uint256 }]
    returnType := [boolTy, uint256]
    body :=
      [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForPrice" ] ++
      checkedExternalCallStmts (.storage calcRef) "price" (.intLit 0)
        [.var "top", .var "ageForPrice"] "price" (perm := false) ++
      [ .internalCall "sub" [.env .timestamp, .var "tic"] "ageForDone",
        -- `done = age > tail || rdiv(price, top) < cusp`, short-circuited: `rdiv` (which can revert
        -- on `top == 0` or `price * RAY` overflow) is only evaluated when `age > tail` is false.
        .letDecl "done" (some boolTy) (.boolLit false),
        .ite (.binary .gt (.var "ageForDone") (.storage tailRef))
          [ .assign .localVar (varRef "done") (.boolLit true) ]
          ([ .internalCall "rdiv" [.var "price", .var "top"] "ratio",
             .assign .localVar (varRef "done")
               (.binary .lt (.var "ratio") (.storage cuspRef)) ]),
        .return [.var "done", .var "price"] ] }

def removeFunction : FunctionDecl :=
  { name := "_remove"
    params := [{ name := "id", ty := uint256 }]
    returnType := []
    body :=
      [ .letDecl "lastIndex" (some uint256)
          (sub256 (.arrayLength .storage activeRef) (.intLit 1)),
        .letDecl "_move" (some uint256) (.storage (activeElemRef (.var "lastIndex"))),
        .ite
          (.binary .ne (.var "id") (.var "_move"))
          [ .letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
            .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
            .assign .storage (salesF (.var "_move") "pos") (.var "_index") ]
          [],
        .pop activeRef,
        .delete (saleRef (.var "id")) ] }

def functions (v : ClipperImmutables) : List FunctionDecl :=
  [minFunction, addFunction, subFunction, mulFunction, wmulFunction, rmulFunction, rdivFunction,
   getFeedPriceFunction v, statusFunction, removeFunction]

/-! ## Getters and views -/

def wardsTransition : TransitionDecl :=
  { name := "wards", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }
def dogTransition : TransitionDecl := { name := "dog", params := [], returnType := [addr], body := nonpayable ++ [ .return [.storage dogRef] ] }
def vowTransition : TransitionDecl := { name := "vow", params := [], returnType := [addr], body := nonpayable ++ [ .return [.storage vowRef] ] }
def spotterTransition : TransitionDecl := { name := "spotter", params := [], returnType := [addr], body := nonpayable ++ [ .return [.storage spotterRef] ] }
def calcTransition : TransitionDecl := { name := "calc", params := [], returnType := [addr], body := nonpayable ++ [ .return [.storage calcRef] ] }
def bufTransition : TransitionDecl := { name := "buf", params := [], returnType := [uint256], body := nonpayable ++ [ .return [.storage bufRef] ] }
def tailTransition : TransitionDecl := { name := "tail", params := [], returnType := [uint256], body := nonpayable ++ [ .return [.storage tailRef] ] }
def cuspTransition : TransitionDecl := { name := "cusp", params := [], returnType := [uint256], body := nonpayable ++ [ .return [.storage cuspRef] ] }
def chipTransition : TransitionDecl := { name := "chip", params := [], returnType := [uint64], body := nonpayable ++ [ .return [.storage chipRef] ] }
def tipTransition : TransitionDecl := { name := "tip", params := [], returnType := [uint192], body := nonpayable ++ [ .return [.storage tipRef] ] }
def chostTransition : TransitionDecl := { name := "chost", params := [], returnType := [uint256], body := nonpayable ++ [ .return [.storage chostRef] ] }
def kicksTransition : TransitionDecl := { name := "kicks", params := [], returnType := [uint256], body := nonpayable ++ [ .return [.storage kicksRef] ] }
def stoppedTransition : TransitionDecl := { name := "stopped", params := [], returnType := [uint256], body := nonpayable ++ [ .return [.storage stoppedRef] ] }
def activeTransition : TransitionDecl := { name := "active", params := [{ name := "arg0", ty := uint256 }], returnType := [uint256], body := nonpayable ++ [ .return [.storage (activeElemRef (.var "arg0"))] ] }
def vatTransition (v : ClipperImmutables) : TransitionDecl := { name := "vat", params := [], returnType := [addr], body := nonpayable ++ [ .return [vatExpr v] ] }
def ilkTransition (v : ClipperImmutables) : TransitionDecl := { name := "ilk", params := [], returnType := [bytes32], body := nonpayable ++ [ .return [ilkExpr v] ] }
def countTransition : TransitionDecl := { name := "count", params := [], returnType := [uint256], body := nonpayable ++ [ .return [.arrayLength .storage activeRef] ] }
def listTransition : TransitionDecl := { name := "list", params := [], returnType := [uint256Array], body := nonpayable ++ [ .return [.storage activeRef] ] }

def salesTransition : TransitionDecl :=
  { name := "sales", params := [{ name := "arg0", ty := uint256 }],
    returnType := [uint256, uint256, uint256, addr, uint96, uint256],
    body := nonpayable ++
      [ .return
          [ .storage (salesF (.var "arg0") "pos"),
            .storage (salesF (.var "arg0") "tab"),
            .storage (salesF (.var "arg0") "lot"),
            .storage (salesF (.var "arg0") "usr"),
            .storage (salesF (.var "arg0") "tic"),
            .storage (salesF (.var "arg0") "top") ] ] }

def getStatusTransition : TransitionDecl :=
  { name := "getStatus"
    params := [{ name := "id", ty := uint256 }]
    returnType := [boolTy, uint256, uint256, uint256]
    body := nonpayable ++
      [ .letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")),
        .letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")),
        .internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st",
        .letDecl "done" (some boolTy) (tuple0 (.var "st")),
        .letDecl "price" (some uint256) (tuple1 (.var "st")),
        .letDecl "needsRedo" (some boolTy)
          (.binary .and (.binary .ne (.var "usr") zeroAddr) (.var "done")),
        .return
          [ .var "needsRedo", .var "price",
            .storage (salesF (.var "id") "lot"),
            .storage (salesF (.var "id") "tab") ] ] }

/-! ## External transitions -/

def relyTransition : TransitionDecl :=
  { name := "rely", params := [{ name := "usr", ty := addr }], returnType := [],
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "usr")) (.intLit 1) ] }
def denyTransition : TransitionDecl :=
  { name := "deny", params := [{ name := "usr", ty := addr }], returnType := [],
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "usr")) (.intLit 0) ] }

def fileUintTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body := nonpayable ++ auth ++ lockPrefix ++
      [ .ite (.binary .eq (.var "what") bufParamLit) [ .assign .storage bufRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") tailParamLit) [ .assign .storage tailRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cuspParamLit) [ .assign .storage cuspRef (.var "data") ]
            [ .ite (.binary .eq (.var "what") chipParamLit) [ .assign .storage chipRef (wrap64 (.var "data")) ]
              [ .ite (.binary .eq (.var "what") tipParamLit) [ .assign .storage tipRef (wrap192 (.var "data")) ]
                [ .ite (.binary .eq (.var "what") stoppedParamLit) [ .assign .storage stoppedRef (.var "data") ]
                  [ .require (.boolLit false) ] ] ] ] ] ],
        .assign .storage lockedRef (.intLit 0) ] }

def fileAddressTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ lockPrefix ++
      [ .ite (.binary .eq (.var "what") spotterParamLit) [ .assign .storage spotterRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") dogParamLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowParamLit) [ .assign .storage vowRef (.var "data") ]
            [ .ite (.binary .eq (.var "what") calcParamLit) [ .assign .storage calcRef (.var "data") ]
              [ .require (.boolLit false) ] ] ] ],
        .assign .storage lockedRef (.intLit 0) ] }

def kickTransition (v : ClipperImmutables) : TransitionDecl :=
  { name := "kick"
    params :=
      [ { name := "tab", ty := uint256 }, { name := "lot", ty := uint256 },
        { name := "usr", ty := addr }, { name := "kpr", ty := addr } ]
    returnType := [uint256]
    body := nonpayable ++ auth ++ lockPrefix ++ isStopped 1 ++
      [ .require (.binary .gt (.var "tab") (.intLit 0)),
        .require (.binary .gt (.var "lot") (.intLit 0)),
        .require (.binary .ne (.var "usr") zeroAddr),
        .letDecl "id" (some uint256) (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))),
        .assign .storage kicksRef (.var "id"),
        .require (.binary .gt (.var "id") (.intLit 0)),
        .push activeRef (some (.var "id")) ] ++
      wrappingSubInto "activePos" (.arrayLength .storage activeRef) (.intLit 1) ++
      [ .assign .storage (salesF (.var "id") "pos") (.var "activePos"),
        .assign .storage (salesF (.var "id") "tab") (.var "tab"),
        .assign .storage (salesF (.var "id") "lot") (.var "lot"),
        .assign .storage (salesF (.var "id") "usr") (.var "usr"),
        .assign .storage (salesF (.var "id") "tic") (wrap96 (.env .timestamp)),
        .internalCall "getFeedPrice" [] "feedPrice",
        .internalCall "rmul" [.var "feedPrice", .storage bufRef] "top",
        .require (.binary .gt (.var "top") (.intLit 0)),
        .assign .storage (salesF (.var "id") "top") (.var "top"),
        .letDecl "_tip" (some uint256) (.storage tipRef),
        .letDecl "_chip" (some uint256) (.storage chipRef),
        .letDecl "coin" (some uint256) (.intLit 0),
        .ite
          (.binary .or (.binary .gt (.var "_tip") (.intLit 0)) (.binary .gt (.var "_chip") (.intLit 0)))
          ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
            checkedAddUintInto "coinNew" (.var "_tip") (.var "chipCoin") ++
            [ .assign .localVar (varRef "coin") (.var "coinNew") ] ++
            checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
              [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
          [],
        .assign .storage lockedRef (.intLit 0),
        .return [.var "id"] ] }

def redoTransition (v : ClipperImmutables) : TransitionDecl :=
  { name := "redo"
    params := [{ name := "id", ty := uint256 }, { name := "kpr", ty := addr }]
    returnType := []
    body := nonpayable ++ lockPrefix ++ isStopped 2 ++
      [ .letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")),
        .letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")),
        .letDecl "top" (some uint256) (.storage (salesF (.var "id") "top")),
        .require (.binary .ne (.var "usr") zeroAddr),
        .internalCall "status" [.var "tic", .var "top"] "st",
        .require (tuple0 (.var "st")),
        .letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")),
        .letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")),
        .assign .storage (salesF (.var "id") "tic") (wrap96 (.env .timestamp)),
        .internalCall "getFeedPrice" [] "feedPrice",
        .internalCall "rmul" [.var "feedPrice", .storage bufRef] "topNew",
        .require (.binary .gt (.var "topNew") (.intLit 0)),
        .assign .storage (salesF (.var "id") "top") (.var "topNew"),
        .letDecl "_tip" (some uint256) (.storage tipRef),
        .letDecl "_chip" (some uint256) (.storage chipRef),
        .ite
          (.binary .or (.binary .gt (.var "_tip") (.intLit 0)) (.binary .gt (.var "_chip") (.intLit 0)))
          -- `tab >= _chost && mul(lot, feedPrice) >= _chost`, short-circuited: `mul` (which can
          -- revert on overflow) is only evaluated when `tab >= _chost`.
          [ .letDecl "_chost" (some uint256) (.storage chostRef),
            .ite
              (.binary .ge (.var "tab") (.var "_chost"))
              (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
                [ .ite
                    (.binary .ge (.var "lotFeed") (.var "_chost"))
                    ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                      checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                      checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
                        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                    [] ])
              [] ]
          [],
        .assign .storage lockedRef (.intLit 0) ] }

def takeTransition (v : ClipperImmutables) : TransitionDecl :=
  { name := "take"
    params :=
      [ { name := "id", ty := uint256 }, { name := "amt", ty := uint256 },
        { name := "max", ty := uint256 }, { name := "who", ty := addr },
        { name := "data", ty := bytesDyn } ]
    returnType := []
    body := nonpayable ++ lockPrefix ++ isStopped 3 ++
      [ .letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")),
        .letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")),
        .require (.binary .ne (.var "usr") zeroAddr),
        .internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st",
        .letDecl "done" (some boolTy) (tuple0 (.var "st")),
        .letDecl "price" (some uint256) (tuple1 (.var "st")),
        .require (.unary .not (.var "done")),
        .require (.binary .ge (.var "max") (.var "price")),
        .letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")),
        .letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")),
        .internalCall "min" [.var "lot", .var "amt"] "slice" ] ++
      checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
      [ .letDecl "owe" (some uint256) (.var "owe0"),
        .ite
          (.binary .gt (.var "owe") (.var "tab"))
          [ .assign .localVar (varRef "owe") (.var "tab"),
            .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
          [ .ite
              (.binary .and (.binary .lt (.var "owe") (.var "tab")) (.binary .lt (.var "slice") (.var "lot")))
              ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
                wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
                [ .ite
                    (.binary .lt (.var "remainingTab") (.var "_chost"))
                    ( [ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                      wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                      [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                        .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ])
                    [] ])
              [] ] ] ++
      wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
      wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
      [ .assign .localVar (varRef "tab") (.var "tabNew"),
        .assign .localVar (varRef "lot") (.var "lotNew") ] ++
      checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet" ++
      [ .letDecl "dog_" (some addr) (.storage dogRef),
        .ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [] ] ++
      checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet" ++
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet"),
        .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ] }

def upchostTransition (v : ClipperImmutables) : TransitionDecl :=
  { name := "upchost"
    params := []
    returnType := []
    body := nonpayable ++
      checkedExternalCallStmts (vatExpr v) "vatIlks" (.intLit 0) [ilkExpr v] "vatIlk" ++
      [ .letDecl "_dust" (some uint256) (.tupleGet (.var "vatIlk") 4) ] ++
      checkedExternalCallStmts (.storage dogRef) "chop" (.intLit 0) [ilkExpr v] "chop" ++
      [ .internalCall "wmul" [.var "_dust", .var "chop"] "chostNew",
        .assign .storage chostRef (.var "chostNew") ] }

def yankTransition (v : ClipperImmutables) : TransitionDecl :=
  { name := "yank"
    params := [{ name := "id", ty := uint256 }]
    returnType := []
    body := nonpayable ++ auth ++ lockPrefix ++
      [ .require (.binary .ne (.storage (salesF (.var "id") "usr")) zeroAddr) ] ++
      checkedExternalCallStmts (.storage dogRef) "digs" (.intLit 0)
        [ilkExpr v, .storage (salesF (.var "id") "tab")] "_digsRet" ++
      checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, sender, .storage (salesF (.var "id") "lot")] "_fluxRet" ++
      [ .internalCall "_remove" [.var "id"] "_removeRet",
        .assign .storage lockedRef (.intLit 0) ] }

def transitions (v : ClipperImmutables) : List TransitionDecl :=
  [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
   countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
   fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
   kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
   spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
   upchostTransition v, vatTransition v, vowTransition, wardsTransition, yankTransition v]

def contract (v : ClipperImmutables) : ContractDecl :=
  { name := "Clipper"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := functions v
    transitions := transitions v }

def config (v : ClipperImmutables) : Config :=
  { storage := storageLayout
    externalABI := externalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment (contract v).ctor.params }

end Benchmarks.Dss.Clipper
