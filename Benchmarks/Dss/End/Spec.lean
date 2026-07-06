import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS End benchmark spec

Faithful Solm benchmark spec for upstream `dss/src/end.sol` (global settlement engine).
Events are omitted, matching the existing event-bearing DSS benchmarks.

Two modelling notes, both behaviour-preserving:
* `u256 e = .inRange uint256Int e` reverts on overflow, so the DSS `add/sub/mul` checks are
  modelled by computing the unbounded result and range-checking it — same revert-iff-overflow
  behaviour as the wrapped EVM arithmetic plus the require.
* `int256(x)` is bit-identity on non-negative values here, so `-int256(x)` is `neg x`, and the
  guard `int256(x) >= 0` (snip/skip) is written as the equivalent `x < 2^255`.
-/

open Solm ABI

namespace Benchmarks.Dss.End

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def int256Int : IntType := .sint ⟨256, by decide⟩
def uint96Int : IntType := .uint ⟨96, by decide⟩
def uint48Int : IntType := .uint ⟨48, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def int256 : ABIType := .elem (.int int256Int)
def uint96 : ABIType := .elem (.int uint96Int)
def uint48 : ABIType := .elem (.int uint48Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def int256St : StorageType := .elem (.int int256Int)
def addrSt : StorageType := .elem .address

/-! ## Constants and expression helpers -/

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def nowT : Expr := .env .timestamp
def WAD : Int := 1000000000000000000
def RAY : Int := 1000000000000000000000000000
-- 2^255, the boundary for a value to fit in a non-negative int256.
def int256Limit : Int := 57896044618658097711785492504343953926634992332820282019728792003956564819968

def u256 (e : Expr) : Expr := .inRange uint256Int e
def asInt256 (e : Expr) : Expr := .cast e int256St

/-! ## bytes32 string literals for `file(what, ...)` (left-aligned ASCII) -/

def strLit3 (a b c : UInt8) : Expr := .fixedBytesLit bytes32Width ([a, b, c] ++ List.replicate 29 0)
def strLit4 (a b c d : UInt8) : Expr :=
  .fixedBytesLit bytes32Width ([a, b, c, d] ++ List.replicate 28 0)

def vatLit  : Expr := strLit3 118 97 116    -- "vat"
def catLit  : Expr := strLit3 99 97 116     -- "cat"
def dogLit  : Expr := strLit3 100 111 103   -- "dog"
def vowLit  : Expr := strLit3 118 111 119   -- "vow"
def potLit  : Expr := strLit3 112 111 116   -- "pot"
def spotLit : Expr := strLit4 115 112 111 116 -- "spot"
def cureLit : Expr := strLit4 99 117 114 101  -- "cure"
def waitLit : Expr := strLit4 119 97 105 116  -- "wait"

/-! ## External ABI

`End` calls `ilks(bytes32)` on four different contracts (vat/cat/dog/spot); all share the same
selector but decode to different return shapes, so they get distinct `name`s here. -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def cageSelector  : ByteArray := selectorBytes 0x69 0x24 0x50 0x09  -- cage()
def ilksSelector  : ByteArray := selectorBytes 0xd9 0x63 0x8d 0x36  -- ilks(bytes32)
def urnsSelector  : ByteArray := selectorBytes 0x24 0x24 0xbe 0x5c  -- urns(bytes32,address)
def daiSelector   : ByteArray := selectorBytes 0x6c 0x25 0xb3 0x46  -- dai(address)
def debtSelector  : ByteArray := selectorBytes 0x0d 0xca 0x59 0xc1  -- debt()
def moveSelector  : ByteArray := selectorBytes 0xbb 0x35 0x78 0x3b  -- move(address,address,uint256)
def hopeSelector  : ByteArray := selectorBytes 0xa3 0xb2 0x2f 0xc4  -- hope(address)
def fluxSelector  : ByteArray := selectorBytes 0x61 0x11 0xbe 0x2e  -- flux(bytes32,address,address,uint256)
def grabSelector  : ByteArray := selectorBytes 0x7b 0xab 0x3f 0x40  -- grab(bytes32,address,address,address,int256,int256)
def suckSelector  : ByteArray := selectorBytes 0xf2 0x4e 0x23 0xeb  -- suck(address,address,uint256)
def parSelector   : ByteArray := selectorBytes 0x49 0x5d 0x32 0xcb  -- par()
def tellSelector  : ByteArray := selectorBytes 0x53 0xd7 0x00 0xe5  -- tell()
def bidsSelector  : ByteArray := selectorBytes 0x44 0x23 0xc5 0xf1  -- bids(uint256)
def salesSelector : ByteArray := selectorBytes 0xb5 0xf5 0x22 0xf7  -- sales(uint256)
def readSelector  : ByteArray := selectorBytes 0x57 0xde 0x26 0xa4  -- read()
def yankSelector  : ByteArray := selectorBytes 0x26 0xe0 0x27 0xf1  -- yank(uint256)

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) := some []

def ilksEncode? (args : List Value) : Option ByteArray :=
  ABI.encodeCallWithSelector? ilksSelector [bytes32] args

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "cage" then (match args with | [] => some cageSelector | _ => none)
    else if name = "vatIlks" then ilksEncode? args
    else if name = "catIlks" then ilksEncode? args
    else if name = "dogIlks" then ilksEncode? args
    else if name = "spotIlks" then ilksEncode? args
    else if name = "urns" then ABI.encodeCallWithSelector? urnsSelector [bytes32, addr] args
    else if name = "dai" then ABI.encodeCallWithSelector? daiSelector [addr] args
    else if name = "debt" then (match args with | [] => some debtSelector | _ => none)
    else if name = "move" then ABI.encodeCallWithSelector? moveSelector [addr, addr, uint256] args
    else if name = "hope" then ABI.encodeCallWithSelector? hopeSelector [addr] args
    else if name = "flux" then
      ABI.encodeCallWithSelector? fluxSelector [bytes32, addr, addr, uint256] args
    else if name = "grab" then
      ABI.encodeCallWithSelector? grabSelector [bytes32, addr, addr, addr, int256, int256] args
    else if name = "suck" then ABI.encodeCallWithSelector? suckSelector [addr, addr, uint256] args
    else if name = "par" then (match args with | [] => some parSelector | _ => none)
    else if name = "tell" then (match args with | [] => some tellSelector | _ => none)
    else if name = "bids" then ABI.encodeCallWithSelector? bidsSelector [uint256] args
    else if name = "sales" then ABI.encodeCallWithSelector? salesSelector [uint256] args
    else if name = "read" then (match args with | [] => some readSelector | _ => none)
    else if name = "yank" then ABI.encodeCallWithSelector? yankSelector [uint256] args
    else none
  decode? := fun name out =>
    if name = "cage" then decodeVoid? out
    else if name = "vatIlks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out
    else if name = "catIlks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256, uint256] out
    else if name = "dogIlks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256, uint256, uint256] out
    else if name = "spotIlks" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256] out
    else if name = "urns" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out
    else if name = "dai" then decodeReturn? uint256 out
    else if name = "debt" then decodeReturn? uint256 out
    else if name = "par" then decodeReturn? uint256 out
    else if name = "tell" then decodeReturn? uint256 out
    else if name = "read" then decodeReturn? bytes32 out
    else if name = "bids" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, addr, uint48, uint48, addr, addr, uint256] out
    else if name = "sales" then
      ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, addr, uint96, uint256] out
    else if name = "move" then decodeVoid? out
    else if name = "hope" then decodeVoid? out
    else if name = "flux" then decodeVoid? out
    else if name = "grab" then decodeVoid? out
    else if name = "suck" then decodeVoid? out
    else if name = "yank" then decodeVoid? out
    else none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef := { base := "wards", steps := [.mindex usr] }
def vatRef  : StorageRef := { base := "vat" }
def catRef  : StorageRef := { base := "cat" }
def dogRef  : StorageRef := { base := "dog" }
def vowRef  : StorageRef := { base := "vow" }
def potRef  : StorageRef := { base := "pot" }
def spotRef : StorageRef := { base := "spot" }
def cureRef : StorageRef := { base := "cure" }
def liveRef : StorageRef := { base := "live" }
def whenRef : StorageRef := { base := "when" }
def waitRef : StorageRef := { base := "wait" }
def debtRef : StorageRef := { base := "debt" }
def tagRef (ilk : Expr) : StorageRef := { base := "tag", steps := [.mindex ilk] }
def gapRef (ilk : Expr) : StorageRef := { base := "gap", steps := [.mindex ilk] }
def ArtRef (ilk : Expr) : StorageRef := { base := "Art", steps := [.mindex ilk] }
def fixRef (ilk : Expr) : StorageRef := { base := "fix", steps := [.mindex ilk] }
def bagRef (usr : Expr) : StorageRef := { base := "bag", steps := [.mindex usr] }
def outRef (ilk usr : Expr) : StorageRef := { base := "out", steps := [.mindex ilk, .mindex usr] }

def vowAddr : Expr := .storage vowRef

/-! ## Storage declarations and layout (slots 0–17, sequential, no packing) -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "vat", ty := addrSt },
    { name := "cat", ty := addrSt },
    { name := "dog", ty := addrSt },
    { name := "vow", ty := addrSt },
    { name := "pot", ty := addrSt },
    { name := "spot", ty := addrSt },
    { name := "cure", ty := addrSt },
    { name := "live", ty := uint256St },
    { name := "when", ty := uint256St },
    { name := "wait", ty := uint256St },
    { name := "debt", ty := uint256St },
    { name := "tag", ty := .mapping (.bytes bytes32Width) uint256St },
    { name := "gap", ty := .mapping (.bytes bytes32Width) uint256St },
    { name := "Art", ty := .mapping (.bytes bytes32Width) uint256St },
    { name := "fix", ty := .mapping (.bytes bytes32Width) uint256St },
    { name := "bag", ty := .mapping .address uint256St },
    { name := "out", ty := .mapping (.bytes bytes32Width) (.mapping .address uint256St) } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord usr) ⟨0⟩
def tagSlot (ilk : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord ilk) ⟨12⟩
def gapSlot (ilk : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord ilk) ⟨13⟩
def ArtSlot (ilk : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord ilk) ⟨14⟩
def fixSlot (ilk : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord ilk) ⟨15⟩
def bagSlot (usr : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord usr) ⟨16⟩
def outIlkSlot (ilk : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord ilk) ⟨17⟩
def outSlot (ilk usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) (outIlkSlot ilk)

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨1⟩)
  | { base := "cat", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "dog", steps := [] }, _ => some (addrLoc ⟨3⟩)
  | { base := "vow", steps := [] }, _ => some (addrLoc ⟨4⟩)
  | { base := "pot", steps := [] }, _ => some (addrLoc ⟨5⟩)
  | { base := "spot", steps := [] }, _ => some (addrLoc ⟨6⟩)
  | { base := "cure", steps := [] }, _ => some (addrLoc ⟨7⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨8⟩)
  | { base := "when", steps := [] }, _ => some (wordLoc ⟨9⟩)
  | { base := "wait", steps := [] }, _ => some (wordLoc ⟨10⟩)
  | { base := "debt", steps := [] }, _ => some (wordLoc ⟨11⟩)
  | { base := "tag", steps := [.mindex ilk] }, _ => some (wordLoc (tagSlot ilk))
  | { base := "gap", steps := [.mindex ilk] }, _ => some (wordLoc (gapSlot ilk))
  | { base := "Art", steps := [.mindex ilk] }, _ => some (wordLoc (ArtSlot ilk))
  | { base := "fix", steps := [.mindex ilk] }, _ => some (wordLoc (fixSlot ilk))
  | { base := "bag", steps := [.mindex usr] }, _ => some (wordLoc (bagSlot usr))
  | { base := "out", steps := [.mindex ilk, .mindex usr] }, _ => some (wordLoc (outSlot ilk usr))
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

/-! ## Constructor and internal math functions -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage liveRef (.intLit 1) ] }

def addFunction : FunctionDecl :=
  { name := "add"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .letDecl "z" (some uint256) (u256 (.binary .add (.var "x") (.var "y"))),
        .require (.binary .ge (.var "z") (.var "x")),
        .return [.var "z"] ] }

def subFunction : FunctionDecl :=
  { name := "sub"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .letDecl "z" (some uint256) (u256 (.binary .sub (.var "x") (.var "y"))),
        .require (.binary .le (.var "z") (.var "x")),
        .return [.var "z"] ] }

def mulFunction : FunctionDecl :=
  { name := "mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .letDecl "z" (some uint256) (u256 (.binary .mul (.var "x") (.var "y"))),
        .require
          (.binary .or
            (.binary .eq (.var "y") (.intLit 0))
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
        .return [.var "z"] ] }

def minFunction : FunctionDecl :=
  { name := "min"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .ite (.binary .le (.var "x") (.var "y")) [ .return [.var "x"] ] [ .return [.var "y"] ] ] }

def rmulFunction : FunctionDecl :=
  { name := "rmul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .internalCall "mul" [.var "x", .var "y"] "m",
        .return [.binary .div (.var "m") (.intLit RAY)] ] }

def wdivFunction : FunctionDecl :=
  { name := "wdiv"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .internalCall "mul" [.var "x", .intLit WAD] "m",
        .return [.binary .div (.var "m") (.var "y")] ] }

def functions : List FunctionDecl :=
  [addFunction, subFunction, mulFunction, minFunction, rmulFunction, wdivFunction]

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def catTransition : TransitionDecl :=
  { name := "cat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage catRef] ] }

def dogTransition : TransitionDecl :=
  { name := "dog", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage dogRef] ] }

def vowTransition : TransitionDecl :=
  { name := "vow", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vowRef] ] }

def potTransition : TransitionDecl :=
  { name := "pot", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage potRef] ] }

def spotTransition : TransitionDecl :=
  { name := "spot", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage spotRef] ] }

def cureTransition : TransitionDecl :=
  { name := "cure", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage cureRef] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

def whenTransition : TransitionDecl :=
  { name := "when", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage whenRef] ] }

def waitTransition : TransitionDecl :=
  { name := "wait", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage waitRef] ] }

def debtTransition : TransitionDecl :=
  { name := "debt", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage debtRef] ] }

def tagTransition : TransitionDecl :=
  { name := "tag", params := [{ name := "arg0", ty := bytes32 }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (tagRef (.var "arg0"))] ] }

def gapTransition : TransitionDecl :=
  { name := "gap", params := [{ name := "arg0", ty := bytes32 }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (gapRef (.var "arg0"))] ] }

def ArtTransition : TransitionDecl :=
  { name := "Art", params := [{ name := "arg0", ty := bytes32 }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (ArtRef (.var "arg0"))] ] }

def fixTransition : TransitionDecl :=
  { name := "fix", params := [{ name := "arg0", ty := bytes32 }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (fixRef (.var "arg0"))] ] }

def bagTransition : TransitionDecl :=
  { name := "bag", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (bagRef (.var "arg0"))] ] }

def outTransition : TransitionDecl :=
  { name := "out"
    params := [{ name := "arg0", ty := bytes32 }, { name := "arg1", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (outRef (.var "arg0") (.var "arg1"))] ] }

/-! ## Administration -/

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
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") vatLit) [ .assign .storage vatRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
        [ .require (.boolLit false) ] ] ] ] ] ] ] ] }

def fileUintTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") waitLit) [ .assign .storage waitRef (.var "data") ]
        [ .require (.boolLit false) ] ] }

/-! ## Settlement -/

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .assign .storage liveRef (.intLit 0),
        .assign .storage whenRef nowT ] ++
      checkedExternalCallStmts (.storage vatRef) "cage" (.intLit 0) [] "_vatCage" ++
      checkedExternalCallStmts (.storage catRef) "cage" (.intLit 0) [] "_catCage" ++
      checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage" ++
      checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ++
      checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
      checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
      checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage" }

def cageIlkTransition : TransitionDecl :=
  { name := "cage"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
        .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ++
      [ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"] "spotIlk"
        (perm := false) ++
      [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
      checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV" (perm := false) ++
      checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead" (perm := false) ++
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ] }

def snipTransition : TransitionDecl :=
  { name := "snip"
    params := [{ name := "ilk", ty := bytes32 }, { name := "id", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"] "dogIlk" ++
      [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
      checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ++
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
      checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
        (perm := false) ++
      [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
        .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
        .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
      checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck" ++
      checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
      [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
        .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
        .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
        -- int256(lot) >= 0 && int256(art) >= 0  ⟺  lot < 2^255 && art < 2^255
        .require
          (.binary .and
            (.binary .lt (.var "lot") (.intLit int256Limit))
            (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
      checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"), asInt256 (.var "art")]
        "_grab" }

def skipTransition : TransitionDecl :=
  { name := "skip"
    params := [{ name := "ilk", ty := bytes32 }, { name := "id", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"] "catIlk" ++
      [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
      checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ++
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
      checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
        (perm := false) ++
      [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
        .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
        .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
        .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
      checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck1" ++
      checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, thisAddr, .var "bid"] "_suck2" ++
      checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hope" ++
      checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ++
      [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
        .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
        .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
        -- int256(lot) >= 0 && int256(art) >= 0  ⟺  lot < 2^255 && art < 2^255
        .require
          (.binary .and
            (.binary .lt (.var "lot") (.intLit int256Limit))
            (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
      checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"), asInt256 (.var "art")]
        "_grab" }

def skimTransition : TransitionDecl :=
  { name := "skim"
    params := [{ name := "ilk", ty := bytes32 }, { name := "urn", ty := addr }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ++
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
      checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
        [.var "ilk", .var "urn"] "vatUrn" ++
      [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
        .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
        .internalCall "rmul" [.var "art", .var "rate"] "owe0",
        .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
        .internalCall "min" [.var "ink", .var "owe"] "wad",
        .internalCall "sub" [.var "owe", .var "wad"] "diff",
        .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
        .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
        .require
          (.binary .and
            (.binary .le (.var "wad") (.intLit int256Limit))
            (.binary .le (.var "art") (.intLit int256Limit))) ] ++
      checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
         .unary .neg (asInt256 (.var "wad")), .unary .neg (asInt256 (.var "art"))]
        "_grab" }

def freeTransition : TransitionDecl :=
  { name := "free"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0) [.var "ilk", sender] "vatUrn" ++
      [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
        .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
        .require (.binary .eq (.var "art") (.intLit 0)),
        .require (.binary .le (.var "ink") (.intLit int256Limit)) ] ++
      checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")), .intLit 0]
        "_grab" }

def thawTransition : TransitionDecl :=
  { name := "thaw"
    params := []
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
        .require (.binary .eq (.storage debtRef) (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
        (perm := false) ++
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")) ] ++
      checkedExternalCallStmts (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ++
      checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ] }

def flowTransition : TransitionDecl :=
  { name := "flow"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
        .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ++
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ] }

def packTransition : TransitionDecl :=
  { name := "pack"
    params := [{ name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
        .internalCall "mul" [.var "wad", .intLit RAY] "amt" ] ++
      checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
        [sender, vowAddr, .var "amt"] "_move" ++
      [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
        .assign .storage (bagRef sender) (.var "bagNew") ] }

def cashTransition : TransitionDecl :=
  { name := "cash"
    params := [{ name := "ilk", ty := bytes32 }, { name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
        .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt" ] ++
      checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
        [.var "ilk", thisAddr, sender, .var "amt"] "_flux" ++
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ] }

def transitions : List TransitionDecl :=
  [ wardsTransition, vatTransition, catTransition, dogTransition, vowTransition, potTransition,
    spotTransition, cureTransition, liveTransition, whenTransition, waitTransition, debtTransition,
    tagTransition, gapTransition, ArtTransition, fixTransition, bagTransition, outTransition,
    relyTransition, denyTransition, fileAddressTransition, fileUintTransition,
    cageTransition, cageIlkTransition, snipTransition, skipTransition, skimTransition,
    freeTransition, thawTransition, flowTransition, packTransition, cashTransition ]

def contract : ContractDecl :=
  { name := "End"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment constructorDecl.params }

end Benchmarks.Dss.End
