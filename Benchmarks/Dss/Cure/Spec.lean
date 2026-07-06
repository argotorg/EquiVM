import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Cure benchmark spec

Faithful Solm benchmark spec for upstream `dss/src/cure.sol`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI

namespace Benchmarks.Dss.Cure

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def addrArray : ABIType := .dynamicArray addr

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def wordModulus : Int := (2 : Int) ^ 256

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def wrap256 (e : Expr) : Expr := .binary .mod e (.intLit wordModulus)
def incUnchecked (e : Expr) : Expr := wrap256 (.binary .add e (.intLit 1))

def zeroPad28 : List UInt8 := List.replicate 28 0
def waitParamLit : Expr :=
  .fixedBytesLit bytes32Width ([119, 97, 105, 116] ++ zeroPad28)

/-! ## External ABI for `SourceLike` -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def sourceCureSelector : ByteArray := selectorBytes 0x84 0x07 0x82 0xed

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "cure" then
      match args with
      | [] => some sourceCureSelector
      | _ => none
    else
      none
  decode? := fun name out =>
    if name = "cure" then
      decodeReturn? uint256 out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def liveRef : StorageRef := { base := "live" }
def srcsRef : StorageRef := { base := "srcs" }
def srcElemRef (idx : Expr) : StorageRef := { base := "srcs", steps := [.aindex idx] }
def waitRef : StorageRef := { base := "wait" }
def whenRef : StorageRef := { base := "when" }

def posRef (src : Expr) : StorageRef :=
  { base := "pos", steps := [.mindex src] }

def amtRef (src : Expr) : StorageRef :=
  { base := "amt", steps := [.mindex src] }

def loadedRef (src : Expr) : StorageRef :=
  { base := "loaded", steps := [.mindex src] }

def lCountRef : StorageRef := { base := "lCount" }
def sayRef : StorageRef := { base := "say" }

def varRef (name : Ident) : StorageRef := { base := name }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "live", ty := uint256St },
    { name := "srcs", ty := .dynamicArray addrSt },
    { name := "wait", ty := uint256St },
    { name := "when", ty := uint256St },
    { name := "pos", ty := .mapping .address uint256St },
    { name := "amt", ty := .mapping .address uint256St },
    { name := "loaded", ty := .mapping .address uint256St },
    { name := "lCount", ty := uint256St },
    { name := "say", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def srcsDataSlot : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (Ethereum.UInt256.toByteArray ⟨2⟩))

def srcElemSlot (idx : KeyValue) : Ethereum.UInt256 :=
  srcsDataSlot + keyValueToWord idx

def posSlot (src : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord src) ⟨5⟩

def amtSlot (src : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord src) ⟨6⟩

def loadedSlot (src : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord src) ⟨7⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨1⟩)
  | { base := "srcs", steps := [.length] }, _ => some (wordLoc ⟨2⟩)
  | { base := "srcs", steps := [.aindex idx] }, _ => some (addrLoc (srcElemSlot idx))
  | { base := "wait", steps := [] }, _ => some (wordLoc ⟨3⟩)
  | { base := "when", steps := [] }, _ => some (wordLoc ⟨4⟩)
  | { base := "pos", steps := [.mindex src] }, _ => some (wordLoc (posSlot src))
  | { base := "amt", steps := [.mindex src] }, _ => some (wordLoc (amtSlot src))
  | { base := "loaded", steps := [.mindex src] }, _ => some (wordLoc (loadedSlot src))
  | { base := "lCount", steps := [] }, _ => some (wordLoc ⟨8⟩)
  | { base := "say", steps := [] }, _ => some (wordLoc ⟨9⟩)
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def auth : List Stmt :=
  [ .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]

def live : List Stmt :=
  [ .require (.binary .eq (.storage liveRef) (.intLit 1)) ]

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

/-! ## Constructor and internal helpers -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      nonpayable ++
      [ .assign .storage liveRef (.intLit 1),
        .assign .storage (wardsRef sender) (.intLit 1) ] }

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

def functions : List FunctionDecl := [addFunction, subFunction]

/-! ## Public storage getters and views -/

def wardsTransition : TransitionDecl :=
  { name := "wards", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

def srcsTransition : TransitionDecl :=
  { name := "srcs", params := [{ name := "arg0", ty := uint256 }], returnType := [addr],
    body := nonpayable ++ [ .return [.storage (srcElemRef (.var "arg0"))] ] }

def waitTransition : TransitionDecl :=
  { name := "wait", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage waitRef] ] }

def whenTransition : TransitionDecl :=
  { name := "when", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage whenRef] ] }

def posTransition : TransitionDecl :=
  { name := "pos", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (posRef (.var "arg0"))] ] }

def amtTransition : TransitionDecl :=
  { name := "amt", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (amtRef (.var "arg0"))] ] }

def loadedTransition : TransitionDecl :=
  { name := "loaded", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (loadedRef (.var "arg0"))] ] }

def lCountTransition : TransitionDecl :=
  { name := "lCount", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage lCountRef] ] }

def sayTransition : TransitionDecl :=
  { name := "say", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage sayRef] ] }

def tCountTransition : TransitionDecl :=
  { name := "tCount", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.arrayLength .storage srcsRef] ] }

def listTransition : TransitionDecl :=
  { name := "list", params := [], returnType := [addrArray],
    body := nonpayable ++ [ .return [.storage srcsRef] ] }

def tellTransition : TransitionDecl :=
  { name := "tell"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .require
          (.binary .and
            (.binary .eq (.storage liveRef) (.intLit 0))
            (.binary .or
              (.binary .eq (.storage lCountRef) (.arrayLength .storage srcsRef))
              (.binary .ge (.env .timestamp) (.storage whenRef)))),
        .return [.storage sayRef] ] }

/-! ## External transitions -/

def relyTransition : TransitionDecl :=
  { name := "rely"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++ live ++
      [ .assign .storage (wardsRef (.var "usr")) (.intLit 1) ] }

def denyTransition : TransitionDecl :=
  { name := "deny"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++ live ++
      [ .assign .storage (wardsRef (.var "usr")) (.intLit 0) ] }

def fileTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++ live ++
      [ .ite
          (.binary .eq (.var "what") waitParamLit)
          [ .assign .storage waitRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def liftTransition : TransitionDecl :=
  { name := "lift"
    params := [{ name := "src", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++ live ++
      [ .require (.binary .eq (.storage (posRef (.var "src"))) (.intLit 0)),
        .push srcsRef (some (.var "src")),
        .assign .storage (posRef (.var "src")) (.arrayLength .storage srcsRef) ] }

def dropTransition : TransitionDecl :=
  { name := "drop"
    params := [{ name := "src", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++ live ++
      [ .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
        .require (.binary .gt (.var "pos_") (.intLit 0)),
        .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
        .ite
          (.binary .lt (.var "pos_") (.var "last"))
          [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
            .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
            .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
            .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
            .assign .storage (posRef (.var "move")) (.var "pos_") ]
          [],
        .pop srcsRef,
        .delete (posRef (.var "src")),
        .delete (amtRef (.var "src")) ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body :=
      nonpayable ++ auth ++ live ++
      [ .assign .storage liveRef (.intLit 0),
        .internalCall "_add" [.env .timestamp, .storage waitRef] "when_",
        .assign .storage whenRef (.var "when_") ] }

def loadTransition : TransitionDecl :=
  { name := "load"
    params := [{ name := "src", ty := addr }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)),
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ] ++
      checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
      [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
        .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
        .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
        .assign .storage sayRef (.var "sayNew"),
        .ite
          (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
          [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
            .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
          [] ] }

def transitions : List TransitionDecl :=
  [amtTransition,
   cageTransition,
   denyTransition,
   dropTransition,
   fileTransition,
   lCountTransition,
   liftTransition,
   listTransition,
   liveTransition,
   loadTransition,
   loadedTransition,
   posTransition,
   relyTransition,
   sayTransition,
   srcsTransition,
   tCountTransition,
   tellTransition,
   waitTransition,
   wardsTransition,
   whenTransition]

def contract : ContractDecl :=
  { name := "Cure"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Cure
