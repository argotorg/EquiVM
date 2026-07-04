import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Vow benchmark spec

Solm benchmark scaffold for upstream `dss/src/vow.sol`.

The storage layout and public ABI surface follow solc `0.6.12`. Events are omitted. The transition
bodies preserve the source order of storage writes and external calls, including repeated `vat.dai`
and `vat.sin` reads.
-/

open Solm ABI

namespace Benchmarks.Dss.Vow

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this

def u256 (e : Expr) : Expr := .inRange uint256Int e
def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)

def waitParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [119, 97, 105, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def bumpParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [98, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def sumpParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [115, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def dumpParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [100, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def humpParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [104, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def flapperParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [102, 108, 97, 112, 112, 101, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def flopperParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [102, 108, 111, 112, 112, 101, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## External ABI for VatLike, FlapLike, and FlopLike -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def vatDaiSelector : ByteArray := selectorBytes 0x6c 0x25 0xb3 0x46
def vatHealSelector : ByteArray := selectorBytes 0xf3 0x7a 0xc6 0x1c
def vatHopeSelector : ByteArray := selectorBytes 0xa3 0xb2 0x2f 0xc4
def vatNopeSelector : ByteArray := selectorBytes 0xdc 0x4d 0x20 0xfa
def vatSinSelector : ByteArray := selectorBytes 0xf0 0x59 0x21 0x2a
def flapCageSelector : ByteArray := selectorBytes 0xa2 0xf9 0x1a 0xf2
def flapKickSelector : ByteArray := selectorBytes 0xca 0x40 0xc4 0x19
def flopCageSelector : ByteArray := selectorBytes 0x69 0x24 0x50 0x09
def flopKickSelector : ByteArray := selectorBytes 0xb7 0xe9 0xcd 0x24

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def vowExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "dai" then
      ABI.encodeCallWithSelector? vatDaiSelector [addr] args
    else if name = "heal" then
      ABI.encodeCallWithSelector? vatHealSelector [uint256] args
    else if name = "hope" then
      ABI.encodeCallWithSelector? vatHopeSelector [addr] args
    else if name = "nope" then
      ABI.encodeCallWithSelector? vatNopeSelector [addr] args
    else if name = "sin" then
      ABI.encodeCallWithSelector? vatSinSelector [addr] args
    else if name = "cage" then
      match args with
      | [] => some flopCageSelector
      | _ => ABI.encodeCallWithSelector? flapCageSelector [uint256] args
    else if name = "kick" then
      match args with
      | [_, _] => ABI.encodeCallWithSelector? flapKickSelector [uint256, uint256] args
      | [_, _, _] => ABI.encodeCallWithSelector? flopKickSelector [addr, uint256, uint256] args
      | _ => none
    else
      none
  decode? := fun name out =>
    if name = "dai" then
      decodeReturn? uint256 out
    else if name = "sin" then
      decodeReturn? uint256 out
    else if name = "kick" then
      decodeReturn? uint256 out
    else if name = "heal" then
      decodeVoid? out
    else if name = "hope" then
      decodeVoid? out
    else if name = "nope" then
      decodeVoid? out
    else if name = "cage" then
      decodeVoid? out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def vatRef : StorageRef := { base := "vat" }
def flapperRef : StorageRef := { base := "flapper" }
def flopperRef : StorageRef := { base := "flopper" }

def sinRef (era : Expr) : StorageRef :=
  { base := "sin", steps := [.mindex era] }

def SinRef : StorageRef := { base := "Sin" }
def AshRef : StorageRef := { base := "Ash" }
def waitRef : StorageRef := { base := "wait" }
def dumpRef : StorageRef := { base := "dump" }
def sumpRef : StorageRef := { base := "sump" }
def bumpRef : StorageRef := { base := "bump" }
def humpRef : StorageRef := { base := "hump" }
def liveRef : StorageRef := { base := "live" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "vat", ty := addrSt },
    { name := "flapper", ty := addrSt },
    { name := "flopper", ty := addrSt },
    { name := "sin", ty := .mapping (.int uint256Int) uint256St },
    { name := "Sin", ty := uint256St },
    { name := "Ash", ty := uint256St },
    { name := "wait", ty := uint256St },
    { name := "dump", ty := uint256St },
    { name := "sump", ty := uint256St },
    { name := "bump", ty := uint256St },
    { name := "hump", ty := uint256St },
    { name := "live", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def sinSlot (era : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord era) ⟨4⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨1⟩)
  | { base := "flapper", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "flopper", steps := [] }, _ => some (addrLoc ⟨3⟩)
  | { base := "sin", steps := [.mindex era] }, _ => some (wordLoc (sinSlot era))
  | { base := "Sin", steps := [] }, _ => some (wordLoc ⟨5⟩)
  | { base := "Ash", steps := [] }, _ => some (wordLoc ⟨6⟩)
  | { base := "wait", steps := [] }, _ => some (wordLoc ⟨7⟩)
  | { base := "dump", steps := [] }, _ => some (wordLoc ⟨8⟩)
  | { base := "sump", steps := [] }, _ => some (wordLoc ⟨9⟩)
  | { base := "bump", steps := [] }, _ => some (wordLoc ⟨10⟩)
  | { base := "hump", steps := [] }, _ => some (wordLoc ⟨11⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨12⟩)
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

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params :=
      [ { name := "vat_", ty := addr }, { name := "flapper_", ty := addr },
        { name := "flopper_", ty := addr } ]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage flapperRef (.var "flapper_"),
        .assign .storage flopperRef (.var "flopper_") ] ++
      checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flapper_"] "_hopeRet" ++
      [ .assign .storage liveRef (.intLit 1) ] }

/-! ## Internal functions -/

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

def minFunction : FunctionDecl :=
  { name := "min"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .letDecl "z" (some uint256)
          (.ite (.binary .le (.var "x") (.var "y")) (.var "x") (.var "y")),
        .return [.var "z"] ] }

def functions : List FunctionDecl :=
  [addFunction, subFunction, minFunction]

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def flapperTransition : TransitionDecl :=
  { name := "flapper", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage flapperRef] ] }

def flopperTransition : TransitionDecl :=
  { name := "flopper", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage flopperRef] ] }

def sinTransition : TransitionDecl :=
  { name := "sin"
    params := [{ name := "arg0", ty := uint256 }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (sinRef (.var "arg0"))] ] }

def SinTransition : TransitionDecl :=
  { name := "Sin", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage SinRef] ] }

def AshTransition : TransitionDecl :=
  { name := "Ash", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage AshRef] ] }

def waitTransition : TransitionDecl :=
  { name := "wait", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage waitRef] ] }

def dumpTransition : TransitionDecl :=
  { name := "dump", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage dumpRef] ] }

def sumpTransition : TransitionDecl :=
  { name := "sump", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage sumpRef] ] }

def bumpTransition : TransitionDecl :=
  { name := "bump", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage bumpRef] ] }

def humpTransition : TransitionDecl :=
  { name := "hump", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage humpRef] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

/-! ## External transitions -/

def relyTransition : TransitionDecl :=
  { name := "rely"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .assign .storage (wardsRef (.var "usr")) (.intLit 1) ] }

def denyTransition : TransitionDecl :=
  { name := "deny"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "usr")) (.intLit 0) ] }

def fileUintTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") waitParamLit)
          [ .assign .storage waitRef (.var "data") ]
          [ .ite
              (.binary .eq (.var "what") bumpParamLit)
              [ .assign .storage bumpRef (.var "data") ]
              [ .ite
                  (.binary .eq (.var "what") sumpParamLit)
                  [ .assign .storage sumpRef (.var "data") ]
                  [ .ite
                      (.binary .eq (.var "what") dumpParamLit)
                      [ .assign .storage dumpRef (.var "data") ]
                      [ .ite
                          (.binary .eq (.var "what") humpParamLit)
                          [ .assign .storage humpRef (.var "data") ]
                          [ .require (.boolLit false) ] ] ] ] ] ] }

def fileAddressTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .ite
          (.binary .eq (.var "what") flapperParamLit)
          (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
              [.storage flapperRef] "_nopeRet" ++
            [ .assign .storage flapperRef (.var "data") ] ++
            checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
              [.var "data"] "_hopeRet")
          [ .ite
              (.binary .eq (.var "what") flopperParamLit)
              [ .assign .storage flopperRef (.var "data") ]
              [ .require (.boolLit false) ] ] ] }

def fessTransition : TransitionDecl :=
  { name := "fess"
    params := [{ name := "tab", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      checkedAddUintInto "sinNew" (.storage (sinRef (.env .timestamp))) (.var "tab") ++
      [ .assign .storage (sinRef (.env .timestamp)) (.var "sinNew") ] ++
      checkedAddUintInto "SinNew" (.storage SinRef) (.var "tab") ++
      [ .assign .storage SinRef (.var "SinNew") ] }

def flogTransition : TransitionDecl :=
  { name := "flog"
    params := [{ name := "era", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .internalCall "add" [.var "era", .storage waitRef] "doneAt",
        .require (.binary .le (.var "doneAt") (.env .timestamp)),
        .internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew",
        .assign .storage SinRef (.var "SinNew"),
        .assign .storage (sinRef (.var "era")) (.intLit 0) ] }

def healTransition : TransitionDecl :=
  { name := "heal"
    params := [{ name := "rad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
        (perm := false) ++
      [ .require (.binary .le (.var "rad") (.var "vatDai")) ] ++
      checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin",
        .internalCall "sub" [.var "freeSin", .storage AshRef] "healDebt",
        .require (.binary .le (.var "rad") (.var "healDebt")) ] ++
      checkedExternalCallStmts (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet" }

def kissTransition : TransitionDecl :=
  { name := "kiss"
    params := [{ name := "rad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .le (.var "rad") (.storage AshRef)) ] ++
      checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
        (perm := false) ++
      [ .require (.binary .le (.var "rad") (.var "vatDai")),
        .internalCall "sub" [.storage AshRef, .var "rad"] "AshNew",
        .assign .storage AshRef (.var "AshNew") ] ++
      checkedExternalCallStmts (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet" }

def flopTransition : TransitionDecl :=
  { name := "flop"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin",
        .internalCall "sub" [.var "freeSin", .storage AshRef] "flopDebt",
        .require (.binary .le (.storage sumpRef) (.var "flopDebt")) ] ++
      checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
        (perm := false) ++
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage AshRef, .storage sumpRef] "AshNew",
        .assign .storage AshRef (.var "AshNew") ] ++
      checkedExternalCallStmts (.storage flopperRef) "kick" (.intLit 0)
        [thisAddr, .storage dumpRef, .storage sumpRef] "id" ++
      [ .return [.var "id"] ] }

def flapTransition : TransitionDecl :=
  { name := "flap"
    params := []
    returnType := [uint256]
    body :=
      nonpayable ++
      checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin0"
        (perm := false) ++
      checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
        (perm := false) ++
      [ .internalCall "add" [.var "vatSin0", .storage bumpRef] "surplus0",
        .internalCall "add" [.var "surplus0", .storage humpRef] "surplusNeed",
        .require (.binary .ge (.var "vatDai") (.var "surplusNeed")) ] ++
      checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin1"
        (perm := false) ++
      [ .internalCall "sub" [.var "vatSin1", .storage SinRef] "freeSin",
        .internalCall "sub" [.var "freeSin", .storage AshRef] "debt",
        .require (.binary .eq (.var "debt") (.intLit 0)) ] ++
      checkedExternalCallStmts (.storage flapperRef) "kick" (.intLit 0)
        [.storage bumpRef, .intLit 0] "id" ++
      [ .return [.var "id"] ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .assign .storage liveRef (.intLit 0),
        .assign .storage SinRef (.intLit 0),
        .assign .storage AshRef (.intLit 0) ] ++
      checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [.storage flapperRef]
        "flapperDai" (perm := false) ++
      checkedExternalCallStmts (.storage flapperRef) "cage" (.intLit 0)
        [.var "flapperDai"] "_flapCageRet" ++
      checkedExternalCallStmts (.storage flopperRef) "cage" (.intLit 0) [] "_flopCageRet" ++
      checkedExternalCallStmts (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
        (perm := false) ++
      checkedExternalCallStmts (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
        (perm := false) ++
      [ .internalCall "min" [.var "vatDai", .var "vatSin"] "healRad" ] ++
      checkedExternalCallStmts (.storage vatRef) "heal" (.intLit 0) [.var "healRad"] "_healRet" }

def transitions : List TransitionDecl :=
  [ AshTransition,
    SinTransition,
    bumpTransition,
    cageTransition,
    denyTransition,
    dumpTransition,
    fessTransition,
    fileUintTransition,
    fileAddressTransition,
    flapTransition,
    flapperTransition,
    flogTransition,
    flopTransition,
    flopperTransition,
    healTransition,
    humpTransition,
    kissTransition,
    liveTransition,
    relyTransition,
    sinTransition,
    sumpTransition,
    vatTransition,
    waitTransition,
    wardsTransition ]

def contract : ContractDecl :=
  { name := "Vow"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := vowExternalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Vow
