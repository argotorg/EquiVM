import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Flopper benchmark spec

Faithful Solm benchmark spec for upstream `dss/src/flop.sol`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI

namespace Benchmarks.Dss.Flopper

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint48Int : IntType := .uint ⟨48, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def uint48 : ABIType := .elem (.int uint48Int)
def addr : ABIType := .elem .address
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def uint48St : StorageType := .elem (.int uint48Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def ONE : Int := 1000000000000000000
def defaultBeg : Int := 1050000000000000000
def defaultPad : Int := 1500000000000000000
def defaultTtl : Int := 10800
def defaultTau : Int := 172800
def maxUint256 : Int := (2 : Int) ^ 256 - 1
def uint48Modulus : Int := (2 : Int) ^ 48

def u256 (e : Expr) : Expr := .inRange uint256Int e
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)
def wrap48 (e : Expr) : Expr := .binary .mod e (.intLit uint48Modulus)

def zeroPad29 : List UInt8 := List.replicate 29 0

def begParamLit : Expr :=
  .fixedBytesLit bytes32Width ([98, 101, 103] ++ zeroPad29)

def padParamLit : Expr :=
  .fixedBytesLit bytes32Width ([112, 97, 100] ++ zeroPad29)

def ttlParamLit : Expr :=
  .fixedBytesLit bytes32Width ([116, 116, 108] ++ zeroPad29)

def tauParamLit : Expr :=
  .fixedBytesLit bytes32Width ([116, 97, 117] ++ zeroPad29)

/-! ## External ABI for VatLike, GemLike, and VowLike -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def moveSelector : ByteArray := selectorBytes 0xbb 0x35 0x78 0x3b
def suckSelector : ByteArray := selectorBytes 0xf2 0x4e 0x23 0xeb
def mintSelector : ByteArray := selectorBytes 0x40 0xc1 0x0f 0x19
def AshSelector : ByteArray := selectorBytes 0x2a 0x1d 0x2b 0x3c
def kissSelector : ByteArray := selectorBytes 0x25 0x06 0x85 0x5a

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "move" then
      ABI.encodeCallWithSelector? moveSelector [addr, addr, uint256] args
    else if name = "suck" then
      ABI.encodeCallWithSelector? suckSelector [addr, addr, uint256] args
    else if name = "mint" then
      ABI.encodeCallWithSelector? mintSelector [addr, uint256] args
    else if name = "Ash" then
      match args with
      | [] => some AshSelector
      | _ => none
    else if name = "kiss" then
      ABI.encodeCallWithSelector? kissSelector [uint256] args
    else
      none
  decode? := fun name out =>
    if name = "move" then
      decodeVoid? out
    else if name = "suck" then
      decodeVoid? out
    else if name = "mint" then
      decodeVoid? out
    else if name = "Ash" then
      decodeReturn? uint256 out
    else if name = "kiss" then
      decodeVoid? out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def bidRef (id : Expr) : StorageRef :=
  { base := "bids", steps := [.mindex id] }

def bidsF (id : Expr) (field : Ident) : StorageRef :=
  { base := "bids", steps := [.mindex id, .field field] }

def vatRef : StorageRef := { base := "vat" }
def gemRef : StorageRef := { base := "gem" }
def begRef : StorageRef := { base := "beg" }
def padRef : StorageRef := { base := "pad" }
def ttlRef : StorageRef := { base := "ttl" }
def tauRef : StorageRef := { base := "tau" }
def kicksRef : StorageRef := { base := "kicks" }
def liveRef : StorageRef := { base := "live" }
def vowRef : StorageRef := { base := "vow" }
def varRef (name : Ident) : StorageRef := { base := name }

/-! ## Storage declarations and layout -/

def BidStructTy : StorageType :=
  .struct "Bid"
    [ ("bid", uint256St), ("lot", uint256St), ("guy", addrSt),
      ("tic", uint48St), ("end", uint48St) ]

def BidStructDecl : StructDecl :=
  { name := "Bid"
    fields :=
      [ { name := "bid", ty := uint256St },
        { name := "lot", ty := uint256St },
        { name := "guy", ty := addrSt },
        { name := "tic", ty := uint48St },
        { name := "end", ty := uint48St } ] }

def structs : List StructDecl := [BidStructDecl]

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "bids", ty := .mapping (.int uint256Int) BidStructTy },
    { name := "vat", ty := addrSt },
    { name := "gem", ty := addrSt },
    { name := "beg", ty := uint256St },
    { name := "pad", ty := uint256St },
    { name := "ttl", ty := uint48St },
    { name := "tau", ty := uint48St },
    { name := "kicks", ty := uint256St },
    { name := "live", ty := uint256St },
    { name := "vow", ty := addrSt } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def bidsBase (id : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord id) ⟨1⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def uint48Loc (slot : Ethereum.UInt256) (offset : Fin 32)
    (hbound : offset.val + 6 - 1 < 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 6, hbound := hbound, type := .int uint48Int }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "bids", steps := [.mindex id, .field "bid"] }, _ =>
      some (wordLoc (bidsBase id))
  | { base := "bids", steps := [.mindex id, .field "lot"] }, _ =>
      some (wordLoc (bidsBase id + ⟨1⟩))
  | { base := "bids", steps := [.mindex id, .field "guy"] }, _ =>
      some (addrLoc (bidsBase id + ⟨2⟩))
  | { base := "bids", steps := [.mindex id, .field "tic"] }, _ =>
      some (uint48Loc (bidsBase id + ⟨2⟩) ⟨20, by decide⟩ (by decide))
  | { base := "bids", steps := [.mindex id, .field "end"] }, _ =>
      some (uint48Loc (bidsBase id + ⟨2⟩) ⟨26, by decide⟩ (by decide))
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "gem", steps := [] }, _ => some (addrLoc ⟨3⟩)
  | { base := "beg", steps := [] }, _ => some (wordLoc ⟨4⟩)
  | { base := "pad", steps := [] }, _ => some (wordLoc ⟨5⟩)
  | { base := "ttl", steps := [] }, _ => some (uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide))
  | { base := "tau", steps := [] }, _ => some (uint48Loc ⟨6⟩ ⟨6, by decide⟩ (by decide))
  | { base := "kicks", steps := [] }, _ => some (wordLoc ⟨7⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨8⟩)
  | { base := "vow", steps := [] }, _ => some (addrLoc ⟨9⟩)
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

def checkedMulUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (mul256 x y),
    .require
      (.binary .or
        (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) ]

def checkedAdd48Into (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint48) (wrap48 (.binary .add x y)),
    .require (.binary .ge (.var name) x) ]

/-! ## Constructor and internal functions -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "vat_", ty := addr }, { name := "gem_", ty := addr }]
    body :=
      nonpayable ++
      [ .assign .storage begRef (.intLit defaultBeg),
        .assign .storage padRef (.intLit defaultPad),
        .assign .storage ttlRef (.intLit defaultTtl),
        .assign .storage tauRef (.intLit defaultTau),
        .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage gemRef (.var "gem_"),
        .assign .storage liveRef (.intLit 1) ] }

def add48Function : FunctionDecl :=
  { name := "add"
    params := [{ name := "x", ty := uint48 }, { name := "y", ty := uint48 }]
    returnType := [uint48]
    body := checkedAdd48Into "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def mulFunction : FunctionDecl :=
  { name := "mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedMulUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def minFunction : FunctionDecl :=
  { name := "min"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .ite
          (.binary .gt (.var "x") (.var "y"))
          [ .return [.var "y"] ]
          [ .return [.var "x"] ] ] }

def functions : List FunctionDecl := [add48Function, mulFunction, minFunction]

def now48 : Expr := wrap48 (.env .timestamp)

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def bidsTransition : TransitionDecl :=
  { name := "bids"
    params := [{ name := "arg0", ty := uint256 }]
    returnType := [uint256, uint256, addr, uint48, uint48]
    body :=
      nonpayable ++
      [ .return
          [ .storage (bidsF (.var "arg0") "bid"),
            .storage (bidsF (.var "arg0") "lot"),
            .storage (bidsF (.var "arg0") "guy"),
            .storage (bidsF (.var "arg0") "tic"),
            .storage (bidsF (.var "arg0") "end") ] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def gemTransition : TransitionDecl :=
  { name := "gem", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage gemRef] ] }

def begTransition : TransitionDecl :=
  { name := "beg", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage begRef] ] }

def padTransition : TransitionDecl :=
  { name := "pad", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage padRef] ] }

def ttlTransition : TransitionDecl :=
  { name := "ttl", params := [], returnType := [uint48],
    body := nonpayable ++ [ .return [.storage ttlRef] ] }

def tauTransition : TransitionDecl :=
  { name := "tau", params := [], returnType := [uint48],
    body := nonpayable ++ [ .return [.storage tauRef] ] }

def kicksTransition : TransitionDecl :=
  { name := "kicks", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage kicksRef] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

def vowTransition : TransitionDecl :=
  { name := "vow", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vowRef] ] }

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
          (.binary .eq (.var "what") begParamLit)
          [ .assign .storage begRef (.var "data") ]
          [ .ite
              (.binary .eq (.var "what") padParamLit)
              [ .assign .storage padRef (.var "data") ]
              [ .ite
                  (.binary .eq (.var "what") ttlParamLit)
                  [ .assign .storage ttlRef (wrap48 (.var "data")) ]
                  [ .ite
                      (.binary .eq (.var "what") tauParamLit)
                      [ .assign .storage tauRef (wrap48 (.var "data")) ]
                      [ .require (.boolLit false) ] ] ] ] ] }

def kickTransition : TransitionDecl :=
  { name := "kick"
    params :=
      [ { name := "gal", ty := addr }, { name := "lot", ty := uint256 },
        { name := "bid", ty := uint256 } ]
    returnType := [uint256]
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)),
        .letDecl "id" (some uint256) (.binary .add (.storage kicksRef) (.intLit 1)),
        .assign .storage kicksRef (.var "id"),
        .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
        .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
        .assign .storage (bidsF (.var "id") "guy") (.var "gal") ] ++
      checkedAdd48Into "end_" now48 (.storage tauRef) ++
      [ .assign .storage (bidsF (.var "id") "end") (.var "end_"),
        .return [.var "id"] ] }

def tickTransition : TransitionDecl :=
  { name := "tick"
    params := [{ name := "id", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
        .require (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) ] ++
      checkedMulUintInto "lotBase" (.storage padRef) (.storage (bidsF (.var "id") "lot")) ++
      [ .assign .storage (bidsF (.var "id") "lot") (.binary .div (.var "lotBase") (.intLit ONE)) ] ++
      checkedAdd48Into "end_" now48 (.storage tauRef) ++
      [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] }

def dentTransition : TransitionDecl :=
  { name := "dent"
    params :=
      [ { name := "id", ty := uint256 }, { name := "lot", ty := uint256 },
        { name := "bid", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr),
        .require
          (.binary .or
            (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
            (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))),
        .require (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
        .require (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))),
        .require (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) ] ++
      checkedMulUintInto "begLot" (.storage begRef) (.var "lot") ++
      checkedMulUintInto "lotOne" (.storage (bidsF (.var "id") "lot")) (.intLit ONE) ++
      [ .require (.binary .le (.var "begLot") (.var "lotOne")),
        .ite
          (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_moveRet" ++
            [ .ite
                (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "Ash" (.intLit 0)
                    [] "Ash" ++
                  [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
                  checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss" (.intLit 0)
                    [.var "kissAmt"] "_kissRet")
                [],
              .assign .storage (bidsF (.var "id") "guy") sender ])
          [],
        .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
      checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
      [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ] }

def dealTransition : TransitionDecl :=
  { name := "deal"
    params := [{ name := "id", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .require
          (.binary .and
            (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
            (.binary .or
              (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
              (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) ] ++
      checkedExternalCallStmts (.storage gemRef) "mint" (.intLit 0)
        [.storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "lot")] "_mintRet" ++
      [ .delete (bidRef (.var "id")) ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .assign .storage liveRef (.intLit 0),
        .assign .storage vowRef sender ] }

def yankTransition : TransitionDecl :=
  { name := "yank"
    params := [{ name := "id", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
        .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) ] ++
      checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [.storage vowRef, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] "_suckRet" ++
      [ .delete (bidRef (.var "id")) ] }

def transitions : List TransitionDecl :=
  [begTransition,
   bidsTransition,
   cageTransition,
   dealTransition,
   dentTransition,
   denyTransition,
   fileTransition,
   gemTransition,
   kickTransition,
   kicksTransition,
   liveTransition,
   padTransition,
   relyTransition,
   tauTransition,
   tickTransition,
   ttlTransition,
   vatTransition,
   vowTransition,
   wardsTransition,
   yankTransition]

def contract : ContractDecl :=
  { name := "Flopper"
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

end Benchmarks.Dss.Flopper
