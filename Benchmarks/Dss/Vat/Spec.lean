import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS Vat benchmark spec

Solm benchmark scaffold for upstream `dss/src/vat.sol`.

The storage layout and public ABI surface follow solc `0.6.12`. Events are omitted. The transition
bodies model the source-level storage effects and Maker's explicit checked arithmetic helpers. The
proof work for this benchmark should isolate the reusable signed/unsigned arithmetic helper lemmas,
storage-mapping layout lemmas, and eager boolean-helper evaluation lemmas.
-/

open Solm ABI

namespace Benchmarks.Dss.Vat

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def int256Int : IntType := .sint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def int256 : ABIType := .elem (.int int256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def uint256St : StorageType := .elem (.int uint256Int)
def int256St : StorageType := .elem (.int int256Int)
def addrSt : StorageType := .elem .address
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller
def ray : Int := 1000000000000000000000000000
def maxInt256 : Int := (2 : Int) ^ 255 - 1

def u256 (e : Expr) : Expr := .inRange uint256Int e
def s256 (e : Expr) : Expr := .inRange int256Int e

def add256 (x y : Expr) : Expr := u256 (.binary .add x y)
def sub256 (x y : Expr) : Expr := u256 (.binary .sub x y)
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)

def lineParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [76, 105, 110, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def spotParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [115, 112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def ilkLineParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [108, 105, 110, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def dustParamLit : Expr :=
  .fixedBytesLit bytes32Width
    [100, 117, 115, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def canRef (src usr : Expr) : StorageRef :=
  { base := "can", steps := [.mindex src, .mindex usr] }

def ilksF (ilk : Expr) (field : Ident) : StorageRef :=
  { base := "ilks", steps := [.mindex ilk, .field field] }

def urnsF (ilk usr : Expr) (field : Ident) : StorageRef :=
  { base := "urns", steps := [.mindex ilk, .mindex usr, .field field] }

def gemRef (ilk usr : Expr) : StorageRef :=
  { base := "gem", steps := [.mindex ilk, .mindex usr] }

def daiRef (usr : Expr) : StorageRef :=
  { base := "dai", steps := [.mindex usr] }

def sinRef (usr : Expr) : StorageRef :=
  { base := "sin", steps := [.mindex usr] }

def debtRef : StorageRef := { base := "debt" }
def viceRef : StorageRef := { base := "vice" }
def LineRef : StorageRef := { base := "Line" }
def liveRef : StorageRef := { base := "live" }

/-! ## Storage declarations and layout -/

def IlkStructTy : StorageType :=
  .struct "Ilk"
    [ ("Art", uint256St), ("rate", uint256St), ("spot", uint256St), ("line", uint256St),
      ("dust", uint256St) ]

def UrnStructTy : StorageType :=
  .struct "Urn" [("ink", uint256St), ("art", uint256St)]

def IlkStructDecl : StructDecl :=
  { name := "Ilk"
    fields :=
      [ { name := "Art", ty := uint256St }, { name := "rate", ty := uint256St },
        { name := "spot", ty := uint256St }, { name := "line", ty := uint256St },
        { name := "dust", ty := uint256St } ] }

def UrnStructDecl : StructDecl :=
  { name := "Urn"
    fields := [ { name := "ink", ty := uint256St }, { name := "art", ty := uint256St } ] }

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "can", ty := .mapping .address (.mapping .address uint256St) },
    { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "urns", ty := .mapping (.bytes bytes32Width) (.mapping .address UrnStructTy) },
    { name := "gem", ty := .mapping (.bytes bytes32Width) (.mapping .address uint256St) },
    { name := "dai", ty := .mapping .address uint256St },
    { name := "sin", ty := .mapping .address uint256St },
    { name := "debt", ty := uint256St },
    { name := "vice", ty := uint256St },
    { name := "Line", ty := uint256St },
    { name := "live", ty := uint256St } ]

def structs : List StructDecl := [IlkStructDecl, UrnStructDecl]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def canOwnerSlot (src : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord src) ⟨1⟩

def canSlot (src usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) (canOwnerSlot src)

def ilksBase (ilk : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord ilk) ⟨2⟩

def urnsIlkSlot (ilk : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord ilk) ⟨3⟩

def urnsBase (ilk usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) (urnsIlkSlot ilk)

def gemIlkSlot (ilk : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord ilk) ⟨4⟩

def gemSlot (ilk usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) (gemIlkSlot ilk)

def daiSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨5⟩

def sinSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨6⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "can", steps := [.mindex src, .mindex usr] }, _ =>
      some (wordLoc (canSlot src usr))
  | { base := "ilks", steps := [.mindex ilk, .field "Art"] }, _ =>
      some (wordLoc (ilksBase ilk))
  | { base := "ilks", steps := [.mindex ilk, .field "rate"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨1⟩))
  | { base := "ilks", steps := [.mindex ilk, .field "spot"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨2⟩))
  | { base := "ilks", steps := [.mindex ilk, .field "line"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨3⟩))
  | { base := "ilks", steps := [.mindex ilk, .field "dust"] }, _ =>
      some (wordLoc (ilksBase ilk + ⟨4⟩))
  | { base := "urns", steps := [.mindex ilk, .mindex usr, .field "ink"] }, _ =>
      some (wordLoc (urnsBase ilk usr))
  | { base := "urns", steps := [.mindex ilk, .mindex usr, .field "art"] }, _ =>
      some (wordLoc (urnsBase ilk usr + ⟨1⟩))
  | { base := "gem", steps := [.mindex ilk, .mindex usr] }, _ =>
      some (wordLoc (gemSlot ilk usr))
  | { base := "dai", steps := [.mindex usr] }, _ => some (wordLoc (daiSlot usr))
  | { base := "sin", steps := [.mindex usr] }, _ => some (wordLoc (sinSlot usr))
  | { base := "debt", steps := [] }, _ => some (wordLoc ⟨7⟩)
  | { base := "vice", steps := [] }, _ => some (wordLoc ⟨8⟩)
  | { base := "Line", steps := [] }, _ => some (wordLoc ⟨9⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨10⟩)
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

def eitherExpr (x y : Expr) : Expr := .binary .or x y
def bothExpr (x y : Expr) : Expr := .binary .and x y

def wishExpr (bit usr : Expr) : Expr :=
  eitherExpr (.binary .eq bit usr) (.binary .eq (.storage (canRef bit usr)) (.intLit 1))

def checkedAddUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (add256 x y),
    .require (.binary .ge (.var name) x) ]

def checkedSubUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (sub256 x y),
    .require (.binary .le (.var name) x) ]

def checkedMulUintInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (mul256 x y),
    .require
      (eitherExpr (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) ]

def checkedAddSignedInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (u256 (.binary .add x y)),
    .require
      (eitherExpr (.binary .ge y (.intLit 0)) (.binary .le (.var name) x)),
    .require
      (eitherExpr (.binary .le y (.intLit 0)) (.binary .ge (.var name) x)) ]

def checkedSubSignedInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some uint256) (u256 (.binary .sub x y)),
    .require
      (eitherExpr (.binary .le y (.intLit 0)) (.binary .le (.var name) x)),
    .require
      (eitherExpr (.binary .ge y (.intLit 0)) (.binary .ge (.var name) x)) ]

def checkedMulSignedInto (name : Ident) (x y : Expr) : List Stmt :=
  [ .letDecl name (some int256) (s256 (.binary .mul x y)),
    .require (.binary .le x (.intLit maxInt256)),
    .require
      (eitherExpr (.binary .eq y (.intLit 0))
        (.binary .eq (.binary .div (.var name) y) x)) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage liveRef (.intLit 1) ] }

/-! ## Public storage getters -/

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def canTransition : TransitionDecl :=
  { name := "can"
    params := [{ name := "arg0", ty := addr }, { name := "arg1", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (canRef (.var "arg0") (.var "arg1"))] ] }

def ilksTransition : TransitionDecl :=
  { name := "ilks"
    params := [{ name := "arg0", ty := bytes32 }]
    returnType := [uint256, uint256, uint256, uint256, uint256]
    body :=
      nonpayable ++
      [ .return
          [ .storage (ilksF (.var "arg0") "Art"), .storage (ilksF (.var "arg0") "rate"),
            .storage (ilksF (.var "arg0") "spot"), .storage (ilksF (.var "arg0") "line"),
            .storage (ilksF (.var "arg0") "dust") ] ] }

def urnsTransition : TransitionDecl :=
  { name := "urns"
    params := [{ name := "arg0", ty := bytes32 }, { name := "arg1", ty := addr }]
    returnType := [uint256, uint256]
    body :=
      nonpayable ++
      [ .return
          [ .storage (urnsF (.var "arg0") (.var "arg1") "ink"),
            .storage (urnsF (.var "arg0") (.var "arg1") "art") ] ] }

def gemTransition : TransitionDecl :=
  { name := "gem"
    params := [{ name := "arg0", ty := bytes32 }, { name := "arg1", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (gemRef (.var "arg0") (.var "arg1"))] ] }

def daiTransition : TransitionDecl :=
  { name := "dai"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (daiRef (.var "arg0"))] ] }

def sinTransition : TransitionDecl :=
  { name := "sin"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (sinRef (.var "arg0"))] ] }

def debtTransition : TransitionDecl :=
  { name := "debt"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage debtRef] ] }

def viceTransition : TransitionDecl :=
  { name := "vice"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage viceRef] ] }

def LineTransition : TransitionDecl :=
  { name := "Line"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage LineRef] ] }

def liveTransition : TransitionDecl :=
  { name := "live"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage liveRef] ] }

/-! ## External transitions -/

def relyTransition : TransitionDecl :=
  { name := "rely"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      [ .assign .storage (wardsRef (.var "usr")) (.intLit 1) ] }

def denyTransition : TransitionDecl :=
  { name := "deny"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      [ .assign .storage (wardsRef (.var "usr")) (.intLit 0) ] }

def hopeTransition : TransitionDecl :=
  { name := "hope"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := nonpayable ++ [ .assign .storage (canRef sender (.var "usr")) (.intLit 1) ] }

def nopeTransition : TransitionDecl :=
  { name := "nope"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := nonpayable ++ [ .assign .storage (canRef sender (.var "usr")) (.intLit 0) ] }

def initTransition : TransitionDecl :=
  { name := "init"
    params := [{ name := "ilk", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      [ .require (.binary .eq (.storage (ilksF (.var "ilk") "rate")) (.intLit 0)),
        .assign .storage (ilksF (.var "ilk") "rate") (.intLit ray) ] }

def fileLineTransition : TransitionDecl :=
  { name := "file"
    params := [{ name := "what", ty := bytes32 }, { name := "data", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      [ .ite
          (.binary .eq (.var "what") lineParamLit)
          [ .assign .storage LineRef (.var "data") ]
          [ .require (.boolLit false) ] ] }

def fileIlkTransition : TransitionDecl :=
  { name := "file"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "what", ty := bytes32 },
        { name := "data", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      [ .ite
          (.binary .eq (.var "what") spotParamLit)
          [ .assign .storage (ilksF (.var "ilk") "spot") (.var "data") ]
          [ .ite
              (.binary .eq (.var "what") ilkLineParamLit)
              [ .assign .storage (ilksF (.var "ilk") "line") (.var "data") ]
              [ .ite
                  (.binary .eq (.var "what") dustParamLit)
                  [ .assign .storage (ilksF (.var "ilk") "dust") (.var "data") ]
                  [ .require (.boolLit false) ] ] ] ] }

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage liveRef (.intLit 0) ] }

def slipTransition : TransitionDecl :=
  { name := "slip"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "usr", ty := addr },
        { name := "wad", ty := int256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++
      checkedAddSignedInto "gemNew" (.storage (gemRef (.var "ilk") (.var "usr"))) (.var "wad") ++
      [ .assign .storage (gemRef (.var "ilk") (.var "usr")) (.var "gemNew") ] }

def fluxTransition : TransitionDecl :=
  { name := "flux"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "src", ty := addr },
        { name := "dst", ty := addr }, { name := "wad", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .require (wishExpr (.var "src") sender) ] ++
      checkedSubUintInto "srcGemNew" (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad") ++
      [ .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew") ] ++
      checkedAddUintInto "dstGemNew" (.storage (gemRef (.var "ilk") (.var "dst"))) (.var "wad") ++
      [ .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ] }

def moveTransition : TransitionDecl :=
  { name := "move"
    params :=
      [ { name := "src", ty := addr }, { name := "dst", ty := addr },
        { name := "rad", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .require (wishExpr (.var "src") sender) ] ++
      checkedSubUintInto "srcDaiNew" (.storage (daiRef (.var "src"))) (.var "rad") ++
      [ .assign .storage (daiRef (.var "src")) (.var "srcDaiNew") ] ++
      checkedAddUintInto "dstDaiNew" (.storage (daiRef (.var "dst"))) (.var "rad") ++
      [ .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ] }

def frobTransition : TransitionDecl :=
  { name := "frob"
    params :=
      [ { name := "i", ty := bytes32 }, { name := "u", ty := addr },
        { name := "v", ty := addr }, { name := "w", ty := addr },
        { name := "dink", ty := int256 }, { name := "dart", ty := int256 } ]
    returnType := []
    body :=
      nonpayable ++ requireLive ++
      [ .letDecl "urnInk" (some uint256) (.storage (urnsF (.var "i") (.var "u") "ink")),
        .letDecl "urnArt" (some uint256) (.storage (urnsF (.var "i") (.var "u") "art")),
        .letDecl "ilkArt" (some uint256) (.storage (ilksF (.var "i") "Art")),
        .letDecl "ilkRate" (some uint256) (.storage (ilksF (.var "i") "rate")),
        .letDecl "ilkSpot" (some uint256) (.storage (ilksF (.var "i") "spot")),
        .letDecl "ilkLine" (some uint256) (.storage (ilksF (.var "i") "line")),
        .letDecl "ilkDust" (some uint256) (.storage (ilksF (.var "i") "dust")),
        .require (.binary .ne (.var "ilkRate") (.intLit 0)) ] ++
      checkedAddSignedInto "urnInkNew" (.var "urnInk") (.var "dink") ++
      checkedAddSignedInto "urnArtNew" (.var "urnArt") (.var "dart") ++
      checkedAddSignedInto "ilkArtNew" (.var "ilkArt") (.var "dart") ++
      checkedMulSignedInto "dtab" (.var "ilkRate") (.var "dart") ++
      checkedMulUintInto "tab" (.var "ilkRate") (.var "urnArtNew") ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "dtab") ++
      [ .assign .storage debtRef (.var "debtNew") ] ++
      checkedMulUintInto "ceilingDebt" (.var "ilkArtNew") (.var "ilkRate") ++
      checkedMulUintInto "inkSpot" (.var "urnInkNew") (.var "ilkSpot") ++
      [ .require
          (eitherExpr
            (.binary .le (.var "dart") (.intLit 0))
            (bothExpr
              (.binary .le (.var "ceilingDebt") (.var "ilkLine"))
              (.binary .le (.var "debtNew") (.storage LineRef)))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (.binary .le (.var "tab") (.var "inkSpot"))),
        .require
          (eitherExpr
            (bothExpr
              (.binary .le (.var "dart") (.intLit 0))
              (.binary .ge (.var "dink") (.intLit 0)))
            (wishExpr (.var "u") sender)),
        .require
          (eitherExpr (.binary .le (.var "dink") (.intLit 0)) (wishExpr (.var "v") sender)),
        .require
          (eitherExpr (.binary .ge (.var "dart") (.intLit 0)) (wishExpr (.var "w") sender)),
        .require
          (eitherExpr (.binary .eq (.var "urnArtNew") (.intLit 0))
            (.binary .ge (.var "tab") (.var "ilkDust"))) ] ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink") ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "w"))) (.var "dtab") ++
      [ .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew"),
        .assign .storage (daiRef (.var "w")) (.var "daiNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew") ] }

def forkTransition : TransitionDecl :=
  { name := "fork"
    params :=
      [ { name := "ilk", ty := bytes32 }, { name := "src", ty := addr },
        { name := "dst", ty := addr }, { name := "dink", ty := int256 },
        { name := "dart", ty := int256 } ]
    returnType := []
    body :=
      nonpayable ++
      checkedSubSignedInto "srcInkNew" (.storage (urnsF (.var "ilk") (.var "src") "ink")) (.var "dink") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "src") "ink") (.var "srcInkNew") ] ++
      checkedSubSignedInto "srcArtNew" (.storage (urnsF (.var "ilk") (.var "src") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "src") "art") (.var "srcArtNew") ] ++
      checkedAddSignedInto "dstInkNew" (.storage (urnsF (.var "ilk") (.var "dst") "ink")) (.var "dink") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "ink") (.var "dstInkNew") ] ++
      checkedAddSignedInto "dstArtNew" (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.var "dart") ++
      [ .assign .storage (urnsF (.var "ilk") (.var "dst") "art") (.var "dstArtNew") ] ++
      checkedMulUintInto "utab"
        (.storage (urnsF (.var "ilk") (.var "src") "art"))
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "vtab"
        (.storage (urnsF (.var "ilk") (.var "dst") "art"))
        (.storage (ilksF (.var "ilk") "rate")) ++
      checkedMulUintInto "srcInkSpot"
        (.storage (urnsF (.var "ilk") (.var "src") "ink"))
        (.storage (ilksF (.var "ilk") "spot")) ++
      checkedMulUintInto "dstInkSpot"
        (.storage (urnsF (.var "ilk") (.var "dst") "ink"))
        (.storage (ilksF (.var "ilk") "spot")) ++
      [ .require (bothExpr (wishExpr (.var "src") sender) (wishExpr (.var "dst") sender)),
        .require (.binary .le (.var "utab") (.var "srcInkSpot")),
        .require (.binary .le (.var "vtab") (.var "dstInkSpot")),
        .require
          (eitherExpr
            (.binary .ge (.var "utab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.storage (urnsF (.var "ilk") (.var "src") "art")) (.intLit 0))),
        .require
          (eitherExpr
            (.binary .ge (.var "vtab") (.storage (ilksF (.var "ilk") "dust")))
            (.binary .eq (.storage (urnsF (.var "ilk") (.var "dst") "art")) (.intLit 0))) ] }

def grabTransition : TransitionDecl :=
  { name := "grab"
    params :=
      [ { name := "i", ty := bytes32 }, { name := "u", ty := addr },
        { name := "v", ty := addr }, { name := "w", ty := addr },
        { name := "dink", ty := int256 }, { name := "dart", ty := int256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++
      checkedAddSignedInto "urnInkNew" (.storage (urnsF (.var "i") (.var "u") "ink")) (.var "dink") ++
      checkedAddSignedInto "urnArtNew" (.storage (urnsF (.var "i") (.var "u") "art")) (.var "dart") ++
      checkedAddSignedInto "ilkArtNew" (.storage (ilksF (.var "i") "Art")) (.var "dart") ++
      checkedMulSignedInto "dtab" (.storage (ilksF (.var "i") "rate")) (.var "dart") ++
      checkedSubSignedInto "gemNew" (.storage (gemRef (.var "i") (.var "v"))) (.var "dink") ++
      checkedSubSignedInto "sinNew" (.storage (sinRef (.var "w"))) (.var "dtab") ++
      checkedSubSignedInto "viceNew" (.storage viceRef) (.var "dtab") ++
      [ .assign .storage (urnsF (.var "i") (.var "u") "ink") (.var "urnInkNew"),
        .assign .storage (urnsF (.var "i") (.var "u") "art") (.var "urnArtNew"),
        .assign .storage (ilksF (.var "i") "Art") (.var "ilkArtNew"),
        .assign .storage (gemRef (.var "i") (.var "v")) (.var "gemNew"),
        .assign .storage (sinRef (.var "w")) (.var "sinNew"),
        .assign .storage viceRef (.var "viceNew") ] }

def healTransition : TransitionDecl :=
  { name := "heal"
    params := [{ name := "rad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      checkedSubUintInto "sinNew" (.storage (sinRef sender)) (.var "rad") ++
      checkedSubUintInto "daiNew" (.storage (daiRef sender)) (.var "rad") ++
      checkedSubUintInto "viceNew" (.storage viceRef) (.var "rad") ++
      checkedSubUintInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage (sinRef sender) (.var "sinNew"),
        .assign .storage (daiRef sender) (.var "daiNew"),
        .assign .storage viceRef (.var "viceNew"),
        .assign .storage debtRef (.var "debtNew") ] }

def suckTransition : TransitionDecl :=
  { name := "suck"
    params :=
      [ { name := "u", ty := addr }, { name := "v", ty := addr },
        { name := "rad", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++
      checkedAddUintInto "sinNew" (.storage (sinRef (.var "u"))) (.var "rad") ++
      checkedAddUintInto "daiNew" (.storage (daiRef (.var "v"))) (.var "rad") ++
      checkedAddUintInto "viceNew" (.storage viceRef) (.var "rad") ++
      checkedAddUintInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage (sinRef (.var "u")) (.var "sinNew"),
        .assign .storage (daiRef (.var "v")) (.var "daiNew"),
        .assign .storage viceRef (.var "viceNew"),
        .assign .storage debtRef (.var "debtNew") ] }

def foldTransition : TransitionDecl :=
  { name := "fold"
    params :=
      [ { name := "i", ty := bytes32 }, { name := "u", ty := addr },
        { name := "rate", ty := int256 } ]
    returnType := []
    body :=
      nonpayable ++ auth ++ requireLive ++
      checkedAddSignedInto "rateNew" (.storage (ilksF (.var "i") "rate")) (.var "rate") ++
      [ .assign .storage (ilksF (.var "i") "rate") (.var "rateNew") ] ++
      checkedMulSignedInto "rad" (.storage (ilksF (.var "i") "Art")) (.var "rate") ++
      checkedAddSignedInto "daiNew" (.storage (daiRef (.var "u"))) (.var "rad") ++
      checkedAddSignedInto "debtNew" (.storage debtRef) (.var "rad") ++
      [ .assign .storage (daiRef (.var "u")) (.var "daiNew"),
        .assign .storage debtRef (.var "debtNew") ] }

def transitions : List TransitionDecl :=
  [ LineTransition,
    cageTransition,
    canTransition,
    daiTransition,
    debtTransition,
    denyTransition,
    fileIlkTransition,
    fileLineTransition,
    fluxTransition,
    foldTransition,
    forkTransition,
    frobTransition,
    gemTransition,
    grabTransition,
    healTransition,
    hopeTransition,
    ilksTransition,
    initTransition,
    liveTransition,
    moveTransition,
    nopeTransition,
    relyTransition,
    sinTransition,
    slipTransition,
    suckTransition,
    urnsTransition,
    viceTransition,
    wardsTransition ]

def contract : ContractDecl :=
  { name := "Vat"
    storage := storageDecls
    ctor := constructorDecl
    structs := structs
    functions := []
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Vat
