import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS DaiJoin benchmark spec

Faithful Solm benchmark scaffold for upstream `dss/src/join.sol` contract `DaiJoin`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI

namespace Benchmarks.Dss.DaiJoin

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
def thisAddr : Expr := .env .this
def ONE : Int := 1000000000000000000000000000
def intMax : Int := 57896044618658097711785492504343953926634992332820282019728792003956564819967
def intLimit : Int := 57896044618658097711785492504343953926634992332820282019728792003956564819968

def u256 (e : Expr) : Expr := .inRange uint256Int e
def mul256 (x y : Expr) : Expr := u256 (.binary .mul x y)
def asInt256 (e : Expr) : Expr := .cast e int256St

/-! ## External ABI -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def vatMoveSelector : ByteArray := selectorBytes 0xbb 0x35 0x78 0x3b
def vatSlipSelector : ByteArray := selectorBytes 0x7c 0xdd 0x3f 0xde
def gemDecimalsSelector : ByteArray := selectorBytes 0x31 0x3c 0xe5 0x67
def gemTransferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb
def gemTransferFromSelector : ByteArray := selectorBytes 0x23 0xb8 0x72 0xdd
def daiMintSelector : ByteArray := selectorBytes 0x40 0xc1 0x0f 0x19
def daiBurnSelector : ByteArray := selectorBytes 0x9d 0xc2 0x9f 0xac

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "move" then
      ABI.encodeCallWithSelector? vatMoveSelector [addr, addr, uint256] args
    else if name = "mint" then
      ABI.encodeCallWithSelector? daiMintSelector [addr, uint256] args
    else if name = "burn" then
      ABI.encodeCallWithSelector? daiBurnSelector [addr, uint256] args
    else
      none
  decode? := fun name out =>
    if name = "move" then
      decodeVoid? out
    else if name = "mint" then
      decodeVoid? out
    else if name = "burn" then
      decodeVoid? out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def vatRef : StorageRef := { base := "vat" }
def daiRef : StorageRef := { base := "dai" }
def liveRef : StorageRef := { base := "live" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "vat", ty := addrSt },
    { name := "dai", ty := addrSt },
    { name := "live", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def intLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int int256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def bytes32Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .bytes bytes32Width }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ => some (wordLoc (wardsSlot usr))
  | { base := "vat", steps := [] }, _ => some (addrLoc ⟨1⟩)
  | { base := "dai", steps := [] }, _ => some (addrLoc ⟨2⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨3⟩)
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

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "vat_", ty := addr }, { name := "dai_", ty := addr }]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage liveRef (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage daiRef (.var "dai_") ] }

def mulFunction : FunctionDecl :=
  { name := "mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body := checkedMulUintInto "z" (.var "x") (.var "y") ++ [ .return [.var "z"] ] }

def functions : List FunctionDecl := [mulFunction]

def wardsTransition : TransitionDecl :=
  { name := "wards", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def daiTransition : TransitionDecl :=
  { name := "dai", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage daiRef] ] }

def liveTransition : TransitionDecl :=
  { name := "live", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage liveRef] ] }

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

def cageTransition : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage liveRef (.intLit 0) ] }

def joinTransition : TransitionDecl :=
  { name := "join"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .internalCall "mul" [.intLit ONE, .var "wad"] "rad" ] ++
      checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
        [thisAddr, .var "usr", .var "rad"] "moveRet" ++
      checkedExternalCallStmts (.storage daiRef) "burn" (.intLit 0)
        [sender, .var "wad"] "burnRet" }

def exitTransition : TransitionDecl :=
  { name := "exit"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .internalCall "mul" [.intLit ONE, .var "wad"] "rad" ] ++
      checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
        [sender, thisAddr, .var "rad"] "moveRet" ++
      checkedExternalCallStmts (.storage daiRef) "mint" (.intLit 0)
        [.var "usr", .var "wad"] "mintRet" }

def transitions : List TransitionDecl :=
  [cageTransition, daiTransition, denyTransition, exitTransition, joinTransition, liveTransition,
    relyTransition, vatTransition, wardsTransition]

def contract : ContractDecl :=
  { name := "DaiJoin"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.DaiJoin
