import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS GemJoin benchmark spec

Faithful Solm benchmark scaffold for upstream `dss/src/join.sol` contract `GemJoin`.
Events are omitted, matching the existing event-bearing DSS benchmarks.
-/

open Solm ABI

namespace Benchmarks.Dss.GemJoin

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

def decodeBoolReturn? (out : EVM.Bytes) : Option (List Value) :=
  match ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [boolTy] out with
  | some [value] => some [value]
  | _ => none

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "decimals" then
      match args with
      | [] => some gemDecimalsSelector
      | _ => none
    else if name = "transfer" then
      ABI.encodeCallWithSelector? gemTransferSelector [addr, uint256] args
    else if name = "transferFrom" then
      ABI.encodeCallWithSelector? gemTransferFromSelector [addr, addr, uint256] args
    else if name = "slip" then
      ABI.encodeCallWithSelector? vatSlipSelector [bytes32, addr, int256] args
    else
      none
  decode? := fun name out =>
    if name = "decimals" then
      decodeReturn? uint256 out
    else if name = "transfer" then
      decodeBoolReturn? out
    else if name = "transferFrom" then
      decodeBoolReturn? out
    else if name = "slip" then
      decodeVoid? out
    else
      none

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def vatRef : StorageRef := { base := "vat" }
def ilkRef : StorageRef := { base := "ilk" }
def gemRef : StorageRef := { base := "gem" }
def decRef : StorageRef := { base := "dec" }
def liveRef : StorageRef := { base := "live" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "vat", ty := addrSt },
    { name := "ilk", ty := bytes32St },
    { name := "gem", ty := addrSt },
    { name := "dec", ty := uint256St },
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
  | { base := "ilk", steps := [] }, _ => some (bytes32Loc ⟨2⟩)
  | { base := "gem", steps := [] }, _ => some (addrLoc ⟨3⟩)
  | { base := "dec", steps := [] }, _ => some (wordLoc ⟨4⟩)
  | { base := "live", steps := [] }, _ => some (wordLoc ⟨5⟩)
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
  { params := [{ name := "vat_", ty := addr }, { name := "ilk_", ty := bytes32 }, { name := "gem_", ty := addr }]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage liveRef (.intLit 1),
        .assign .storage vatRef (.var "vat_"),
        .assign .storage ilkRef (.var "ilk_"),
        .assign .storage gemRef (.var "gem_") ] ++
      -- GemLike.decimals() is `view` → STATICCALL (perm := false)
      checkedExternalCallStmts (.var "gem_") "decimals" (.intLit 0) [] "decimalsRet"
        (perm := false) ++
      [ .assign .storage decRef (.var "decimalsRet") ] }

def functions : List FunctionDecl := []

def wardsTransition : TransitionDecl :=
  { name := "wards", params := [{ name := "arg0", ty := addr }], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def vatTransition : TransitionDecl :=
  { name := "vat", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage vatRef] ] }

def ilkTransition : TransitionDecl :=
  { name := "ilk", params := [], returnType := [bytes32],
    body := nonpayable ++ [ .return [.storage ilkRef] ] }

def gemTransition : TransitionDecl :=
  { name := "gem", params := [], returnType := [addr],
    body := nonpayable ++ [ .return [.storage gemRef] ] }

def decTransition : TransitionDecl :=
  { name := "dec", params := [], returnType := [uint256],
    body := nonpayable ++ [ .return [.storage decRef] ] }

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
      [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
        -- `int(wad) >= 0` ⟺ `wad < 2^255` (asInt256 is identity, so `asInt256 wad >= 0` would be a no-op)
        .require (.binary .lt (.var "wad") (.intLit intLimit)) ] ++
      checkedExternalCallStmts (.storage vatRef) "slip" (.intLit 0)
        [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet" ++
      checkedExternalCallStmts (.storage gemRef) "transferFrom" (.intLit 0)
        [sender, thisAddr, .var "wad"] "transferFromOk" ++
      [ .require (.var "transferFromOk") ] }

def exitTransition : TransitionDecl :=
  { name := "exit"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .le (.var "wad") (.intLit intLimit)) ] ++
      checkedExternalCallStmts (.storage vatRef) "slip" (.intLit 0)
        [.storage ilkRef, sender, .unary .neg (asInt256 (.var "wad"))] "slipRet" ++
      checkedExternalCallStmts (.storage gemRef) "transfer" (.intLit 0)
        [.var "usr", .var "wad"] "transferOk" ++
      [ .require (.var "transferOk") ] }

def transitions : List TransitionDecl :=
  [cageTransition, decTransition, denyTransition, exitTransition, gemTransition, ilkTransition,
    joinTransition, liveTransition, relyTransition, vatTransition, wardsTransition]

def contract : ContractDecl :=
  { name := "GemJoin"
    storage := storageDecls
    ctor := constructorDecl
    functions := functions
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.GemJoin
