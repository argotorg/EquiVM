import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO DSS Dai benchmark spec

Solm benchmark scaffold for upstream MakerDAO/Sky `dss/src/dai.sol`.

Events are omitted.  The ordinary auth and ERC20 paths are modeled source-structurally, including
Maker's explicit checked `add`/`sub` helper pattern.  The `permit` transition is included with the
EIP-712 digest construction and an `ecrecover` precompile-shaped static call; proving that path
faithfully will require reusable precompile/ABI lemmas.
-/

open Solm ABI

namespace Benchmarks.Dss.Dai

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def stringTy : ABIType := .string

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def ecrecoverPrecompile : Expr := .cast (.intLit 1) addrSt
def maxUint256 : Int := (2 : Int) ^ 256 - 1

def u256 (e : Expr) : Expr := .inRange uint256Int e
def addressAsUint256 (e : Expr) : Expr := .cast e uint256St

def add256 (x y : Expr) : Expr :=
  u256 (.binary .add x y)

def sub256 (x y : Expr) : Expr :=
  u256 (.binary .sub x y)

def uncheckedAdd256 (x y : Expr) : Expr :=
  .binary .add x y

def checkedAdd (x y : Expr) : List Stmt :=
  [ .require (.binary .ge (add256 x y) x) ]

def checkedSub (x y : Expr) : List Stmt :=
  [ .require (.binary .le (sub256 x y) x) ]

/-! ## Storage references -/

def wardsRef (usr : Expr) : StorageRef :=
  { base := "wards", steps := [.mindex usr] }

def totalSupplyRef : StorageRef := { base := "totalSupply" }

def balanceOfRef (usr : Expr) : StorageRef :=
  { base := "balanceOf", steps := [.mindex usr] }

def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowance", steps := [.mindex owner, .mindex spender] }

def noncesRef (usr : Expr) : StorageRef :=
  { base := "nonces", steps := [.mindex usr] }

def domainSeparatorRef : StorageRef := { base := "DOMAIN_SEPARATOR" }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "wards", ty := .mapping .address uint256St },
    { name := "totalSupply", ty := uint256St },
    { name := "balanceOf", ty := .mapping .address uint256St },
    { name := "allowance", ty := .mapping .address (.mapping .address uint256St) },
    { name := "nonces", ty := .mapping .address uint256St },
    { name := "DOMAIN_SEPARATOR", ty := bytes32St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wardsSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨0⟩

def balanceOfSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨2⟩

def allowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨3⟩

def allowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord spender) (allowanceOwnerSlot owner)

def noncesSlot (usr : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord usr) ⟨4⟩

def wordLoc (slot : Ethereum.UInt256) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := ty }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex usr] }, _ =>
      some (wordLoc (wardsSlot usr) (.int uint256Int))
  | { base := "totalSupply", steps := [] }, _ =>
      some (wordLoc ⟨1⟩ (.int uint256Int))
  | { base := "balanceOf", steps := [.mindex usr] }, _ =>
      some (wordLoc (balanceOfSlot usr) (.int uint256Int))
  | { base := "allowance", steps := [.mindex owner, .mindex spender] }, _ =>
      some (wordLoc (allowanceSlot owner spender) (.int uint256Int))
  | { base := "nonces", steps := [.mindex usr] }, _ =>
      some (wordLoc (noncesSlot usr) (.int uint256Int))
  | { base := "DOMAIN_SEPARATOR", steps := [] }, _ =>
      some (wordLoc ⟨5⟩ (.bytes bytes32Width))
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source expressions -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def auth : List Stmt :=
  [ .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ]

def permitTypehashBytes : List UInt8 :=
  [ 234, 42, 160, 161, 190, 17, 160, 126, 216, 109, 117, 92, 147, 70, 127, 79,
    130, 54, 43, 69, 35, 113, 209, 186, 148, 209, 113, 81, 35, 81, 26, 203 ]

def permitTypehashExpr : Expr :=
  .fixedBytesLit bytes32Width permitTypehashBytes

def eip191Prefix : Expr :=
  .bytesLit ⟨#[25, 1]⟩

def domainSeparatorExpr : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (bytes32, .keccak256
          (.bytesLit
            (String.toByteArray "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"))),
        (bytes32, .keccak256 (.bytesLit (String.toByteArray "Dai Stablecoin"))),
        (bytes32, .keccak256 (.bytesLit (String.toByteArray "1"))),
        (uint256, .var "chainId_"),
        (uint256, addressAsUint256 (.env .this)) ])

def permitStructHashExpr : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (bytes32, permitTypehashExpr),
        (uint256, addressAsUint256 (.var "holder")),
        (uint256, addressAsUint256 (.var "spender")),
        (uint256, .var "nonce"),
        (uint256, .var "expiry"),
        (uint256, .ite (.var "allowed") (.intLit 1) (.intLit 0)) ])

def permitDigestExpr : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (ABIType.bytes, eip191Prefix),
        (bytes32, .storage domainSeparatorRef),
        (bytes32, permitStructHashExpr) ])

def ecrecoverCalldataExpr : Expr :=
  .abiEncodePacked
    [ (bytes32, .var "digest"),
      (uint256, .var "v"),
      (bytes32, .var "r"),
      (bytes32, .var "s") ]

def allowanceNeedsSpend (owner spender : Expr) : Expr :=
  .ite
    (.binary .ne owner spender)
    (.binary .ne (.storage (allowanceRef owner spender)) (.intLit maxUint256))
    (.boolLit false)

def spendAllowance (owner spender amount : Expr) : List Stmt :=
  [ .require (.binary .ge (.storage (allowanceRef owner spender)) amount) ] ++
  checkedSub (.storage (allowanceRef owner spender)) amount ++
  [ .assign .storage (allowanceRef owner spender)
      (sub256 (.storage (allowanceRef owner spender)) amount) ]

def debitBalance (usr amount : Expr) : List Stmt :=
  [ .require (.binary .ge (.storage (balanceOfRef usr)) amount) ] ++
  checkedSub (.storage (balanceOfRef usr)) amount ++
  [ .assign .storage (balanceOfRef usr) (sub256 (.storage (balanceOfRef usr)) amount) ]

def creditBalance (usr amount : Expr) : List Stmt :=
  checkedAdd (.storage (balanceOfRef usr)) amount ++
  [ .assign .storage (balanceOfRef usr) (add256 (.storage (balanceOfRef usr)) amount) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "chainId_", ty := uint256 }]
    body :=
      nonpayable ++
      [ .assign .storage (wardsRef sender) (.intLit 1),
        .assign .storage domainSeparatorRef domainSeparatorExpr ] }

/-! ## Public ABI surface -/

def nameTransition : TransitionDecl :=
  { name := "name"
    params := []
    returnType := [stringTy]
    body := nonpayable ++ [ .return [.bytesLit (String.toByteArray "Dai Stablecoin")] ] }

def symbolTransition : TransitionDecl :=
  { name := "symbol"
    params := []
    returnType := [stringTy]
    body := nonpayable ++ [ .return [.bytesLit (String.toByteArray "DAI")] ] }

def versionTransition : TransitionDecl :=
  { name := "version"
    params := []
    returnType := [stringTy]
    body := nonpayable ++ [ .return [.bytesLit (String.toByteArray "1")] ] }

def decimalsTransition : TransitionDecl :=
  { name := "decimals"
    params := []
    returnType := [uint8]
    body := nonpayable ++ [ .return [.intLit 18] ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage totalSupplyRef] ] }

def wardsTransition : TransitionDecl :=
  { name := "wards"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (wardsRef (.var "arg0"))] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (balanceOfRef (.var "arg0"))] ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "arg0", ty := addr }, { name := "arg1", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (allowanceRef (.var "arg0") (.var "arg1"))] ] }

def noncesTransition : TransitionDecl :=
  { name := "nonces"
    params := [{ name := "arg0", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (noncesRef (.var "arg0"))] ] }

def domainSeparatorTransition : TransitionDecl :=
  { name := "DOMAIN_SEPARATOR"
    params := []
    returnType := [bytes32]
    body := nonpayable ++ [ .return [.storage domainSeparatorRef] ] }

def permitTypehashTransition : TransitionDecl :=
  { name := "PERMIT_TYPEHASH"
    params := []
    returnType := [bytes32]
    body := nonpayable ++ [ .return [permitTypehashExpr] ] }

def relyTransition : TransitionDecl :=
  { name := "rely"
    params := [{ name := "guy", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "guy")) (.intLit 1) ] }

def denyTransition : TransitionDecl :=
  { name := "deny"
    params := [{ name := "guy", ty := addr }]
    returnType := []
    body := nonpayable ++ auth ++ [ .assign .storage (wardsRef (.var "guy")) (.intLit 0) ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "dst", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ .internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok",
        .return [.var "_ok"] ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params :=
      [ { name := "src", ty := addr }, { name := "dst", ty := addr },
        { name := "wad", ty := uint256 } ]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ .require (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")),
        .ite
          (allowanceNeedsSpend (.var "src") sender)
          (spendAllowance (.var "src") sender (.var "wad"))
          [] ] ++
      debitBalance (.var "src") (.var "wad") ++
      creditBalance (.var "dst") (.var "wad") ++
      [ .return [.boolLit true] ] }

def mintTransition : TransitionDecl :=
  { name := "mint"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++ auth ++
      creditBalance (.var "usr") (.var "wad") ++
      checkedAdd (.storage totalSupplyRef) (.var "wad") ++
      [ .assign .storage totalSupplyRef (add256 (.storage totalSupplyRef) (.var "wad")) ] }

def burnTransition : TransitionDecl :=
  { name := "burn"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .ge (.storage (balanceOfRef (.var "usr"))) (.var "wad")),
        .ite
          (allowanceNeedsSpend (.var "usr") sender)
          (spendAllowance (.var "usr") sender (.var "wad"))
          [] ] ++
      debitBalance (.var "usr") (.var "wad") ++
      checkedSub (.storage totalSupplyRef) (.var "wad") ++
      [ .assign .storage totalSupplyRef (sub256 (.storage totalSupplyRef) (.var "wad")) ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ .assign .storage (allowanceRef sender (.var "usr")) (.var "wad"),
        .return [.boolLit true] ] }

def pushTransition : TransitionDecl :=
  { name := "push"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := []
    body := nonpayable ++ [ .internalCall "transferFrom" [sender, .var "usr", .var "wad"] "_ok" ] }

def pullTransition : TransitionDecl :=
  { name := "pull"
    params := [{ name := "usr", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := []
    body := nonpayable ++ [ .internalCall "transferFrom" [.var "usr", sender, .var "wad"] "_ok" ] }

def moveTransition : TransitionDecl :=
  { name := "move"
    params :=
      [ { name := "src", ty := addr }, { name := "dst", ty := addr },
        { name := "wad", ty := uint256 } ]
    returnType := []
    body := nonpayable ++ [ .internalCall "transferFrom" [.var "src", .var "dst", .var "wad"] "_ok" ] }

def permitTransition : TransitionDecl :=
  { name := "permit"
    params :=
      [ { name := "holder", ty := addr }, { name := "spender", ty := addr },
        { name := "nonce", ty := uint256 }, { name := "expiry", ty := uint256 },
        { name := "allowed", ty := boolTy }, { name := "v", ty := uint8 },
        { name := "r", ty := bytes32 }, { name := "s", ty := bytes32 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .letDecl "digest" (some bytes32) permitDigestExpr,
        .require (.binary .ne (.var "holder") zeroAddr),
        .lowLevelCall ecrecoverPrecompile (.intLit 0) ecrecoverCalldataExpr
          "ecrecoverSuccess" "ecrecoverData" false,
        .require (.var "ecrecoverSuccess"),
        .letDecl "recovered" (some addr) (.abiDecode addr (.var "ecrecoverData")),
        .require (.binary .eq (.var "holder") (.var "recovered")),
        .require
          (.binary .or
            (.binary .eq (.var "expiry") (.intLit 0))
            (.binary .le (.env .timestamp) (.var "expiry"))),
        .require (.binary .eq (.var "nonce") (.storage (noncesRef (.var "holder")))),
        .assign .storage (noncesRef (.var "holder"))
          (uncheckedAdd256 (.storage (noncesRef (.var "holder"))) (.intLit 1)),
        .letDecl "wad" (some uint256)
          (.ite (.var "allowed") (.intLit maxUint256) (.intLit 0)),
        .assign .storage (allowanceRef (.var "holder") (.var "spender")) (.var "wad") ] }

def transitions : List TransitionDecl :=
  [ allowanceTransition,
    approveTransition,
    balanceOfTransition,
    burnTransition,
    decimalsTransition,
    denyTransition,
    domainSeparatorTransition,
    mintTransition,
    moveTransition,
    nameTransition,
    noncesTransition,
    permitTransition,
    permitTypehashTransition,
    pullTransition,
    pushTransition,
    relyTransition,
    symbolTransition,
    totalSupplyTransition,
    transferTransition,
    transferFromTransition,
    versionTransition,
    wardsTransition ]

def contract : ContractDecl :=
  { name := "Dai"
    storage := storageDecls
    ctor := constructorDecl
    functions := []
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.Dai
