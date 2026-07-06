import Solm.Semantics
import Solm.SolidityLayout

/-!
# Safe benchmark spec

Source-shaped Solm spec for upstream `safe-global/safe-smart-account`
`Benchmarks/Safe/contracts/Safe.sol`, compiled with solc 0.7.6.

Events and revert strings are intentionally omitted, since the benchmark equivalence relation
observes successful return values, storage/world effects, and revert-vs-success behavior, but not
logs or revert payloads.  The fallback and receive entrypoints are modeled explicitly.
-/

open Solm ABI

namespace Benchmarks.Safe

/-! ## Types and small expression helpers -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def bytes1Width : Fin 32 := ⟨0, by decide⟩
def bytes2Width : Fin 32 := ⟨1, by decide⟩
def bytes4Width : Fin 32 := ⟨3, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def bytes1 : ABIType := .elem (.bytes bytes1Width)
def bytes2 : ABIType := .elem (.bytes bytes2Width)
def bytes4 : ABIType := .elem (.bytes bytes4Width)
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def stringTy : ABIType := .string

def uint8St : StorageType := .elem (.int uint8Int)
def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def addrArrayTy : ABIType := .dynamicArray addr

def maxUint256 : Int := 2 ^ 256 - 1
def uint256Modulus : Int := 2 ^ 256

def sender : Expr := .env .caller
def origin : Expr := .env .origin
def this : Expr := .env .this
def callvalue : Expr := .env .callvalue
def gasprice : Expr := .env .gasprice

def zeroAddr : Expr := .cast (.intLit 0) addrSt
def sentinelAddr : Expr := .cast (.intLit 1) addrSt
def ecrecoverPrecompile : Expr := .cast (.intLit 1) addrSt
def p256Precompile : Expr := .cast (.intLit 256) addrSt

def eqE (x y : Expr) : Expr := .binary .eq x y
def neE (x y : Expr) : Expr := .binary .ne x y
def ltE (x y : Expr) : Expr := .binary .lt x y
def leE (x y : Expr) : Expr := .binary .le x y
def gtE (x y : Expr) : Expr := .binary .gt x y
def geE (x y : Expr) : Expr := .binary .ge x y
def andE (x y : Expr) : Expr := .binary .and x y
def orE (x y : Expr) : Expr := .binary .or x y
def notE (x : Expr) : Expr := .unary .not x
def addE (x y : Expr) : Expr := .binary .add x y
def subE (x y : Expr) : Expr := .binary .sub x y
def mulE (x y : Expr) : Expr := .binary .mul x y
def divE (x y : Expr) : Expr := .binary .div x y
def shlE (x y : Expr) : Expr := .binary .shl x y
def minE (x y : Expr) : Expr := .ite (ltE x y) x y
def maxE (x y : Expr) : Expr := .ite (gtE x y) x y
def wrap256 (x : Expr) : Expr := .binary .mod x (.intLit uint256Modulus)
def u8 (x : Expr) : Expr := .inRange uint8Int x
def u256 (x : Expr) : Expr := .inRange uint256Int x
def add256 (x y : Expr) : Expr := u256 (addE x y)
def sub256 (x y : Expr) : Expr := u256 (subE x y)
def mul256 (x y : Expr) : Expr := u256 (mulE x y)

def varRef (name : Ident) : StorageRef := { base := name }
def localIndex (name : Ident) (idx : Expr) : StorageRef :=
  { base := name, steps := [.aindex idx] }
def localLength (name : Ident) : Expr :=
  .arrayLength .localVar (varRef name)
def arrGet (name : Ident) (idx : Expr) : Expr :=
  .index (.var name) idx
def arrSet (name : Ident) (idx value : Expr) : Stmt :=
  .assign .localVar (localIndex name idx) value
def tuple0 (e : Expr) : Expr := .tupleGet e 0
def tuple1 (e : Expr) : Expr := .tupleGet e 1

def addressAsUint256 (e : Expr) : Expr := .cast e uint256St
def uint256AsAddress (e : Expr) : Expr := .cast e addrSt
def bytes32AsUint256 (e : Expr) : Expr := .cast e uint256St
def bytes1AsUint8 (e : Expr) : Expr := .cast e uint8St

def emptyBytes : Expr := .bytesLit ByteArray.empty
def zeroBytes32 : Expr := .fixedBytesLit bytes32Width (List.replicate 32 (0 : UInt8))

def fixedBytes4Lit (a b c d : UInt8) : Expr :=
  .fixedBytesLit bytes4Width [a, b, c, d]

/-! ## Constants -/

def domainSeparatorTypehash : Expr :=
  .fixedBytesLit bytes32Width
    [ 0x47, 0xe7, 0x95, 0x34, 0xa2, 0x45, 0x95, 0x2e,
      0x8b, 0x16, 0x89, 0x3a, 0x33, 0x6b, 0x85, 0xa3,
      0xd9, 0xea, 0x9f, 0xa8, 0xc5, 0x73, 0xf3, 0xd8,
      0x03, 0xaf, 0xb9, 0x2a, 0x79, 0x46, 0x92, 0x18 ]

def safeTxTypehash : Expr :=
  .fixedBytesLit bytes32Width
    [ 0xbb, 0x83, 0x10, 0xd4, 0x86, 0x36, 0x8d, 0xb6,
      0xbd, 0x6f, 0x84, 0x94, 0x02, 0xfd, 0xd7, 0x3a,
      0xd5, 0x3d, 0x31, 0x6b, 0x5a, 0x4b, 0x26, 0x44,
      0xad, 0x6e, 0xfe, 0x0f, 0x94, 0x12, 0x86, 0xd8 ]

def eip712Prefix : Expr :=
  .fixedBytesLit bytes2Width [0x19, 0x01]

def ethSignPrefix : Expr :=
  .bytesLit
    ⟨#[ 25, 69, 116, 104, 101, 114, 101, 117, 109, 32, 83, 105, 103, 110,
        101, 100, 32, 77, 101, 115, 115, 97, 103, 101, 58, 10, 51, 50 ]⟩

def eip1271MagicBytes32 : Expr :=
  .fixedBytesLit bytes32Width
    ([0x16, 0x26, 0xba, 0x7e] ++ List.replicate 28 (0 : UInt8))

def transactionGuardInterfaceId : Expr :=
  fixedBytes4Lit 0xe6 0xd7 0xa8 0x3a

def moduleGuardInterfaceId : Expr :=
  fixedBytes4Lit 0x58 0x40 0x1e 0xd8

/-! ## Storage references -/

def singletonRef : StorageRef := { base := "singleton" }
def modulesRef (module : Expr) : StorageRef := { base := "modules", steps := [.mindex module] }
def ownersRef (owner : Expr) : StorageRef := { base := "owners", steps := [.mindex owner] }
def ownerCountRef : StorageRef := { base := "ownerCount" }
def thresholdRef : StorageRef := { base := "threshold" }
def nonceRef : StorageRef := { base := "nonce" }
def deprecatedDomainSeparatorRef : StorageRef := { base := "_deprecatedDomainSeparator" }
def signedMessagesRef (messageHash : Expr) : StorageRef :=
  { base := "signedMessages", steps := [.mindex messageHash] }
def approvedHashesRef (owner messageHash : Expr) : StorageRef :=
  { base := "approvedHashes", steps := [.mindex owner, .mindex messageHash] }

def fallbackHandlerRef : StorageRef := { base := "_fallbackHandler" }
def guardRef : StorageRef := { base := "_guard" }
def moduleGuardRef : StorageRef := { base := "_moduleGuard" }
def rawStorageRef (slot : Expr) : StorageRef :=
  { base := "_rawStorage", steps := [.mindex slot] }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "singleton", ty := addrSt },
    { name := "modules", ty := .mapping .address addrSt },
    { name := "owners", ty := .mapping .address addrSt },
    { name := "ownerCount", ty := uint256St },
    { name := "threshold", ty := uint256St },
    { name := "nonce", ty := uint256St },
    { name := "_deprecatedDomainSeparator", ty := bytes32St },
    { name := "signedMessages", ty := .mapping (.bytes bytes32Width) uint256St },
    { name := "approvedHashes",
      ty := .mapping .address (.mapping (.bytes bytes32Width) uint256St) },
    { name := "_fallbackHandler", ty := addrSt },
    { name := "_guard", ty := addrSt },
    { name := "_moduleGuard", ty := addrSt },
    { name := "_rawStorage", ty := .mapping (.int uint256Int) uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def modulesSlot (module : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord module) ⟨1⟩

def ownersSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨2⟩

def signedMessagesSlot (messageHash : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord messageHash) ⟨7⟩

def approvedHashesOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨8⟩

def approvedHashesSlot (owner messageHash : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord messageHash) (approvedHashesOwnerSlot owner)

def fallbackHandlerSlot : Ethereum.UInt256 :=
  ⟨0x6c9a6c4a39284e37ed1cf53d337577d14212a4870fb976a4366c693b939918d5⟩

def guardSlot : Ethereum.UInt256 :=
  ⟨0x4a204f620c8c5ccdca3fd54d003badd85ba500436a431f0cbda4f558c93c34c8⟩

def moduleGuardSlot : Ethereum.UInt256 :=
  ⟨0xb104e0b93118902c651344349b610029d694cfdec91c589c91ebafbcd0289947⟩

def loc (slot : Ethereum.UInt256) (offset : Fin 32) (size : Fin 33)
    (hbound : offset.val + size.val - 1 < 32) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := offset, size := size, hbound := hbound, type := ty }

def wordLoc (slot : Ethereum.UInt256) (ty : ElemType) : StorageLoc :=
  loc slot ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) ty

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  loc slot ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide) .address

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "singleton", steps := [] }, _ => some (addrLoc ⟨0⟩)
  | { base := "modules", steps := [.mindex module] }, _ => some (addrLoc (modulesSlot module))
  | { base := "owners", steps := [.mindex owner] }, _ => some (addrLoc (ownersSlot owner))
  | { base := "ownerCount", steps := [] }, _ => some (wordLoc ⟨3⟩ (.int uint256Int))
  | { base := "threshold", steps := [] }, _ => some (wordLoc ⟨4⟩ (.int uint256Int))
  | { base := "nonce", steps := [] }, _ => some (wordLoc ⟨5⟩ (.int uint256Int))
  | { base := "_deprecatedDomainSeparator", steps := [] }, _ =>
      some (wordLoc ⟨6⟩ (.bytes bytes32Width))
  | { base := "signedMessages", steps := [.mindex messageHash] }, _ =>
      some (wordLoc (signedMessagesSlot messageHash) (.int uint256Int))
  | { base := "approvedHashes", steps := [.mindex owner, .mindex messageHash] }, _ =>
      some (wordLoc (approvedHashesSlot owner messageHash) (.int uint256Int))
  | { base := "_fallbackHandler", steps := [] }, _ => some (addrLoc fallbackHandlerSlot)
  | { base := "_guard", steps := [] }, _ => some (addrLoc guardSlot)
  | { base := "_moduleGuard", steps := [] }, _ => some (addrLoc moduleGuardSlot)
  | { base := "_rawStorage", steps := [.mindex slot] }, _ =>
      some (wordLoc (keyValueToWord slot) (.int uint256Int))
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## External ABI for guard, token, and signature calls -/

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def transferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb
def supportsInterfaceSelector : ByteArray := selectorBytes 0x01 0xff 0xc9 0xa7
def isValidSignatureSelector : ByteArray := selectorBytes 0x16 0x26 0xba 0x7e
def checkTransactionSelector : ByteArray := selectorBytes 0x75 0xf0 0xbb 0x52
def checkAfterExecutionSelector : ByteArray := selectorBytes 0x93 0x27 0x13 0x68
def checkModuleTransactionSelector : ByteArray := selectorBytes 0x72 0x8c 0x29 0x72
def checkAfterModuleExecutionSelector : ByteArray := selectorBytes 0x2a 0xcc 0x37 0xaa

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.modern ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

def safeExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "transfer" then
      ABI.encodeCallWithSelector? transferSelector [addr, uint256] args
    else if name = "supportsInterface" then
      ABI.encodeCallWithSelector? supportsInterfaceSelector [bytes4] args
    else if name = "isValidSignature" then
      ABI.encodeCallWithSelector? isValidSignatureSelector [bytes32, bytesTy] args
    else if name = "checkTransaction" then
      ABI.encodeCallWithSelector? checkTransactionSelector
        [addr, uint256, bytesTy, uint8, uint256, uint256, uint256, addr, addr, bytesTy, addr]
        args
    else if name = "checkAfterExecution" then
      ABI.encodeCallWithSelector? checkAfterExecutionSelector [bytes32, boolTy] args
    else if name = "checkModuleTransaction" then
      ABI.encodeCallWithSelector? checkModuleTransactionSelector
        [addr, uint256, bytesTy, uint8, addr] args
    else if name = "checkAfterModuleExecution" then
      ABI.encodeCallWithSelector? checkAfterModuleExecutionSelector [bytes32, boolTy] args
    else
      none
  decode? := fun name out =>
    if name = "transfer" then
      decodeReturn? boolTy out
    else if name = "supportsInterface" then
      decodeReturn? boolTy out
    else if name = "isValidSignature" then
      decodeReturn? bytes32 out
    else if name = "checkTransaction" then
      decodeVoid? out
    else if name = "checkAfterExecution" then
      decodeVoid? out
    else if name = "checkModuleTransaction" then
      decodeReturn? bytes32 out
    else if name = "checkAfterModuleExecution" then
      decodeVoid? out
    else
      none

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (eqE callvalue (.intLit 0)) ]

def authorized : List Stmt :=
  [ .require (eqE sender this) ]

def validOperation : Expr :=
  leE (.var "operation") (.intLit 1)

def checkedExternalCallStmts (receiver : Expr) (name : Ident) (eth : Expr)
    (args : List Expr) (retVar : Ident) (perm : Bool := true) : List Stmt :=
  [ .require (gtE (.extCodeSize receiver) (.intLit 0)),
    .externalCall receiver name eth args retVar (perm := perm) ]

def isThisDelegatedAccountExpr : Expr :=
  eqE (.extCodePrefix this (.intLit 3)) (.bytesLit ⟨#[0xef, 0x01, 0x00]⟩)

def validOwnerExpr (owner : Expr) : Expr :=
  andE (neE owner zeroAddr)
    (andE (neE owner sentinelAddr)
      (orE (neE owner this) isThisDelegatedAccountExpr))

def ownerEnabledExpr (owner : Expr) : Expr :=
  andE (neE (.storage (ownersRef owner)) zeroAddr) (neE owner sentinelAddr)

def moduleEnabledExpr (module : Expr) : Expr :=
  andE (neE (.storage (modulesRef module)) zeroAddr) (neE module sentinelAddr)

def txDataHashExpr : Expr :=
  .keccak256 (.var "data")

def domainSeparatorExpr : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (bytes32, domainSeparatorTypehash),
        (uint256, .env .chainid),
        (uint256, addressAsUint256 this) ])

def transactionStructHashExpr (nonceExpr : Expr) : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (bytes32, safeTxTypehash),
        (uint256, addressAsUint256 (.var "to")),
        (uint256, .var "value"),
        (bytes32, txDataHashExpr),
        (uint256, .var "operation"),
        (uint256, .var "safeTxGas"),
        (uint256, .var "baseGas"),
        (uint256, .var "gasPrice"),
        (uint256, addressAsUint256 (.var "gasToken")),
        (uint256, addressAsUint256 (.var "refundReceiver")),
        (uint256, nonceExpr) ])

def transactionHashExpr (nonceExpr : Expr) : Expr :=
  .keccak256
    (.abiEncodePacked
      [ (bytes2, eip712Prefix),
        (bytes32, domainSeparatorExpr),
        (bytes32, transactionStructHashExpr nonceExpr) ])

def signatureOffsetExpr : Expr :=
  mulE (.intLit 65) (.var "i")

def signatureWordAt (base offset : Expr) : Expr :=
  .abiDecode bytes32 (.bytesSlice base offset (addE offset (.intLit 32)))

def signatureUintAt (base offset : Expr) : Expr :=
  .abiDecode uint256 (.bytesSlice base offset (addE offset (.intLit 32)))

def signatureByteAt (base offset : Expr) : Expr :=
  bytes1AsUint8 (.index base offset)

def ecrecoverCalldataExpr : Expr :=
  .abiEncodePacked
    [ (bytes32, .var "digest"),
      (uint256, .var "v"),
      (bytes32, .var "r"),
      (bytes32, .var "s") ]

/-! ## SafeMath and internal helper functions -/

def addFunction : FunctionDecl :=
  { name := "_add"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .letDecl "z" (some uint256) (add256 (.var "x") (.var "y")),
        .require (geE (.var "z") (.var "x")),
        .return [.var "z"] ] }

def subFunction : FunctionDecl :=
  { name := "_sub"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
        .require (leE (.var "z") (.var "x")),
        .return [.var "z"] ] }

def mulFunction : FunctionDecl :=
  { name := "_mul"
    params := [{ name := "x", ty := uint256 }, { name := "y", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ .letDecl "z" (some uint256) (mul256 (.var "x") (.var "y")),
        .require
          (orE (eqE (.var "y") (.intLit 0))
            (eqE (divE (.var "z") (.var "y")) (.var "x"))),
        .return [.var "z"] ] }

def executeFunction : FunctionDecl :=
  { name := "execute"
    params :=
      [ { name := "to", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 } ]
    returnType := [boolTy]
    body :=
      [ .ite (eqE (.var "operation") (.intLit 1))
          [ .delegateCall (.var "to") (.var "data") "success" "returnData" ]
          [ .lowLevelCall (.var "to") (.var "value") (.var "data") "success" "returnData" ],
        .return [.var "success"] ] }

def transferTokenFunction : FunctionDecl :=
  { name := "transferToken"
    params :=
      [ { name := "token", ty := addr }, { name := "receiver", ty := addr },
        { name := "amount", ty := uint256 } ]
    returnType := [boolTy]
    body :=
      [ .lowLevelCall (.var "token") (.intLit 0)
          (.abiEncodeCall "transfer" [.var "receiver", .var "amount"])
          "tokenSuccess" "tokenData",
        .return
          [ .ite (eqE (localLength "tokenData") (.intLit 0))
              (.var "tokenSuccess")
              (.ite (eqE (localLength "tokenData") (.intLit 32))
                (andE (.var "tokenSuccess")
                  (neE (.abiDecode uint256 (.var "tokenData")) (.intLit 0)))
                (.boolLit false)) ] ] }

def handlePaymentFunction : FunctionDecl :=
  { name := "handlePayment"
    params :=
      [ { name := "gasUsed", ty := uint256 }, { name := "baseGas", ty := uint256 },
        { name := "gasPrice", ty := uint256 }, { name := "gasToken", ty := addr },
        { name := "refundReceiver", ty := addr } ]
    returnType := [uint256]
    body :=
      [ .letDecl "receiver" (some addr)
          (.ite (eqE (.var "refundReceiver") zeroAddr) origin (.var "refundReceiver")),
        .internalCall "_add" [.var "gasUsed", .var "baseGas"] "gasTotal",
        .ite (eqE (.var "gasToken") zeroAddr)
          [ .internalCall "_mul"
              [.var "gasTotal", minE (.var "gasPrice") gasprice] "payment",
            .lowLevelCall (.var "receiver") (.var "payment") emptyBytes
              "refundSuccess" "refundData",
            .require (.var "refundSuccess") ]
          [ .internalCall "_mul" [.var "gasTotal", .var "gasPrice"] "payment",
            .internalCall "transferToken"
              [.var "gasToken", .var "receiver", .var "payment"] "transferred",
            .require (.var "transferred") ],
        .return [.var "payment"] ] }

def requireCanAddOwnerFunction : FunctionDecl :=
  { name := "requireCanAddOwner"
    params := [{ name := "owner", ty := addr }]
    returnType := []
    body :=
      [ .require (validOwnerExpr (.var "owner")),
        .require (eqE (.storage (ownersRef (.var "owner"))) zeroAddr) ] }

def requireCanRemoveOwnerFunction : FunctionDecl :=
  { name := "requireCanRemoveOwner"
    params := [{ name := "prevOwner", ty := addr }, { name := "owner", ty := addr }]
    returnType := []
    body :=
      [ .require (validOwnerExpr (.var "owner")),
        .require (eqE (.storage (ownersRef (.var "prevOwner"))) (.var "owner")) ] }

def changeThresholdBodyFunction : FunctionDecl :=
  { name := "changeThresholdBody"
    params := [{ name := "_threshold", ty := uint256 }]
    returnType := []
    body :=
      [ .require (leE (.var "_threshold") (.storage ownerCountRef)),
        .require (neE (.var "_threshold") (.intLit 0)),
        .assign .storage thresholdRef (.var "_threshold") ] }

def setupOwnersFunction : FunctionDecl :=
  { name := "setupOwners"
    params :=
      [ { name := "_owners", ty := addrArrayTy }, { name := "_threshold", ty := uint256 } ]
    returnType := []
    body :=
      [ .require (eqE (.storage thresholdRef) (.intLit 0)),
        .require (leE (.var "_threshold") (localLength "_owners")),
        .require (neE (.var "_threshold") (.intLit 0)),
        .letDecl "currentOwner" (some addr) sentinelAddr,
        .letDecl "ownersLength" (some uint256) (localLength "_owners"),
        .letDecl "i" (some uint256) (.intLit 0),
        .while (ltE (.var "i") (.var "ownersLength"))
          [ .letDecl "owner" (some addr) (arrGet "_owners" (.var "i")),
            .require (neE (.var "owner") (.var "currentOwner")),
            .internalCall "requireCanAddOwner" [.var "owner"] "_ok",
            .assign .storage (ownersRef (.var "currentOwner")) (.var "owner"),
            .assign .localVar (varRef "currentOwner") (.var "owner"),
            .assign .localVar (varRef "i") (wrap256 (addE (.var "i") (.intLit 1))) ],
        .assign .storage (ownersRef (.var "currentOwner")) sentinelAddr,
        .assign .storage ownerCountRef (.var "ownersLength"),
        .assign .storage thresholdRef (.var "_threshold") ] }

def internalSetFallbackHandlerFunction : FunctionDecl :=
  { name := "internalSetFallbackHandler"
    params := [{ name := "handler", ty := addr }]
    returnType := []
    body :=
      [ .require (neE (.var "handler") this),
        .assign .storage fallbackHandlerRef (.var "handler") ] }

def setupModulesFunction : FunctionDecl :=
  { name := "setupModules"
    params := [{ name := "to", ty := addr }, { name := "data", ty := bytesTy }]
    returnType := []
    body :=
      [ .require (eqE (.storage (modulesRef sentinelAddr)) zeroAddr),
        .assign .storage (modulesRef sentinelAddr) sentinelAddr,
        .ite (neE (.var "to") zeroAddr)
          [ .require (gtE (.extCodeSize (.var "to")) (.intLit 0)),
            .internalCall "execute"
              [.var "to", .intLit 0, .var "data", .intLit 1] "setupSuccess",
            .require (.var "setupSuccess") ]
          [] ] }

def preModuleExecutionFunction : FunctionDecl :=
  { name := "preModuleExecution"
    params :=
      [ { name := "to", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 } ]
    returnType := [addr, bytes32]
    body :=
      [ .require validOperation,
        .letDecl "guard" (some addr) (.storage moduleGuardRef),
        .letDecl "guardHash" (some bytes32) zeroBytes32,
        .require (andE (neE sender sentinelAddr) (neE (.storage (modulesRef sender)) zeroAddr)),
        .ite (neE (.var "guard") zeroAddr)
          (checkedExternalCallStmts (.var "guard") "checkModuleTransaction" (.intLit 0)
            [.var "to", .var "value", .var "data", .var "operation", sender]
            "guardHashCall" ++
            [ .assign .localVar (varRef "guardHash") (.var "guardHashCall") ])
          [],
        .return [.var "guard", .var "guardHash"] ] }

def postModuleExecutionFunction : FunctionDecl :=
  { name := "postModuleExecution"
    params :=
      [ { name := "guard", ty := addr }, { name := "guardHash", ty := bytes32 },
        { name := "success", ty := boolTy } ]
    returnType := []
    body :=
      [ .ite (neE (.var "guard") zeroAddr)
          (checkedExternalCallStmts (.var "guard") "checkAfterModuleExecution" (.intLit 0)
            [.var "guardHash", .var "success"] "_after")
          [] ] }

def validateContractSignatureFunction : FunctionDecl :=
  { name := "validateContractSignature"
    params :=
      [ { name := "owner", ty := addr }, { name := "dataHash", ty := bytes32 },
        { name := "signature", ty := bytesTy } ]
    returnType := [boolTy]
    body :=
      [ .lowLevelCall (.var "owner") (.intLit 0)
          (.abiEncodeCall "isValidSignature" [.var "dataHash", .var "signature"])
          "sigSuccess" "sigResult" false,
        .return
          [ andE (.var "sigSuccess")
              (andE (eqE (localLength "sigResult") (.intLit 32))
                (eqE (.abiDecode bytes32 (.var "sigResult")) eip1271MagicBytes32)) ] ] }

def checkContractSignatureFunction : FunctionDecl :=
  { name := "checkContractSignature"
    params :=
      [ { name := "owner", ty := addr }, { name := "dataHash", ty := bytes32 },
        { name := "signatures", ty := bytesTy }, { name := "offset", ty := uint256 } ]
    returnType := []
    body :=
      [ .internalCall "_add" [.var "offset", .intLit 32] "signatureDataStart",
        .require (leE (.var "signatureDataStart") (localLength "signatures")),
        .letDecl "contractSignatureLen" (some uint256)
          (signatureUintAt (.var "signatures") (.var "offset")),
        .internalCall "_add"
          [.var "signatureDataStart", .var "contractSignatureLen"] "signatureDataEnd",
        .require (leE (.var "signatureDataEnd") (localLength "signatures")),
        .letDecl "contractSignature" (some bytesTy)
          (.bytesSlice (.var "signatures") (.var "signatureDataStart") (.var "signatureDataEnd")),
        .internalCall "validateContractSignature"
          [.var "owner", .var "dataHash", .var "contractSignature"] "valid",
        .require (.var "valid") ] }

def p256VerifyFunction : FunctionDecl :=
  { name := "p256Verify"
    params :=
      [ { name := "h", ty := bytes32 }, { name := "r", ty := bytes32 },
        { name := "s", ty := bytes32 }, { name := "qx", ty := uint256 },
        { name := "qy", ty := uint256 } ]
    returnType := [boolTy]
    body :=
      [ .lowLevelCall p256Precompile (.intLit 0)
          (.abiEncodePacked
            [ (bytes32, .var "h"), (bytes32, .var "r"), (bytes32, .var "s"),
              (uint256, .var "qx"), (uint256, .var "qy") ])
          "p256Success" "p256Result" false,
        .return
          [ andE (.var "p256Success")
              (andE (eqE (localLength "p256Result") (.intLit 32))
                (eqE (.abiDecode uint256 (.var "p256Result")) (.intLit 1))) ] ] }

def ecrecoverAddressFunction : FunctionDecl :=
  { name := "ecrecoverAddress"
    params :=
      [ { name := "digest", ty := bytes32 }, { name := "v", ty := uint8 },
        { name := "r", ty := bytes32 }, { name := "s", ty := bytes32 } ]
    returnType := [addr]
    body :=
      [ .lowLevelCall ecrecoverPrecompile (.intLit 0) ecrecoverCalldataExpr
          "ecrecoverSuccess" "ecrecoverData" false,
        .require (.var "ecrecoverSuccess"),
        .return [.abiDecode addr (.var "ecrecoverData")] ] }

def checkNSignaturesImplFunction : FunctionDecl :=
  { name := "checkNSignaturesImpl"
    params :=
      [ { name := "executor", ty := addr }, { name := "dataHash", ty := bytes32 },
        { name := "signatures", ty := bytesTy },
        { name := "requiredSignatures", ty := uint256 } ]
    returnType := []
    body :=
      [ .internalCall "_mul" [.var "requiredSignatures", .intLit 65] "requiredBytes",
        .require (geE (localLength "signatures") (.var "requiredBytes")),
        .letDecl "lastOwner" (some addr) zeroAddr,
        .letDecl "currentOwner" (some addr) zeroAddr,
        .letDecl "i" (some uint256) (.intLit 0),
        .while (ltE (.var "i") (.var "requiredSignatures"))
          [ .letDecl "signatureOffset" (some uint256) signatureOffsetExpr,
            .letDecl "r" (some bytes32)
              (signatureWordAt (.var "signatures") (.var "signatureOffset")),
            .letDecl "s" (some bytes32)
              (signatureWordAt (.var "signatures") (addE (.var "signatureOffset") (.intLit 32))),
            .letDecl "v" (some uint8)
              (signatureByteAt (.var "signatures") (addE (.var "signatureOffset") (.intLit 64))),
            .ite (eqE (.var "v") (.intLit 0))
              [ .assign .localVar (varRef "currentOwner")
                  (uint256AsAddress (bytes32AsUint256 (.var "r"))),
                .letDecl "contractOffset" (some uint256) (bytes32AsUint256 (.var "s")),
                .require (geE (.var "contractOffset") (.var "requiredBytes")),
                .internalCall "checkContractSignature"
                  [.var "currentOwner", .var "dataHash", .var "signatures", .var "contractOffset"]
                  "_contractSigOk" ]
              [ .ite (eqE (.var "v") (.intLit 1))
                  [ .assign .localVar (varRef "currentOwner")
                      (uint256AsAddress (bytes32AsUint256 (.var "r"))),
                    .require
                      (orE (eqE (.var "executor") (.var "currentOwner"))
                        (neE (.storage (approvedHashesRef (.var "currentOwner") (.var "dataHash")))
                          (.intLit 0))) ]
                  [ .ite (eqE (.var "v") (.intLit 2))
                      [ .assign .localVar (varRef "currentOwner")
                          (uint256AsAddress (bytes32AsUint256 (.var "r"))),
                        .letDecl "p256Offset" (some uint256) (bytes32AsUint256 (.var "s")),
                        .require (geE (.var "p256Offset") (.var "requiredBytes")),
                        .internalCall "_add" [.var "p256Offset", .intLit 128] "p256End",
                        .require (leE (.var "p256End") (localLength "signatures")),
                        .letDecl "p256r" (some bytes32)
                          (signatureWordAt (.var "signatures") (.var "p256Offset")),
                        .letDecl "p256s" (some bytes32)
                          (signatureWordAt (.var "signatures") (addE (.var "p256Offset") (.intLit 32))),
                        .letDecl "qx" (some uint256)
                          (signatureUintAt (.var "signatures") (addE (.var "p256Offset") (.intLit 64))),
                        .letDecl "qy" (some uint256)
                          (signatureUintAt (.var "signatures") (addE (.var "p256Offset") (.intLit 96))),
                        .letDecl "signerAddress" (some addr)
                          (uint256AsAddress
                            (bytes32AsUint256
                              (.keccak256
                                (.abiEncodePacked
                                  [(uint256, .var "qx"), (uint256, .var "qy")])))),
                        .internalCall "p256Verify"
                          [.var "dataHash", .var "p256r", .var "p256s", .var "qx", .var "qy"]
                          "p256Ok",
                        .require
                          (andE (eqE (.var "currentOwner") (.var "signerAddress"))
                            (.var "p256Ok")) ]
                      [ .ite (gtE (.var "v") (.intLit 30))
                          [ .letDecl "ethSignedHash" (some bytes32)
                              (.keccak256
                                (.abiEncodePacked
                                  [(bytesTy, ethSignPrefix), (bytes32, .var "dataHash")])),
                            .internalCall "ecrecoverAddress"
                              [.var "ethSignedHash", u8 (subE (.var "v") (.intLit 4)),
                                .var "r", .var "s"] "recoveredOwner",
                            .assign .localVar (varRef "currentOwner") (.var "recoveredOwner") ]
                          [ .internalCall "ecrecoverAddress"
                              [.var "dataHash", .var "v", .var "r", .var "s"] "recoveredOwner",
                            .assign .localVar (varRef "currentOwner") (.var "recoveredOwner") ] ] ] ],
            .require
              (andE (gtE (.var "currentOwner") (.var "lastOwner"))
                (andE (neE (.storage (ownersRef (.var "currentOwner"))) zeroAddr)
                  (neE (.var "currentOwner") sentinelAddr))),
            .assign .localVar (varRef "lastOwner") (.var "currentOwner"),
            .assign .localVar (varRef "i") (wrap256 (addE (.var "i") (.intLit 1))) ] ] }

def checkSignaturesImplFunction : FunctionDecl :=
  { name := "checkSignaturesImpl"
    params :=
      [ { name := "executor", ty := addr }, { name := "dataHash", ty := bytes32 },
        { name := "signatures", ty := bytesTy } ]
    returnType := []
    body :=
      [ .letDecl "_threshold" (some uint256) (.storage thresholdRef),
        .require (neE (.var "_threshold") (.intLit 0)),
        .internalCall "checkNSignaturesImpl"
          [.var "executor", .var "dataHash", .var "signatures", .var "_threshold"]
          "_checked" ] }

def internalFunctions : List FunctionDecl :=
  [ addFunction,
    subFunction,
    mulFunction,
    executeFunction,
    transferTokenFunction,
    handlePaymentFunction,
    requireCanAddOwnerFunction,
    requireCanRemoveOwnerFunction,
    changeThresholdBodyFunction,
    setupOwnersFunction,
    internalSetFallbackHandlerFunction,
    setupModulesFunction,
    preModuleExecutionFunction,
    postModuleExecutionFunction,
    validateContractSignatureFunction,
    checkContractSignatureFunction,
    p256VerifyFunction,
    ecrecoverAddressFunction,
    checkNSignaturesImplFunction,
    checkSignaturesImplFunction ]

/-! ## Constructor, receive, and fallback -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body := nonpayable ++ [ .assign .storage thresholdRef (.intLit 1) ] }

def receiveTransition : TransitionDecl :=
  { name := "receive"
    params := []
    returnType := []
    body := [] }

def fallbackTransition : TransitionDecl :=
  { name := "fallback"
    params := [{ name := "calldata", ty := bytesTy }]
    returnType := [bytesTy]
    body :=
      nonpayable ++
      [ .letDecl "handler" (some addr) (.storage fallbackHandlerRef),
        .ite (eqE (.var "handler") zeroAddr)
          [ .return [emptyBytes] ]
          [ .lowLevelCall (.var "handler") (.intLit 0)
              (.abiEncodePacked [(bytesTy, .var "calldata"), (addr, sender)])
              "handlerSuccess" "handlerReturn",
            .require (.var "handlerSuccess"),
            .return [.var "handlerReturn"] ] ] }

/-! ## Public ABI surface -/

def versionTransition : TransitionDecl :=
  { name := "VERSION"
    params := []
    returnType := [stringTy]
    body := nonpayable ++ [ .return [.bytesLit (String.toByteArray "1.5.0")] ] }

def addownerwiththresholdTransition : TransitionDecl :=
  { name := "addOwnerWithThreshold"
    params := [ { name := "owner", ty := addr }, { name := "_threshold", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .internalCall "requireCanAddOwner" [.var "owner"] "_ok",
        .assign .storage (ownersRef (.var "owner")) (.storage (ownersRef sentinelAddr)),
        .assign .storage (ownersRef sentinelAddr) (.var "owner"),
        .assign .storage ownerCountRef (wrap256 (addE (.storage ownerCountRef) (.intLit 1))),
        .ite (neE (.storage thresholdRef) (.var "_threshold"))
          [ .internalCall "changeThresholdBody" [.var "_threshold"] "_thresholdChanged" ]
          [] ] }

def approvehashTransition : TransitionDecl :=
  { name := "approveHash"
    params := [ { name := "hashToApprove", ty := bytes32 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .require (neE (.storage (ownersRef sender)) zeroAddr),
        .assign .storage (approvedHashesRef sender (.var "hashToApprove")) (.intLit 1) ] }

def approvedhashesTransition : TransitionDecl :=
  { name := "approvedHashes"
    params := [ { name := "arg0", ty := addr }, { name := "arg1", ty := bytes32 } ]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (approvedHashesRef (.var "arg0") (.var "arg1"))] ] }

def changethresholdTransition : TransitionDecl :=
  { name := "changeThreshold"
    params := [ { name := "_threshold", ty := uint256 } ]
    returnType := []
    body := nonpayable ++ authorized ++ [ .internalCall "changeThresholdBody" [.var "_threshold"] "_ok" ] }

def checknsignaturesTransition : TransitionDecl :=
  { name := "checkNSignatures"
    params :=
      [ { name := "dataHash", ty := bytes32 }, { name := "data", ty := bytesTy },
        { name := "signatures", ty := bytesTy }, { name := "requiredSignatures", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .internalCall "checkNSignaturesImpl"
          [sender, .var "dataHash", .var "signatures", .var "requiredSignatures"] "_checked" ] }

def checknsignaturesAddressBytes32BytesUint256Transition : TransitionDecl :=
  { name := "checkNSignatures"
    params :=
      [ { name := "executor", ty := addr }, { name := "dataHash", ty := bytes32 },
        { name := "signatures", ty := bytesTy },
        { name := "requiredSignatures", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++
      [ .internalCall "checkNSignaturesImpl"
          [.var "executor", .var "dataHash", .var "signatures", .var "requiredSignatures"]
          "_checked" ] }

def checksignaturesTransition : TransitionDecl :=
  { name := "checkSignatures"
    params :=
      [ { name := "dataHash", ty := bytes32 }, { name := "data", ty := bytesTy },
        { name := "signatures", ty := bytesTy } ]
    returnType := []
    body :=
      nonpayable ++
      [ .internalCall "checkSignaturesImpl" [sender, .var "dataHash", .var "signatures"]
          "_checked" ] }

def checksignaturesAddressBytes32BytesTransition : TransitionDecl :=
  { name := "checkSignatures"
    params :=
      [ { name := "executor", ty := addr }, { name := "dataHash", ty := bytes32 },
        { name := "signatures", ty := bytesTy } ]
    returnType := []
    body :=
      nonpayable ++
      [ .internalCall "checkSignaturesImpl"
          [.var "executor", .var "dataHash", .var "signatures"] "_checked" ] }

def disablemoduleTransition : TransitionDecl :=
  { name := "disableModule"
    params := [ { name := "prevModule", ty := addr }, { name := "module", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .require (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)),
        .require (eqE (.storage (modulesRef (.var "prevModule"))) (.var "module")),
        .assign .storage (modulesRef (.var "prevModule")) (.storage (modulesRef (.var "module"))),
        .assign .storage (modulesRef (.var "module")) zeroAddr ] }

def domainseparatorTransition : TransitionDecl :=
  { name := "domainSeparator"
    params := []
    returnType := [bytes32]
    body := nonpayable ++ [ .return [domainSeparatorExpr] ] }

def enablemoduleTransition : TransitionDecl :=
  { name := "enableModule"
    params := [ { name := "module", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .require (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)),
        .require (eqE (.storage (modulesRef (.var "module"))) zeroAddr),
        .assign .storage (modulesRef (.var "module")) (.storage (modulesRef sentinelAddr)),
        .assign .storage (modulesRef sentinelAddr) (.var "module") ] }

def exectransactionTransition : TransitionDecl :=
  { name := "execTransaction"
    params :=
      [ { name := "to", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 },
        { name := "safeTxGas", ty := uint256 }, { name := "baseGas", ty := uint256 },
        { name := "gasPrice", ty := uint256 }, { name := "gasToken", ty := addr },
        { name := "refundReceiver", ty := addr }, { name := "signatures", ty := bytesTy } ]
    returnType := [boolTy]
    body :=
      [ .require validOperation,
        .letDecl "nonceBefore" (some uint256) (.storage nonceRef),
        .letDecl "txHash" (some bytes32) (transactionHashExpr (.var "nonceBefore")),
        .assign .storage nonceRef (wrap256 (addE (.var "nonceBefore") (.intLit 1))),
        .internalCall "checkSignaturesImpl" [sender, .var "txHash", .var "signatures"] "_sigOk",
        .letDecl "guard" (some addr) (.storage guardRef),
        .ite (neE (.var "guard") zeroAddr)
          (checkedExternalCallStmts (.var "guard") "checkTransaction" (.intLit 0)
            [ .var "to", .var "value", .var "data", .var "operation", .var "safeTxGas",
              .var "baseGas", .var "gasPrice", .var "gasToken", .var "refundReceiver",
              .var "signatures", sender ]
            "_guardChecked")
          [],
        .letGas "gasForCheck",
        .require
          (geE (.var "gasForCheck")
            (addE
              (maxE (divE (shlE (.var "safeTxGas") (.intLit 6)) (.intLit 63))
                (addE (.var "safeTxGas") (.intLit 2500)))
              (.intLit 500))),
        .letGas "gasBefore",
        .internalCall "execute"
          [.var "to", .var "value", .var "data", .var "operation"] "success",
        .letGas "gasAfter",
        .internalCall "_sub" [.var "gasBefore", .var "gasAfter"] "gasUsed",
        .require
          (orE (.var "success")
            (orE (neE (.var "safeTxGas") (.intLit 0)) (neE (.var "gasPrice") (.intLit 0)))),
        .letDecl "payment" (some uint256) (.intLit 0),
        .ite (gtE (.var "gasPrice") (.intLit 0))
          [ .internalCall "handlePayment"
              [.var "gasUsed", .var "baseGas", .var "gasPrice", .var "gasToken",
                .var "refundReceiver"] "paymentCall",
            .assign .localVar (varRef "payment") (.var "paymentCall") ]
          [],
        .ite (neE (.var "guard") zeroAddr)
          (checkedExternalCallStmts (.var "guard") "checkAfterExecution" (.intLit 0)
            [.var "txHash", .var "success"] "_guardAfter")
          [],
        .return [.var "success"] ] }

def exectransactionfrommoduleTransition : TransitionDecl :=
  { name := "execTransactionFromModule"
    params :=
      [ { name := "to", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 } ]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ .require validOperation,
        .internalCall "preModuleExecution"
          [.var "to", .var "value", .var "data", .var "operation"] "pre",
        .internalCall "execute" [.var "to", .var "value", .var "data", .var "operation"]
          "success",
        .internalCall "postModuleExecution" [tuple0 (.var "pre"), tuple1 (.var "pre"), .var "success"]
          "_post",
        .return [.var "success"] ] }

def exectransactionfrommodulereturndataTransition : TransitionDecl :=
  { name := "execTransactionFromModuleReturnData"
    params :=
      [ { name := "to", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 } ]
    returnType := [boolTy, bytesTy]
    body :=
      nonpayable ++
      [ .require validOperation,
        .internalCall "preModuleExecution"
          [.var "to", .var "value", .var "data", .var "operation"] "pre",
        .ite (eqE (.var "operation") (.intLit 1))
          [ .delegateCall (.var "to") (.var "data") "success" "returnData" ]
          [ .lowLevelCall (.var "to") (.var "value") (.var "data") "success" "returnData" ],
        .internalCall "postModuleExecution" [tuple0 (.var "pre"), tuple1 (.var "pre"), .var "success"]
          "_post",
        .return [.var "success", .var "returnData"] ] }

def getmodulespaginatedTransition : TransitionDecl :=
  { name := "getModulesPaginated"
    params := [ { name := "start", ty := addr }, { name := "pageSize", ty := uint256 } ]
    returnType := [(.dynamicArray addr), addr]
    body :=
      nonpayable ++
      [ .require (orE (eqE (.var "start") sentinelAddr) (moduleEnabledExpr (.var "start"))),
        .require (neE (.var "pageSize") (.intLit 0)),
        .letDecl "moduleCount" (some uint256) (.intLit 0),
        .letDecl "next" (some addr) (.storage (modulesRef (.var "start"))),
        .letDecl "last" (some addr) zeroAddr,
        .while
          (andE (andE (neE (.var "next") zeroAddr) (neE (.var "next") sentinelAddr))
            (ltE (.var "moduleCount") (.var "pageSize")))
          [ .assign .localVar (varRef "last") (.var "next"),
            .assign .localVar (varRef "next") (.storage (modulesRef (.var "next"))),
            .assign .localVar (varRef "moduleCount")
              (wrap256 (addE (.var "moduleCount") (.intLit 1))) ],
        .ite (neE (.var "next") sentinelAddr)
          [ .require (gtE (.var "moduleCount") (.intLit 0)),
            .assign .localVar (varRef "next") (.var "last") ]
          [],
        .letDecl "array" (some (.dynamicArray addr)) (.newArray addrSt (.var "moduleCount")),
        .letDecl "fill" (some uint256) (.intLit 0),
        .letDecl "current" (some addr) (.storage (modulesRef (.var "start"))),
        .while (ltE (.var "fill") (.var "moduleCount"))
          [ arrSet "array" (.var "fill") (.var "current"),
            .assign .localVar (varRef "current") (.storage (modulesRef (.var "current"))),
            .assign .localVar (varRef "fill") (wrap256 (addE (.var "fill") (.intLit 1))) ],
        .return [.var "array", .var "next"] ] }

def getownersTransition : TransitionDecl :=
  { name := "getOwners"
    params := []
    returnType := [(.dynamicArray addr)]
    body :=
      nonpayable ++
      [ .letDecl "array" (some (.dynamicArray addr)) (.newArray addrSt (.storage ownerCountRef)),
        .letDecl "index" (some uint256) (.intLit 0),
        .letDecl "currentOwner" (some addr) (.storage (ownersRef sentinelAddr)),
        .while (neE (.var "currentOwner") sentinelAddr)
          [ arrSet "array" (.var "index") (.var "currentOwner"),
            .assign .localVar (varRef "currentOwner")
              (.storage (ownersRef (.var "currentOwner"))),
            .assign .localVar (varRef "index") (wrap256 (addE (.var "index") (.intLit 1))) ],
        .return [.var "array"] ] }

def getstorageatTransition : TransitionDecl :=
  { name := "getStorageAt"
    params := [ { name := "offset", ty := uint256 }, { name := "length", ty := uint256 } ]
    returnType := [bytesTy]
    body :=
      nonpayable ++
      [ .letDecl "result" (some bytesTy) emptyBytes,
        .letDecl "index" (some uint256) (.intLit 0),
        .while (ltE (.var "index") (.var "length"))
          [ .assign .localVar (varRef "result")
              (.abiEncodePacked
                [ (bytesTy, .var "result"),
                  (uint256, .storage (rawStorageRef (addE (.var "offset") (.var "index")))) ]),
            .assign .localVar (varRef "index") (wrap256 (addE (.var "index") (.intLit 1))) ],
        .return [.var "result"] ] }

def getthresholdTransition : TransitionDecl :=
  { name := "getThreshold"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage thresholdRef] ] }

def gettransactionhashTransition : TransitionDecl :=
  { name := "getTransactionHash"
    params :=
      [ { name := "to", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 },
        { name := "safeTxGas", ty := uint256 }, { name := "baseGas", ty := uint256 },
        { name := "gasPrice", ty := uint256 }, { name := "gasToken", ty := addr },
        { name := "refundReceiver", ty := addr }, { name := "_nonce", ty := uint256 } ]
    returnType := [bytes32]
    body := nonpayable ++ [ .require validOperation, .return [transactionHashExpr (.var "_nonce")] ] }

def ismoduleenabledTransition : TransitionDecl :=
  { name := "isModuleEnabled"
    params := [ { name := "module", ty := addr } ]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [moduleEnabledExpr (.var "module")] ] }

def isownerTransition : TransitionDecl :=
  { name := "isOwner"
    params := [ { name := "owner", ty := addr } ]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [ownerEnabledExpr (.var "owner")] ] }

def nonceTransition : TransitionDecl :=
  { name := "nonce"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage nonceRef] ] }

def removeownerTransition : TransitionDecl :=
  { name := "removeOwner"
    params :=
      [ { name := "prevOwner", ty := addr }, { name := "owner", ty := addr },
        { name := "_threshold", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .assign .storage ownerCountRef (wrap256 (subE (.storage ownerCountRef) (.intLit 1))),
        .require (geE (.storage ownerCountRef) (.var "_threshold")),
        .internalCall "requireCanRemoveOwner" [.var "prevOwner", .var "owner"] "_ok",
        .assign .storage (ownersRef (.var "prevOwner")) (.storage (ownersRef (.var "owner"))),
        .assign .storage (ownersRef (.var "owner")) zeroAddr,
        .ite (neE (.storage thresholdRef) (.var "_threshold"))
          [ .internalCall "changeThresholdBody" [.var "_threshold"] "_thresholdChanged" ]
          [] ] }

def setfallbackhandlerTransition : TransitionDecl :=
  { name := "setFallbackHandler"
    params := [ { name := "handler", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .internalCall "internalSetFallbackHandler" [.var "handler"] "_ok" ] }

def setguardTransition : TransitionDecl :=
  { name := "setGuard"
    params := [ { name := "guard", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .ite (neE (.var "guard") zeroAddr)
          (checkedExternalCallStmts (.var "guard") "supportsInterface" (.intLit 0)
            [transactionGuardInterfaceId] "supported" (perm := false) ++
            [ .require (.var "supported") ])
          [],
        .assign .storage guardRef (.var "guard") ] }

def setmoduleguardTransition : TransitionDecl :=
  { name := "setModuleGuard"
    params := [ { name := "moduleGuard", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .ite (neE (.var "moduleGuard") zeroAddr)
          (checkedExternalCallStmts (.var "moduleGuard") "supportsInterface" (.intLit 0)
            [moduleGuardInterfaceId] "supported" (perm := false) ++
            [ .require (.var "supported") ])
          [],
        .assign .storage moduleGuardRef (.var "moduleGuard") ] }

def setupTransition : TransitionDecl :=
  { name := "setup"
    params :=
      [ { name := "_owners", ty := (.dynamicArray addr) },
        { name := "_threshold", ty := uint256 }, { name := "to", ty := addr },
        { name := "data", ty := bytesTy }, { name := "fallbackHandler", ty := addr },
        { name := "paymentToken", ty := addr }, { name := "payment", ty := uint256 },
        { name := "paymentReceiver", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++
      [ .internalCall "setupOwners" [.var "_owners", .var "_threshold"] "_ownersSetup",
        .ite (neE (.var "fallbackHandler") zeroAddr)
          [ .internalCall "internalSetFallbackHandler" [.var "fallbackHandler"] "_fallbackSet" ]
          [],
        .internalCall "setupModules" [.var "to", .var "data"] "_modulesSetup",
        .ite (gtE (.var "payment") (.intLit 0))
          [ .internalCall "handlePayment"
              [.var "payment", .intLit 0, .intLit 1, .var "paymentToken",
                .var "paymentReceiver"] "_paymentDone" ]
          [] ] }

def signedmessagesTransition : TransitionDecl :=
  { name := "signedMessages"
    params := [ { name := "arg0", ty := bytes32 } ]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (signedMessagesRef (.var "arg0"))] ] }

def simulateandrevertTransition : TransitionDecl :=
  { name := "simulateAndRevert"
    params :=
      [ { name := "targetContract", ty := addr }, { name := "calldataPayload", ty := bytesTy } ]
    returnType := []
    body :=
      nonpayable ++
      [ .delegateCall (.var "targetContract") (.var "calldataPayload")
          "simulateSuccess" "simulateReturn",
        .require (.boolLit false) ] }

def swapownerTransition : TransitionDecl :=
  { name := "swapOwner"
    params :=
      [ { name := "prevOwner", ty := addr }, { name := "oldOwner", ty := addr },
        { name := "newOwner", ty := addr } ]
    returnType := []
    body :=
      nonpayable ++ authorized ++
      [ .internalCall "requireCanAddOwner" [.var "newOwner"] "_canAdd",
        .internalCall "requireCanRemoveOwner" [.var "prevOwner", .var "oldOwner"] "_canRemove",
        .assign .storage (ownersRef (.var "newOwner")) (.storage (ownersRef (.var "oldOwner"))),
        .assign .storage (ownersRef (.var "prevOwner")) (.var "newOwner"),
        .assign .storage (ownersRef (.var "oldOwner")) zeroAddr ] }

def transitions : List TransitionDecl :=
  [ versionTransition,
    addownerwiththresholdTransition,
    approvehashTransition,
    approvedhashesTransition,
    changethresholdTransition,
    checknsignaturesTransition,
    checknsignaturesAddressBytes32BytesUint256Transition,
    checksignaturesTransition,
    checksignaturesAddressBytes32BytesTransition,
    disablemoduleTransition,
    domainseparatorTransition,
    enablemoduleTransition,
    exectransactionTransition,
    exectransactionfrommoduleTransition,
    exectransactionfrommodulereturndataTransition,
    getmodulespaginatedTransition,
    getownersTransition,
    getstorageatTransition,
    getthresholdTransition,
    gettransactionhashTransition,
    ismoduleenabledTransition,
    isownerTransition,
    nonceTransition,
    removeownerTransition,
    setfallbackhandlerTransition,
    setguardTransition,
    setmoduleguardTransition,
    setupTransition,
    signedmessagesTransition,
    simulateandrevertTransition,
    swapownerTransition ]

def contract : ContractDecl :=
  { name := "Safe"
    storage := storageDecls
    ctor := constructorDecl
    functions := internalFunctions
    transitions := transitions
    receive := some receiveTransition
    fallback := some fallbackTransition }

def config : Config :=
  { storage := storageLayout
    externalABI := safeExternalABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Safe
