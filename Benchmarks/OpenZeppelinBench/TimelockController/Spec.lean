import Solm.Semantics
import Solm.SolidityLayout

/-!
# OpenZeppelin TimelockController benchmark spec

Solm specification for `TimelockControllerBench`, a payable wrapper around OpenZeppelin
`TimelockController` compiled with solc 0.8.35. The wrapper fixes the constructor to:

* `minDelay = 1 days`
* `msg.sender` as initial admin, proposer, and canceller
* `address(0)` as the initial executor, making execution open until revoked

Events, custom-error payloads, and bubbled revert bytes are omitted because the current equivalence
observes storage, calls, return values, and revert/non-revert behavior, not logs or revert data.
The event-only loop in `scheduleBatch` is therefore intentionally absent. Operation ids use the
standard Solidity `abi.encode(...)` tuple encoding through the benchmark-local ABI hooks below.
-/

open Solm ABI

namespace OpenZeppelinBench.TimelockController

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes4Width : Fin 32 := ⟨3, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def bytes4 : ABIType := .elem (.bytes bytes4Width)
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def addrArray : ABIType := .dynamicArray addr
def uint256Array : ABIType := .dynamicArray uint256
def bytesArray : ABIType := .dynamicArray bytesTy

def boolSt : StorageType := .elem .bool
def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def initialMinDelay : Expr := .intLit 86400
def doneTimestamp : Expr := .intLit 1

def fixedBytes32 (bytes : List UInt8) : Expr :=
  .fixedBytesLit bytes32Width bytes

def fixedBytes4 (bytes : List UInt8) : Expr :=
  .fixedBytesLit bytes4Width bytes

def defaultAdminRole : Expr :=
  fixedBytes32 (List.replicate 32 0)

-- keccak256("PROPOSER_ROLE"), as emitted in the optimized runtime.
def proposerRole : Expr :=
  fixedBytes32
    [ 0xb0, 0x9a, 0xa5, 0xae, 0xb3, 0x70, 0x2c, 0xfd,
      0x50, 0xb6, 0xb6, 0x2b, 0xc4, 0x53, 0x26, 0x04,
      0x93, 0x8f, 0x21, 0x24, 0x8a, 0x27, 0xa1, 0xd5,
      0xca, 0x73, 0x60, 0x82, 0xb6, 0x81, 0x9c, 0xc1 ]

-- keccak256("EXECUTOR_ROLE"), as emitted in the optimized runtime.
def executorRole : Expr :=
  fixedBytes32
    [ 0xd8, 0xaa, 0x0f, 0x31, 0x94, 0x97, 0x1a, 0x2a,
      0x11, 0x66, 0x79, 0xf7, 0xc2, 0x09, 0x0f, 0x69,
      0x39, 0xc8, 0xd4, 0xe0, 0x1a, 0x2a, 0x8d, 0x7e,
      0x41, 0xd5, 0x5e, 0x53, 0x51, 0x46, 0x9e, 0x63 ]

-- keccak256("CANCELLER_ROLE"), as emitted in the optimized runtime.
def cancellerRole : Expr :=
  fixedBytes32
    [ 0xfd, 0x64, 0x3c, 0x72, 0x71, 0x0c, 0x63, 0xc0,
      0x18, 0x02, 0x59, 0xab, 0xa6, 0xb2, 0xd0, 0x54,
      0x51, 0xe3, 0x59, 0x1a, 0x24, 0xe5, 0x8b, 0x62,
      0x23, 0x93, 0x78, 0x08, 0x57, 0x26, 0xf7, 0x83 ]

def ierc165Id : Expr := fixedBytes4 [0x01, 0xff, 0xc9, 0xa7]
def iaccessControlId : Expr := fixedBytes4 [0x79, 0x65, 0xdb, 0x0b]
def ierc1155ReceiverId : Expr := fixedBytes4 [0x4e, 0x23, 0x12, 0xe0]
def erc721ReceivedSelector : Expr := fixedBytes4 [0x15, 0x0b, 0x7a, 0x02]
def erc1155ReceivedSelector : Expr := fixedBytes4 [0xf2, 0x3a, 0x6e, 0x61]
def erc1155BatchReceivedSelector : Expr := fixedBytes4 [0xbc, 0x19, 0x7c, 0x81]

def u256 (expr : Expr) : Expr :=
  .inRange uint256Int expr

def localRef (name : Ident) : StorageRef :=
  { base := name }

def lenLocal (name : Ident) : Expr :=
  .arrayLength .localVar (localRef name)

def roleHasRoleRef (role account : Expr) : StorageRef :=
  { base := "_roles", steps := [.mindex role, .field "hasRole", .mindex account] }

def roleAdminRef (role : Expr) : StorageRef :=
  { base := "_roles", steps := [.mindex role, .field "adminRole"] }

def timestampRef (id : Expr) : StorageRef :=
  { base := "_timestamps", steps := [.mindex id] }

def minDelayRef : StorageRef :=
  { base := "_minDelay" }

def roleDataSt : StorageType :=
  .struct "RoleData" [("hasRole", .mapping .address boolSt), ("adminRole", bytes32St)]

def storageDecls : List StorageDecl :=
  [ { name := "_roles", ty := .mapping (.bytes bytes32Width) roleDataSt },
    { name := "_timestamps", ty := .mapping (.bytes bytes32Width) uint256St },
    { name := "_minDelay", ty := uint256St } ]

def roleDataStruct : StructDecl :=
  { name := "RoleData"
    fields :=
      [ { name := "hasRole", ty := .mapping .address boolSt },
        { name := "adminRole", ty := bytes32St } ] }

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def addSlot (slot : Ethereum.UInt256) (offset : Nat) : Ethereum.UInt256 :=
  EVM.word (slot.toNat + offset)

def roleDataSlot (role : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord role) ⟨0⟩

def roleHasRoleSlot (role account : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord account) (roleDataSlot role)

def roleAdminSlot (role : KeyValue) : Ethereum.UInt256 :=
  addSlot (roleDataSlot role) 1

def timestampSlot (id : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord id) ⟨1⟩

def boolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def uint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def bytes32Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .bytes bytes32Width }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_roles", [.mindex role, .field "hasRole", .mindex account] =>
        some (boolLoc (roleHasRoleSlot role account))
    | "_roles", [.mindex role, .field "adminRole"] =>
        some (bytes32Loc (roleAdminSlot role))
    | "_timestamps", [.mindex id] =>
        some (uint256Loc (timestampSlot id))
    | "_minDelay", [] =>
        some (uint256Loc ⟨2⟩)
    | _, _ => none

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def hasRoleExpr (role account : Expr) : Expr :=
  .storage (roleHasRoleRef role account)

def onlyRole (role : Expr) : List Stmt :=
  [ .require (hasRoleExpr role sender) ]

def onlyRoleOrOpenRole (role : Expr) : List Stmt :=
  [ .ite (.unary .not (hasRoleExpr role zeroAddr))
      [ .require (hasRoleExpr role sender) ]
      [] ]

def timestampExpr (id : Expr) : Expr :=
  .storage (timestampRef id)

def isOperationExpr (id : Expr) : Expr :=
  .binary .ne (timestampExpr id) (.intLit 0)

def isOperationPendingExpr (id : Expr) : Expr :=
  .binary .gt (timestampExpr id) doneTimestamp

def isOperationReadyExpr (id : Expr) : Expr :=
  .binary .and
    (isOperationPendingExpr id)
    (.binary .le (timestampExpr id) (.env .timestamp))

def isOperationDoneExpr (id : Expr) : Expr :=
  .binary .eq (timestampExpr id) doneTimestamp

def operationStateExpr (id : Expr) : Expr :=
  .ite (.binary .eq (timestampExpr id) (.intLit 0))
    (.intLit 0)
    (.ite (.binary .eq (timestampExpr id) doneTimestamp)
      (.intLit 3)
      (.ite (.binary .gt (timestampExpr id) (.env .timestamp))
        (.intLit 1)
        (.intLit 2)))

def timelockExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "__abi_encode_hashOperation" then
      ABI.encodeReturnValues? [addr, uint256, bytesTy, bytes32, bytes32] args
    else if name = "__abi_encode_hashOperationBatch" then
      ABI.encodeReturnValues? [addrArray, uint256Array, bytesArray, bytes32, bytes32] args
    else
      none
  decode? := fun _ _ => none

def hashOperationExpr
    (target value data predecessor salt : Expr) : Expr :=
  .keccak256
    (.abiEncodeCall "__abi_encode_hashOperation" [target, value, data, predecessor, salt])

def hashOperationBatchExpr
    (targets values payloads predecessor salt : Expr) : Expr :=
  .keccak256
    (.abiEncodeCall "__abi_encode_hashOperationBatch"
      [targets, values, payloads, predecessor, salt])

def grantRoleIfMissing (role account : Expr) : List Stmt :=
  [ .ite (.unary .not (hasRoleExpr role account))
      [ .assign .storage (roleHasRoleRef role account) (.boolLit true) ]
      [] ]

def revokeRoleIfPresent (role account : Expr) : List Stmt :=
  [ .ite (hasRoleExpr role account)
      [ .assign .storage (roleHasRoleRef role account) (.boolLit false) ]
      [] ]

def scheduleOperation (id delay : Expr) : List Stmt :=
  [ .require (.unary .not (isOperationExpr id)),
    .letDecl "minDelay" (some uint256) (.storage minDelayRef),
    .require (.binary .ge delay (.var "minDelay")),
    .assign .storage (timestampRef id) (u256 (.binary .add (.env .timestamp) delay)) ]

def beforeCall (id predecessor : Expr) : List Stmt :=
  [ .require (isOperationReadyExpr id),
    .ite (.binary .ne predecessor defaultAdminRole)
      [ .require (isOperationDoneExpr predecessor) ]
      [] ]

def afterCall (id : Expr) : List Stmt :=
  [ .require (isOperationReadyExpr id),
    .assign .storage (timestampRef id) doneTimestamp ]

def rawExecute (target value payload : Expr) : List Stmt :=
  [ .lowLevelCall target value payload "success" "returndata",
    .require (.var "success") ]

def defaultAdminRoleTransition : TransitionDecl :=
  { name := "DEFAULT_ADMIN_ROLE"
    params := []
    returnType := [bytes32]
    body := nonpayable ++ [ .return [defaultAdminRole] ] }

def proposerRoleTransition : TransitionDecl :=
  { name := "PROPOSER_ROLE"
    params := []
    returnType := [bytes32]
    body := nonpayable ++ [ .return [proposerRole] ] }

def executorRoleTransition : TransitionDecl :=
  { name := "EXECUTOR_ROLE"
    params := []
    returnType := [bytes32]
    body := nonpayable ++ [ .return [executorRole] ] }

def cancellerRoleTransition : TransitionDecl :=
  { name := "CANCELLER_ROLE"
    params := []
    returnType := [bytes32]
    body := nonpayable ++ [ .return [cancellerRole] ] }

def supportsInterfaceTransition : TransitionDecl :=
  { name := "supportsInterface"
    params := [{ name := "interfaceId", ty := bytes4 }]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ .return [
          (.binary .or
            (.binary .eq (.var "interfaceId") ierc1155ReceiverId)
            (.binary .or
              (.binary .eq (.var "interfaceId") iaccessControlId)
              (.binary .eq (.var "interfaceId") ierc165Id)))] ] }

def hasRoleTransition : TransitionDecl :=
  { name := "hasRole"
    params := [{ name := "role", ty := bytes32 }, { name := "account", ty := addr }]
    returnType := [boolTy]
    body :=
      nonpayable ++
      [ .return [(hasRoleExpr (.var "role") (.var "account"))] ] }

def getRoleAdminTransition : TransitionDecl :=
  { name := "getRoleAdmin"
    params := [{ name := "role", ty := bytes32 }]
    returnType := [bytes32]
    body :=
      nonpayable ++
      [ .return [(.storage (roleAdminRef (.var "role")))] ] }

def grantRoleTransition : TransitionDecl :=
  { name := "grantRole"
    params := [{ name := "role", ty := bytes32 }, { name := "account", ty := addr }]
    returnType := []
    body :=
      nonpayable ++
      [ .letDecl "adminRole" (some bytes32) (.storage (roleAdminRef (.var "role"))),
        .require (hasRoleExpr (.var "adminRole") sender) ] ++
      grantRoleIfMissing (.var "role") (.var "account") }

def revokeRoleTransition : TransitionDecl :=
  { name := "revokeRole"
    params := [{ name := "role", ty := bytes32 }, { name := "account", ty := addr }]
    returnType := []
    body :=
      nonpayable ++
      [ .letDecl "adminRole" (some bytes32) (.storage (roleAdminRef (.var "role"))),
        .require (hasRoleExpr (.var "adminRole") sender) ] ++
      revokeRoleIfPresent (.var "role") (.var "account") }

def renounceRoleTransition : TransitionDecl :=
  { name := "renounceRole"
    params := [{ name := "role", ty := bytes32 }, { name := "callerConfirmation", ty := addr }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq (.var "callerConfirmation") sender) ] ++
      revokeRoleIfPresent (.var "role") (.var "callerConfirmation") }

def isOperationTransition : TransitionDecl :=
  { name := "isOperation"
    params := [{ name := "id", ty := bytes32 }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(isOperationExpr (.var "id"))] ] }

def isOperationPendingTransition : TransitionDecl :=
  { name := "isOperationPending"
    params := [{ name := "id", ty := bytes32 }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(isOperationPendingExpr (.var "id"))] ] }

def isOperationReadyTransition : TransitionDecl :=
  { name := "isOperationReady"
    params := [{ name := "id", ty := bytes32 }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(isOperationReadyExpr (.var "id"))] ] }

def isOperationDoneTransition : TransitionDecl :=
  { name := "isOperationDone"
    params := [{ name := "id", ty := bytes32 }]
    returnType := [boolTy]
    body := nonpayable ++ [ .return [(isOperationDoneExpr (.var "id"))] ] }

def getTimestampTransition : TransitionDecl :=
  { name := "getTimestamp"
    params := [{ name := "id", ty := bytes32 }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [(timestampExpr (.var "id"))] ] }

def getOperationStateTransition : TransitionDecl :=
  { name := "getOperationState"
    params := [{ name := "id", ty := bytes32 }]
    returnType := [uint8]
    body := nonpayable ++ [ .return [(operationStateExpr (.var "id"))] ] }

def getMinDelayTransition : TransitionDecl :=
  { name := "getMinDelay"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.storage minDelayRef)] ] }

def hashOperationTransition : TransitionDecl :=
  { name := "hashOperation"
    params :=
      [ { name := "target", ty := addr },
        { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy },
        { name := "predecessor", ty := bytes32 },
        { name := "salt", ty := bytes32 } ]
    returnType := [bytes32]
    body :=
      nonpayable ++
      [ .return [
          hashOperationExpr (.var "target") (.var "value") (.var "data")
            (.var "predecessor") (.var "salt")] ] }

def hashOperationBatchTransition : TransitionDecl :=
  { name := "hashOperationBatch"
    params :=
      [ { name := "targets", ty := addrArray },
        { name := "values", ty := uint256Array },
        { name := "payloads", ty := bytesArray },
        { name := "predecessor", ty := bytes32 },
        { name := "salt", ty := bytes32 } ]
    returnType := [bytes32]
    body :=
      nonpayable ++
      [ .return [
          hashOperationBatchExpr (.var "targets") (.var "values") (.var "payloads")
            (.var "predecessor") (.var "salt")] ] }

def scheduleTransition : TransitionDecl :=
  { name := "schedule"
    params :=
      [ { name := "target", ty := addr },
        { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy },
        { name := "predecessor", ty := bytes32 },
        { name := "salt", ty := bytes32 },
        { name := "delay", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++
      onlyRole proposerRole ++
      [ .letDecl "id" (some bytes32)
          (hashOperationExpr (.var "target") (.var "value") (.var "data")
            (.var "predecessor") (.var "salt")) ] ++
      scheduleOperation (.var "id") (.var "delay") }

def scheduleBatchTransition : TransitionDecl :=
  { name := "scheduleBatch"
    params :=
      [ { name := "targets", ty := addrArray },
        { name := "values", ty := uint256Array },
        { name := "payloads", ty := bytesArray },
        { name := "predecessor", ty := bytes32 },
        { name := "salt", ty := bytes32 },
        { name := "delay", ty := uint256 } ]
    returnType := []
    body :=
      nonpayable ++
      onlyRole proposerRole ++
      [ .require (.binary .eq (lenLocal "targets") (lenLocal "values")),
        .require (.binary .eq (lenLocal "targets") (lenLocal "payloads")),
        .letDecl "id" (some bytes32)
          (hashOperationBatchExpr (.var "targets") (.var "values") (.var "payloads")
            (.var "predecessor") (.var "salt")) ] ++
      scheduleOperation (.var "id") (.var "delay") }

def cancelTransition : TransitionDecl :=
  { name := "cancel"
    params := [{ name := "id", ty := bytes32 }]
    returnType := []
    body :=
      nonpayable ++
      onlyRole cancellerRole ++
      [ .require (isOperationPendingExpr (.var "id")),
        .delete (timestampRef (.var "id")) ] }

def executeTransition : TransitionDecl :=
  { name := "execute"
    params :=
      [ { name := "target", ty := addr },
        { name := "value", ty := uint256 },
        { name := "payload", ty := bytesTy },
        { name := "predecessor", ty := bytes32 },
        { name := "salt", ty := bytes32 } ]
    returnType := []
    body :=
      onlyRoleOrOpenRole executorRole ++
      [ .letDecl "id" (some bytes32)
          (hashOperationExpr (.var "target") (.var "value") (.var "payload")
            (.var "predecessor") (.var "salt")) ] ++
      beforeCall (.var "id") (.var "predecessor") ++
      rawExecute (.var "target") (.var "value") (.var "payload") ++
      afterCall (.var "id") }

def executeBatchTransition : TransitionDecl :=
  { name := "executeBatch"
    params :=
      [ { name := "targets", ty := addrArray },
        { name := "values", ty := uint256Array },
        { name := "payloads", ty := bytesArray },
        { name := "predecessor", ty := bytes32 },
        { name := "salt", ty := bytes32 } ]
    returnType := []
    body :=
      onlyRoleOrOpenRole executorRole ++
      [ .require (.binary .eq (lenLocal "targets") (lenLocal "values")),
        .require (.binary .eq (lenLocal "targets") (lenLocal "payloads")),
        .letDecl "id" (some bytes32)
          (hashOperationBatchExpr (.var "targets") (.var "values") (.var "payloads")
            (.var "predecessor") (.var "salt")) ] ++
      beforeCall (.var "id") (.var "predecessor") ++
      [ .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (lenLocal "targets"))
          [ .assign .localVar { base := "i" } (u256 (.binary .add (.var "i") (.intLit 1))) ]
          (rawExecute
            (.index (.var "targets") (.var "i"))
            (.index (.var "values") (.var "i"))
            (.index (.var "payloads") (.var "i"))) ] ++
      afterCall (.var "id") }

def updateDelayTransition : TransitionDecl :=
  { name := "updateDelay"
    params := [{ name := "newDelay", ty := uint256 }]
    returnType := []
    body :=
      nonpayable ++
      [ .require (.binary .eq sender thisAddr),
        .assign .storage minDelayRef (.var "newDelay") ] }

def onERC721ReceivedTransition : TransitionDecl :=
  { name := "onERC721Received"
    params :=
      [ { name := "operator", ty := addr },
        { name := "from", ty := addr },
        { name := "tokenId", ty := uint256 },
        { name := "data", ty := bytesTy } ]
    returnType := [bytes4]
    body := nonpayable ++ [ .return [erc721ReceivedSelector] ] }

def onERC1155ReceivedTransition : TransitionDecl :=
  { name := "onERC1155Received"
    params :=
      [ { name := "operator", ty := addr },
        { name := "from", ty := addr },
        { name := "id", ty := uint256 },
        { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy } ]
    returnType := [bytes4]
    body := nonpayable ++ [ .return [erc1155ReceivedSelector] ] }

def onERC1155BatchReceivedTransition : TransitionDecl :=
  { name := "onERC1155BatchReceived"
    params :=
      [ { name := "operator", ty := addr },
        { name := "from", ty := addr },
        { name := "ids", ty := uint256Array },
        { name := "values", ty := uint256Array },
        { name := "data", ty := bytesTy } ]
    returnType := [bytes4]
    body := nonpayable ++ [ .return [erc1155BatchReceivedSelector] ] }

def receiveTransition : TransitionDecl :=
  { name := "receive"
    params := []
    returnType := []
    body := [] }

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      grantRoleIfMissing defaultAdminRole thisAddr ++
      grantRoleIfMissing defaultAdminRole sender ++
      grantRoleIfMissing proposerRole sender ++
      grantRoleIfMissing cancellerRole sender ++
      grantRoleIfMissing executorRole zeroAddr ++
      [ .assign .storage minDelayRef initialMinDelay ] }

def contract : ContractDecl :=
  { name := "TimelockControllerBench"
    storage := storageDecls
    ctor := constructorDecl
    structs := [roleDataStruct]
    transitions :=
      [ cancellerRoleTransition,
        cancelTransition,
        defaultAdminRoleTransition,
        executeBatchTransition,
        executeTransition,
        executorRoleTransition,
        getMinDelayTransition,
        getOperationStateTransition,
        getRoleAdminTransition,
        getTimestampTransition,
        grantRoleTransition,
        hasRoleTransition,
        hashOperationBatchTransition,
        hashOperationTransition,
        isOperationDoneTransition,
        isOperationPendingTransition,
        isOperationReadyTransition,
        isOperationTransition,
        onERC1155BatchReceivedTransition,
        onERC1155ReceivedTransition,
        onERC721ReceivedTransition,
        proposerRoleTransition,
        renounceRoleTransition,
        revokeRoleTransition,
        scheduleBatchTransition,
        scheduleTransition,
        supportsInterfaceTransition,
        updateDelayTransition ]
    receive := some receiveTransition }

def config : Config :=
  { storage := storageLayout
    externalABI := timelockExternalABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end OpenZeppelinBench.TimelockController
