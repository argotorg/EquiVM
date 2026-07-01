import Solm.Semantics
import Solm.SolidityLayout

/-!
# Gnosis MultiSigWallet benchmark spec

Solm benchmark scaffold for the upstream `gnosis/MultiSigWallet` contract.

Events are omitted.  The payable fallback is modeled as the source-level no-op on storage; its
`Deposit` event is ignored by the current equivalence.  The `Transaction.data` field is a dynamic
`bytes` value stored with Solidity's compact bytes layout.
-/

open Solm ABI

namespace Benchmarks.GnosisMultiSig

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def addrArrayTy : ABIType := .dynamicArray addr
def uintArrayTy : ABIType := .dynamicArray uint256

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool
def bytesSt : StorageType := .bytes

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def maxOwnerCount : Int := 50

def u256 (e : Expr) : Expr := .inRange uint256Int e

def localRef (name : Ident) : StorageRef := { base := name }

def and3 (a b c : Expr) : Expr :=
  .binary .and (.binary .and a b) c

def and4 (a b c d : Expr) : Expr :=
  .binary .and (and3 a b c) d

def validRequirementExpr (ownerCount required : Expr) : Expr :=
  and4
    (.binary .le ownerCount (.intLit maxOwnerCount))
    (.binary .le required ownerCount)
    (.binary .ne required (.intLit 0))
    (.binary .ne ownerCount (.intLit 0))

/-! ## Storage references -/

def transactionsRef (transactionId : Expr) : StorageRef :=
  { base := "transactions", steps := [.mindex transactionId] }

def txnF (transactionId : Expr) (field : Ident) : StorageRef :=
  { base := "transactions", steps := [.mindex transactionId, .field field] }

def aliasF (name : Ident) (field : Ident) : StorageRef :=
  { base := name, steps := [.field field] }

def confirmationsRef (transactionId owner : Expr) : StorageRef :=
  { base := "confirmations", steps := [.mindex transactionId, .mindex owner] }

def isOwnerRef (owner : Expr) : StorageRef :=
  { base := "isOwner", steps := [.mindex owner] }

def ownersRef : StorageRef := { base := "owners" }

def ownerAtRef (index : Expr) : StorageRef :=
  { base := "owners", steps := [.aindex index] }

def requiredRef : StorageRef := { base := "required" }
def transactionCountRef : StorageRef := { base := "transactionCount" }

/-! ## Storage declarations and layout -/

def transactionStructTy : StorageType :=
  .struct "Transaction"
    [ ("destination", addrSt), ("value", uint256St), ("data", bytesSt),
      ("executed", boolSt) ]

def transactionStructDecl : StructDecl :=
  { name := "Transaction"
    fields :=
      [ { name := "destination", ty := addrSt },
        { name := "value", ty := uint256St },
        { name := "data", ty := bytesSt },
        { name := "executed", ty := boolSt } ] }

def storageDecls : List StorageDecl :=
  [ { name := "transactions", ty := .mapping (.int uint256Int) transactionStructTy },
    { name := "confirmations", ty := .mapping (.int uint256Int) (.mapping .address boolSt) },
    { name := "isOwner", ty := .mapping .address boolSt },
    { name := "owners", ty := .dynamicArray addrSt },
    { name := "required", ty := uint256St },
    { name := "transactionCount", ty := uint256St } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def transactionsBase (transactionId : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord transactionId) ⟨0⟩

def transactionDataSlot (transactionId : KeyValue) : Ethereum.UInt256 :=
  transactionsBase transactionId + ⟨2⟩

def confirmationsBase (transactionId : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord transactionId) ⟨1⟩

def confirmationsSlot (transactionId owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) (confirmationsBase transactionId)

def isOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨2⟩

def ownersDataBase : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (Ethereum.UInt256.toByteArray ⟨3⟩))

def ownerElemSlot (index : KeyValue) : Ethereum.UInt256 :=
  ownersDataBase + Ethereum.UInt256.ofNat (keyValueToWord index).toNat

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def boolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "transactions", steps := [.mindex transactionId, .field "destination"] }, _ =>
      some (addrLoc (transactionsBase transactionId))
  | { base := "transactions", steps := [.mindex transactionId, .field "value"] }, _ =>
      some (wordLoc (transactionsBase transactionId + ⟨1⟩))
  | { base := "transactions", steps := [.mindex transactionId, .field "data", .length] }, evm =>
      some (bytesLikeLengthLoc (transactionDataSlot transactionId) evm)
  | { base := "transactions", steps := [.mindex transactionId, .field "executed"] }, _ =>
      some (boolLoc (transactionsBase transactionId + ⟨3⟩))
  | { base := "confirmations", steps := [.mindex transactionId, .mindex owner] }, _ =>
      some (boolLoc (confirmationsSlot transactionId owner))
  | { base := "isOwner", steps := [.mindex owner] }, _ =>
      some (boolLoc (isOwnerSlot owner))
  | { base := "owners", steps := [.length] }, _ =>
      some (wordLoc ⟨3⟩)
  | { base := "owners", steps := [.aindex index] }, _ =>
      some (addrLoc (ownerElemSlot index))
  | { base := "required", steps := [] }, _ =>
      some (wordLoc ⟨4⟩)
  | { base := "transactionCount", steps := [] }, _ =>
      some (wordLoc ⟨5⟩)
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def onlyWallet : List Stmt :=
  [ .require (.binary .eq sender thisAddr) ]

def ownerExists (owner : Expr) : List Stmt :=
  [ .require (.storage (isOwnerRef owner)) ]

def ownerDoesNotExist (owner : Expr) : List Stmt :=
  [ .require (.unary .not (.storage (isOwnerRef owner))) ]

def transactionExists (transactionId : Expr) : List Stmt :=
  [ .require (.binary .ne (.storage (txnF transactionId "destination")) zeroAddr) ]

def confirmed (transactionId owner : Expr) : List Stmt :=
  [ .require (.storage (confirmationsRef transactionId owner)) ]

def notConfirmed (transactionId owner : Expr) : List Stmt :=
  [ .require (.unary .not (.storage (confirmationsRef transactionId owner))) ]

def notExecuted (transactionId : Expr) : List Stmt :=
  [ .require (.unary .not (.storage (txnF transactionId "executed"))) ]

def notNull (address : Expr) : List Stmt :=
  [ .require (.binary .ne address zeroAddr) ]

def requireValidRequirement (ownerCount required : Expr) : List Stmt :=
  [ .require (validRequirementExpr ownerCount required) ]

def fallbackTransition : TransitionDecl :=
  { name := "fallback"
    params := []
    returnType := none
    body := [] }

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "_owners", ty := addrArrayTy }, { name := "_required", ty := uint256 }]
    body :=
      nonpayable ++
      requireValidRequirement (.arrayLength .localVar { base := "_owners" }) (.var "_required") ++
      [ .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.arrayLength .localVar { base := "_owners" }))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .letDecl "owner" (some addr) (.index (.var "_owners") (.var "i")),
            .require (.binary .and
              (.unary .not (.storage (isOwnerRef (.var "owner"))))
              (.binary .ne (.var "owner") zeroAddr)),
            .assign .storage (isOwnerRef (.var "owner")) (.boolLit true) ],
        .assign .storage ownersRef (.var "_owners"),
        .assign .storage requiredRef (.var "_required") ] }

/-! ## Internal helpers -/

def addTransactionFn : FunctionDecl :=
  { name := "addTransaction"
    params :=
      [ { name := "destination", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy } ]
    returnType := some uint256
    body :=
      notNull (.var "destination") ++
      [ .letDecl "transactionId" (some uint256) (.storage transactionCountRef),
        .assign .storage (txnF (.var "transactionId") "destination") (.var "destination"),
        .assign .storage (txnF (.var "transactionId") "value") (.var "value"),
        .assign .storage (txnF (.var "transactionId") "data") (.var "data"),
        .assign .storage (txnF (.var "transactionId") "executed") (.boolLit false),
        .assign .storage transactionCountRef
          (u256 (.binary .add (.storage transactionCountRef) (.intLit 1))),
        .return (.var "transactionId") ] }

def externalCallFn : FunctionDecl :=
  { name := "external_call"
    params :=
      [ { name := "destination", ty := addr }, { name := "value", ty := uint256 },
        { name := "dataLength", ty := uint256 }, { name := "data", ty := bytesTy } ]
    returnType := some boolTy
    body :=
      [ .lowLevelCall (.var "destination") (.var "value") (.var "data") "result" "_returndata",
        .return (.var "result") ] }

/-! ## Public transitions -/

def maxOwnerCountTransition : TransitionDecl :=
  { name := "MAX_OWNER_COUNT"
    params := []
    returnType := some uint256
    body := nonpayable ++ [ .return (.intLit maxOwnerCount) ] }

def ownersTransition : TransitionDecl :=
  { name := "owners"
    params := [{ name := "index", ty := uint256 }]
    returnType := some addr
    body := nonpayable ++ [ .return (.storage (ownerAtRef (.var "index"))) ] }

def isOwnerTransition : TransitionDecl :=
  { name := "isOwner"
    params := [{ name := "owner", ty := addr }]
    returnType := some boolTy
    body := nonpayable ++ [ .return (.storage (isOwnerRef (.var "owner"))) ] }

def confirmationsTransition : TransitionDecl :=
  { name := "confirmations"
    params := [{ name := "transactionId", ty := uint256 }, { name := "owner", ty := addr }]
    returnType := some boolTy
    body :=
      nonpayable ++
      [ .return (.storage (confirmationsRef (.var "transactionId") (.var "owner"))) ] }

def transactionsTransition : TransitionDecl :=
  { name := "transactions"
    params := [{ name := "transactionId", ty := uint256 }]
    returnType := some (.tuple [addr, uint256, bytesTy, boolTy])
    body :=
      nonpayable ++
      [ .return (.tupleLit
          [ .storage (txnF (.var "transactionId") "destination"),
            .storage (txnF (.var "transactionId") "value"),
            .storage (txnF (.var "transactionId") "data"),
            .storage (txnF (.var "transactionId") "executed") ]) ] }

def requiredTransition : TransitionDecl :=
  { name := "required"
    params := []
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage requiredRef) ] }

def transactionCountTransition : TransitionDecl :=
  { name := "transactionCount"
    params := []
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage transactionCountRef) ] }

def addOwnerTransition : TransitionDecl :=
  { name := "addOwner"
    params := [{ name := "owner", ty := addr }]
    returnType := none
    body :=
      nonpayable ++ onlyWallet ++ ownerDoesNotExist (.var "owner") ++ notNull (.var "owner") ++
      requireValidRequirement
        (u256 (.binary .add (.arrayLength .storage ownersRef) (.intLit 1)))
        (.storage requiredRef) ++
      [ .assign .storage (isOwnerRef (.var "owner")) (.boolLit true),
        .push ownersRef (some (.var "owner")) ] }

def removeOwnerTransition : TransitionDecl :=
  { name := "removeOwner"
    params := [{ name := "owner", ty := addr }]
    returnType := none
    body :=
      nonpayable ++ onlyWallet ++ ownerExists (.var "owner") ++
      [ .assign .storage (isOwnerRef (.var "owner")) (.boolLit false),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i")
            (u256 (.binary .sub (.arrayLength .storage ownersRef) (.intLit 1))))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .ite (.binary .eq (.storage (ownerAtRef (.var "i"))) (.var "owner"))
              [ .assign .storage (ownerAtRef (.var "i"))
                  (.storage (ownerAtRef
                    (u256 (.binary .sub (.arrayLength .storage ownersRef) (.intLit 1))))),
                .break ]
              [] ],
        .pop ownersRef,
        .ite (.binary .gt (.storage requiredRef) (.arrayLength .storage ownersRef))
          [ .internalCall "changeRequirement" [ .arrayLength .storage ownersRef ] "_unit" ]
          [] ] }

def replaceOwnerTransition : TransitionDecl :=
  { name := "replaceOwner"
    params := [{ name := "owner", ty := addr }, { name := "newOwner", ty := addr }]
    returnType := none
    body :=
      nonpayable ++ onlyWallet ++ ownerExists (.var "owner") ++
      ownerDoesNotExist (.var "newOwner") ++
      [ .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.arrayLength .storage ownersRef))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .ite (.binary .eq (.storage (ownerAtRef (.var "i"))) (.var "owner"))
              [ .assign .storage (ownerAtRef (.var "i")) (.var "newOwner"), .break ]
              [] ],
        .assign .storage (isOwnerRef (.var "owner")) (.boolLit false),
        .assign .storage (isOwnerRef (.var "newOwner")) (.boolLit true) ] }

def changeRequirementTransition : TransitionDecl :=
  { name := "changeRequirement"
    params := [{ name := "_required", ty := uint256 }]
    returnType := none
    body :=
      nonpayable ++ onlyWallet ++
      requireValidRequirement (.arrayLength .storage ownersRef) (.var "_required") ++
      [ .assign .storage requiredRef (.var "_required") ] }

def submitTransactionTransition : TransitionDecl :=
  { name := "submitTransaction"
    params :=
      [ { name := "destination", ty := addr }, { name := "value", ty := uint256 },
        { name := "data", ty := bytesTy } ]
    returnType := some uint256
    body :=
      nonpayable ++
      [ .internalCall "addTransaction" [ .var "destination", .var "value", .var "data" ]
          "transactionId",
        .internalCall "confirmTransaction" [ .var "transactionId" ] "_unit",
        .return (.var "transactionId") ] }

def confirmTransactionTransition : TransitionDecl :=
  { name := "confirmTransaction"
    params := [{ name := "transactionId", ty := uint256 }]
    returnType := none
    body :=
      nonpayable ++ ownerExists sender ++ transactionExists (.var "transactionId") ++
      notConfirmed (.var "transactionId") sender ++
      [ .assign .storage (confirmationsRef (.var "transactionId") sender) (.boolLit true),
        .internalCall "executeTransaction" [ .var "transactionId" ] "_unit" ] }

def revokeConfirmationTransition : TransitionDecl :=
  { name := "revokeConfirmation"
    params := [{ name := "transactionId", ty := uint256 }]
    returnType := none
    body :=
      nonpayable ++ ownerExists sender ++ confirmed (.var "transactionId") sender ++
      notExecuted (.var "transactionId") ++
      [ .assign .storage (confirmationsRef (.var "transactionId") sender) (.boolLit false) ] }

def executeTransactionTransition : TransitionDecl :=
  { name := "executeTransaction"
    params := [{ name := "transactionId", ty := uint256 }]
    returnType := none
    body :=
      nonpayable ++ ownerExists sender ++ confirmed (.var "transactionId") sender ++
      notExecuted (.var "transactionId") ++
      [ .internalCall "isConfirmed" [ .var "transactionId" ] "confirmed_",
        .ite (.var "confirmed_")
          [ .letStorage "txn" (transactionsRef (.var "transactionId")),
            .assign .storage (aliasF "txn" "executed") (.boolLit true),
            .internalCall "external_call"
              [ .storage (aliasF "txn" "destination"), .storage (aliasF "txn" "value"),
                .intLit 0, .storage (aliasF "txn" "data") ]
              "success",
            .ite (.var "success")
              []
              [ .assign .storage (aliasF "txn" "executed") (.boolLit false) ] ]
          [] ] }

def isConfirmedTransition : TransitionDecl :=
  { name := "isConfirmed"
    params := [{ name := "transactionId", ty := uint256 }]
    returnType := some boolTy
    body :=
      nonpayable ++
      [ .letDecl "count" (some uint256) (.intLit 0),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.arrayLength .storage ownersRef))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .ite
              (.storage (confirmationsRef (.var "transactionId") (.storage (ownerAtRef (.var "i")))))
              [ .assign .localVar (localRef "count")
                  (u256 (.binary .add (.var "count") (.intLit 1))) ]
              [],
            .ite (.binary .eq (.var "count") (.storage requiredRef))
              [ .return (.boolLit true) ]
              [] ],
        .return (.boolLit false) ] }

def getConfirmationCountTransition : TransitionDecl :=
  { name := "getConfirmationCount"
    params := [{ name := "transactionId", ty := uint256 }]
    returnType := some uint256
    body :=
      nonpayable ++
      [ .letDecl "count" (some uint256) (.intLit 0),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.arrayLength .storage ownersRef))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .ite
              (.storage (confirmationsRef (.var "transactionId") (.storage (ownerAtRef (.var "i")))))
              [ .assign .localVar (localRef "count")
                  (u256 (.binary .add (.var "count") (.intLit 1))) ]
              [] ],
        .return (.var "count") ] }

def getTransactionCountTransition : TransitionDecl :=
  { name := "getTransactionCount"
    params := [{ name := "pending", ty := boolTy }, { name := "executed", ty := boolTy }]
    returnType := some uint256
    body :=
      nonpayable ++
      [ .letDecl "count" (some uint256) (.intLit 0),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.storage transactionCountRef))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .ite
              (.binary .or
                (.binary .and (.var "pending")
                  (.unary .not (.storage (txnF (.var "i") "executed"))))
                (.binary .and (.var "executed") (.storage (txnF (.var "i") "executed"))))
              [ .assign .localVar (localRef "count")
                  (u256 (.binary .add (.var "count") (.intLit 1))) ]
              [] ],
        .return (.var "count") ] }

def getOwnersTransition : TransitionDecl :=
  { name := "getOwners"
    params := []
    returnType := some addrArrayTy
    body := nonpayable ++ [ .return (.storage ownersRef) ] }

def getConfirmationsTransition : TransitionDecl :=
  { name := "getConfirmations"
    params := [{ name := "transactionId", ty := uint256 }]
    returnType := some addrArrayTy
    body :=
      nonpayable ++
      [ .letDecl "confirmationsTemp" (some addrArrayTy)
          (.newArray addrSt (.arrayLength .storage ownersRef)),
        .letDecl "count" (some uint256) (.intLit 0),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.arrayLength .storage ownersRef))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .ite
              (.storage (confirmationsRef (.var "transactionId") (.storage (ownerAtRef (.var "i")))))
              [ .assign .localVar
                  { base := "confirmationsTemp", steps := [.aindex (.var "count")] }
                  (.storage (ownerAtRef (.var "i"))),
                .assign .localVar (localRef "count")
                  (u256 (.binary .add (.var "count") (.intLit 1))) ]
              [] ],
        .letDecl "_confirmations" (some addrArrayTy) (.newArray addrSt (.var "count")),
        .for
          [ .assign .localVar (localRef "i") (.intLit 0) ]
          (.binary .lt (.var "i") (.var "count"))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .assign .localVar { base := "_confirmations", steps := [.aindex (.var "i")] }
              (.index (.var "confirmationsTemp") (.var "i")) ],
        .return (.var "_confirmations") ] }

def getTransactionIdsTransition : TransitionDecl :=
  { name := "getTransactionIds"
    params :=
      [ { name := "from", ty := uint256 }, { name := "to", ty := uint256 },
        { name := "pending", ty := boolTy }, { name := "executed", ty := boolTy } ]
    returnType := some uintArrayTy
    body :=
      nonpayable ++
      [ .letDecl "transactionIdsTemp" (some uintArrayTy)
          (.newArray uint256St (.storage transactionCountRef)),
        .letDecl "count" (some uint256) (.intLit 0),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.storage transactionCountRef))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .ite
              (.binary .or
                (.binary .and (.var "pending")
                  (.unary .not (.storage (txnF (.var "i") "executed"))))
                (.binary .and (.var "executed") (.storage (txnF (.var "i") "executed"))))
              [ .assign .localVar { base := "transactionIdsTemp", steps := [.aindex (.var "count")] }
                  (.var "i"),
                .assign .localVar (localRef "count")
                  (u256 (.binary .add (.var "count") (.intLit 1))) ]
              [] ],
        .letDecl "_transactionIds" (some uintArrayTy)
          (.newArray uint256St (u256 (.binary .sub (.var "to") (.var "from")))),
        .for
          [ .assign .localVar (localRef "i") (.var "from") ]
          (.binary .lt (.var "i") (.var "to"))
          [ .assign .localVar (localRef "i") (u256 (.binary .add (.var "i") (.intLit 1))) ]
          [ .assign .localVar
              { base := "_transactionIds",
                steps := [.aindex (u256 (.binary .sub (.var "i") (.var "from")))] }
              (.index (.var "transactionIdsTemp") (.var "i")) ],
        .return (.var "_transactionIds") ] }

def functions : List FunctionDecl :=
  [ addTransactionFn, externalCallFn ]

def transitions : List TransitionDecl :=
  [ ownersTransition,
    removeOwnerTransition,
    revokeConfirmationTransition,
    isOwnerTransition,
    confirmationsTransition,
    getTransactionCountTransition,
    addOwnerTransition,
    isConfirmedTransition,
    getConfirmationCountTransition,
    transactionsTransition,
    getOwnersTransition,
    getTransactionIdsTransition,
    getConfirmationsTransition,
    transactionCountTransition,
    changeRequirementTransition,
    confirmTransactionTransition,
    submitTransactionTransition,
    maxOwnerCountTransition,
    requiredTransition,
    replaceOwnerTransition,
    executeTransactionTransition ]

def contract : ContractDecl :=
  { name := "MultiSigWallet"
    storage := storageDecls
    ctor := constructorDecl
    structs := [transactionStructDecl]
    functions := functions
    transitions := transitions
    fallback := some fallbackTransition }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.GnosisMultiSig
