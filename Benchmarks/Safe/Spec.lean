import Solm.Semantics
import Solm.SolidityLayout

/-!
# Safe benchmark spec

Solm benchmark scaffold for upstream `safe-global/safe-smart-account` `Benchmarks/Safe/contracts/Safe.sol`.
The storage declarations and raw storage layout are transcribed from solc's storage-layout output.
Events and fallback/receive dispatch are omitted; the selector-dispatched ABI surface is explicit.

The transition bodies are ABI-shaped proof scaffolds: they enforce nonpayable call-value checks,
return storage-backed values for compiler-visible public state where practical, and otherwise use
zero/default return values until the full source semantics are proved.
-/

open Solm ABI

namespace Benchmarks.Safe

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def stringTy : ABIType := .string

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def addrArrayTy : ABIType := .dynamicArray addr

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def sentinelAddr : Expr := .cast (.intLit 1) addrSt

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
    { name := "approvedHashes", ty := .mapping .address (.mapping (.bytes bytes32Width) uint256St) } ]

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

def loc (slot : Ethereum.UInt256) (offset : Fin 32) (size : Fin 33)
    (hbound : offset.val + size.val - 1 < 32) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := offset, size := size, hbound := hbound, type := ty }

def wordLoc (slot : Ethereum.UInt256) (ty : ElemType) : StorageLoc :=
  loc slot ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide) ty

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  loc slot ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide) .address

/-- Raw storage layout transcribed from `solc --combined-json storage-layout` for `Safe`. -/
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
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

/-! ## Shared source patterns -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

/-! ## Constructor -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body := nonpayable }

/-! ## Public ABI surface -/

def versionTransition : TransitionDecl :=
  { name := "VERSION"
    params := []
    returnType := (some stringTy)
    body := nonpayable ++ [ .return (.bytesLit (String.toByteArray "1.5.0")) ] }

def addownerwiththresholdTransition : TransitionDecl :=
  { name := "addOwnerWithThreshold"
    params := [ { name := "owner", ty := addr }, { name := "_threshold", ty := uint256 } ]
    returnType := none
    body := nonpayable }

def approvehashTransition : TransitionDecl :=
  { name := "approveHash"
    params := [ { name := "hashToApprove", ty := bytes32 } ]
    returnType := none
    body := nonpayable }

def approvedhashesTransition : TransitionDecl :=
  { name := "approvedHashes"
    params := [ { name := "arg0", ty := addr }, { name := "arg1", ty := bytes32 } ]
    returnType := (some uint256)
    body := nonpayable ++ [ .return (.storage (approvedHashesRef (.var "arg0") (.var "arg1"))) ] }

def changethresholdTransition : TransitionDecl :=
  { name := "changeThreshold"
    params := [ { name := "_threshold", ty := uint256 } ]
    returnType := none
    body := nonpayable }

def checknsignaturesTransition : TransitionDecl :=
  { name := "checkNSignatures"
    params := [ { name := "dataHash", ty := bytes32 }, { name := "data", ty := bytesTy }, { name := "signatures", ty := bytesTy }, { name := "requiredSignatures", ty := uint256 } ]
    returnType := none
    body := nonpayable }

def checknsignaturesAddressBytes32BytesUint256Transition : TransitionDecl :=
  { name := "checkNSignatures"
    params := [ { name := "executor", ty := addr }, { name := "dataHash", ty := bytes32 }, { name := "signatures", ty := bytesTy }, { name := "requiredSignatures", ty := uint256 } ]
    returnType := none
    body := nonpayable }

def checksignaturesTransition : TransitionDecl :=
  { name := "checkSignatures"
    params := [ { name := "dataHash", ty := bytes32 }, { name := "data", ty := bytesTy }, { name := "signatures", ty := bytesTy } ]
    returnType := none
    body := nonpayable }

def checksignaturesAddressBytes32BytesTransition : TransitionDecl :=
  { name := "checkSignatures"
    params := [ { name := "executor", ty := addr }, { name := "dataHash", ty := bytes32 }, { name := "signatures", ty := bytesTy } ]
    returnType := none
    body := nonpayable }

def disablemoduleTransition : TransitionDecl :=
  { name := "disableModule"
    params := [ { name := "prevModule", ty := addr }, { name := "module", ty := addr } ]
    returnType := none
    body := nonpayable }

def domainseparatorTransition : TransitionDecl :=
  { name := "domainSeparator"
    params := []
    returnType := (some bytes32)
    body := nonpayable ++ [ .return (.storage deprecatedDomainSeparatorRef) ] }

def enablemoduleTransition : TransitionDecl :=
  { name := "enableModule"
    params := [ { name := "module", ty := addr } ]
    returnType := none
    body := nonpayable }

def exectransactionTransition : TransitionDecl :=
  { name := "execTransaction"
    params := [ { name := "to", ty := addr }, { name := "value", ty := uint256 }, { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 }, { name := "safeTxGas", ty := uint256 }, { name := "baseGas", ty := uint256 }, { name := "gasPrice", ty := uint256 }, { name := "gasToken", ty := addr }, { name := "refundReceiver", ty := addr }, { name := "signatures", ty := bytesTy } ]
    returnType := (some boolTy)
    body := [] ++ [ .return (.boolLit false) ] }

def exectransactionfrommoduleTransition : TransitionDecl :=
  { name := "execTransactionFromModule"
    params := [ { name := "to", ty := addr }, { name := "value", ty := uint256 }, { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 } ]
    returnType := (some boolTy)
    body := nonpayable ++ [ .return (.boolLit false) ] }

def exectransactionfrommodulereturndataTransition : TransitionDecl :=
  { name := "execTransactionFromModuleReturnData"
    params := [ { name := "to", ty := addr }, { name := "value", ty := uint256 }, { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 } ]
    returnType := (some (.tuple [boolTy, bytesTy]))
    body := nonpayable ++ [ .return (.tupleLit [(.boolLit false), (.bytesLit ByteArray.empty)]) ] }

def getmodulespaginatedTransition : TransitionDecl :=
  { name := "getModulesPaginated"
    params := [ { name := "start", ty := addr }, { name := "pageSize", ty := uint256 } ]
    returnType := (some (.tuple [(.dynamicArray addr), addr]))
    body := nonpayable ++ [ .return (.tupleLit [(.arrayLit []), zeroAddr]) ] }

def getownersTransition : TransitionDecl :=
  { name := "getOwners"
    params := []
    returnType := (some (.dynamicArray addr))
    body := nonpayable ++ [ .return (.arrayLit []) ] }

def getstorageatTransition : TransitionDecl :=
  { name := "getStorageAt"
    params := [ { name := "offset", ty := uint256 }, { name := "length", ty := uint256 } ]
    returnType := (some bytesTy)
    body := nonpayable ++ [ .return (.bytesLit ByteArray.empty) ] }

def getthresholdTransition : TransitionDecl :=
  { name := "getThreshold"
    params := []
    returnType := (some uint256)
    body := nonpayable ++ [ .return (.storage thresholdRef) ] }

def gettransactionhashTransition : TransitionDecl :=
  { name := "getTransactionHash"
    params := [ { name := "to", ty := addr }, { name := "value", ty := uint256 }, { name := "data", ty := bytesTy }, { name := "operation", ty := uint8 }, { name := "safeTxGas", ty := uint256 }, { name := "baseGas", ty := uint256 }, { name := "gasPrice", ty := uint256 }, { name := "gasToken", ty := addr }, { name := "refundReceiver", ty := addr }, { name := "_nonce", ty := uint256 } ]
    returnType := (some bytes32)
    body := nonpayable ++ [ .return (.fixedBytesLit ⟨31, by decide⟩ (List.replicate 32 (0 : UInt8))) ] }

def ismoduleenabledTransition : TransitionDecl :=
  { name := "isModuleEnabled"
    params := [ { name := "module", ty := addr } ]
    returnType := (some boolTy)
    body := nonpayable ++ [ .return (.binary .and (.binary .ne (.storage (modulesRef (.var "module"))) zeroAddr) (.binary .ne (.var "module") sentinelAddr)) ] }

def isownerTransition : TransitionDecl :=
  { name := "isOwner"
    params := [ { name := "owner", ty := addr } ]
    returnType := (some boolTy)
    body := nonpayable ++ [ .return (.binary .and (.binary .ne (.storage (ownersRef (.var "owner"))) zeroAddr) (.binary .ne (.var "owner") sentinelAddr)) ] }

def nonceTransition : TransitionDecl :=
  { name := "nonce"
    params := []
    returnType := (some uint256)
    body := nonpayable ++ [ .return (.storage nonceRef) ] }

def removeownerTransition : TransitionDecl :=
  { name := "removeOwner"
    params := [ { name := "prevOwner", ty := addr }, { name := "owner", ty := addr }, { name := "_threshold", ty := uint256 } ]
    returnType := none
    body := nonpayable }

def setfallbackhandlerTransition : TransitionDecl :=
  { name := "setFallbackHandler"
    params := [ { name := "handler", ty := addr } ]
    returnType := none
    body := nonpayable }

def setguardTransition : TransitionDecl :=
  { name := "setGuard"
    params := [ { name := "guard", ty := addr } ]
    returnType := none
    body := nonpayable }

def setmoduleguardTransition : TransitionDecl :=
  { name := "setModuleGuard"
    params := [ { name := "moduleGuard", ty := addr } ]
    returnType := none
    body := nonpayable }

def setupTransition : TransitionDecl :=
  { name := "setup"
    params := [ { name := "_owners", ty := (.dynamicArray addr) }, { name := "_threshold", ty := uint256 }, { name := "to", ty := addr }, { name := "data", ty := bytesTy }, { name := "fallbackHandler", ty := addr }, { name := "paymentToken", ty := addr }, { name := "payment", ty := uint256 }, { name := "paymentReceiver", ty := addr } ]
    returnType := none
    body := nonpayable }

def signedmessagesTransition : TransitionDecl :=
  { name := "signedMessages"
    params := [ { name := "arg0", ty := bytes32 } ]
    returnType := (some uint256)
    body := nonpayable ++ [ .return (.storage (signedMessagesRef (.var "arg0"))) ] }

def simulateandrevertTransition : TransitionDecl :=
  { name := "simulateAndRevert"
    params := [ { name := "targetContract", ty := addr }, { name := "calldataPayload", ty := bytesTy } ]
    returnType := none
    body := nonpayable }

def swapownerTransition : TransitionDecl :=
  { name := "swapOwner"
    params := [ { name := "prevOwner", ty := addr }, { name := "oldOwner", ty := addr }, { name := "newOwner", ty := addr } ]
    returnType := none
    body := nonpayable }

def transitions : List TransitionDecl :=
  [
        versionTransition,
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
    functions := []
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Safe
