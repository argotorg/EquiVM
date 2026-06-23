import Solm.Semantics
import Solm.SolidityLayout

/-!
# OpenZeppelin ERC6909 benchmark spec

Solm specification for the public ERC-6909 surface implemented by OpenZeppelin.  Events and custom
error payloads are omitted; storage effects, allowance rules, and return values are modelled.
-/

open Solm ABI

namespace OpenZeppelinBench.ERC6909

def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes4Width : Fin 32 := ⟨3, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes4 : ABIType := .elem (.bytes bytes4Width)

def uint256St : StorageType := .elem (.int uint256Int)
def boolSt : StorageType := .elem .bool
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt
def maxUint256 : Int := (2 : Int) ^ 256 - 1
def maxUint256Lit : Expr := .intLit maxUint256
def ierc165Id : Expr := .fixedBytesLit bytes4Width [0x01, 0xff, 0xc9, 0xa7]
def ierc6909Id : Expr := .fixedBytesLit bytes4Width [0x0f, 0x63, 0x2f, 0xb3]

def valueInUInt256 (expr : Expr) : Expr := .inRange uint256Int expr

def balanceRef (owner id : Expr) : StorageRef :=
  { base := "_balances", steps := [.mindex owner, .mindex id] }

def operatorApprovalRef (owner spender : Expr) : StorageRef :=
  { base := "_operatorApprovals", steps := [.mindex owner, .mindex spender] }

def allowanceRef (owner spender id : Expr) : StorageRef :=
  { base := "_allowances", steps := [.mindex owner, .mindex spender, .mindex id] }

def storageDecls : List StorageDecl :=
  [ { name := "_balances", ty := .mapping .address (.mapping (.int uint256Int) uint256St) },
    { name := "_operatorApprovals", ty := .mapping .address (.mapping .address boolSt) },
    { name := "_allowances",
      ty := .mapping .address (.mapping .address (.mapping (.int uint256Int) uint256St)) } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def balanceSlot (owner id : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord id) (mapSlot (keyValueToWord owner) ⟨0⟩)

def operatorApprovalSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord spender) (mapSlot (keyValueToWord owner) ⟨1⟩)

def allowanceSlot (owner spender id : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord id)
    (mapSlot (keyValueToWord spender) (mapSlot (keyValueToWord owner) ⟨2⟩))

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def boolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_balances", [.mindex owner, .mindex id] =>
        some (wordLoc (balanceSlot owner id))
    | "_operatorApprovals", [.mindex owner, .mindex spender] =>
        some (boolLoc (operatorApprovalSlot owner spender))
    | "_allowances", [.mindex owner, .mindex spender, .mindex id] =>
        some (wordLoc (allowanceSlot owner spender id))
    | _, _ => none

def supportsInterfaceTransition : TransitionDecl :=
  { name := "supportsInterface"
    params := [{ name := "interfaceId", ty := bytes4 }]
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return
          (.binary .or
            (.binary .eq (.var "interfaceId") ierc6909Id)
            (.binary .eq (.var "interfaceId") ierc165Id)) ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }, { name := "id", ty := uint256 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (balanceRef (.var "owner") (.var "id"))) ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr },
      { name := "id", ty := uint256 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (allowanceRef (.var "owner") (.var "spender") (.var "id"))) ] }

def isOperatorTransition : TransitionDecl :=
  { name := "isOperator"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (operatorApprovalRef (.var "owner") (.var "spender"))) ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "id", ty := uint256 },
      { name := "amount", ty := uint256 }]
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .ne sender zeroAddr),
        .require (.binary .ne (.var "spender") zeroAddr),
        .assign .storage (allowanceRef sender (.var "spender") (.var "id")) (.var "amount"),
        .return (.boolLit true) ] }

def setOperatorTransition : TransitionDecl :=
  { name := "setOperator"
    params := [{ name := "spender", ty := addr }, { name := "approved", ty := boolTy }]
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .ne sender zeroAddr),
        .require (.binary .ne (.var "spender") zeroAddr),
        .assign .storage (operatorApprovalRef sender (.var "spender")) (.var "approved"),
        .return (.boolLit true) ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "receiver", ty := addr }, { name := "id", ty := uint256 },
      { name := "amount", ty := uint256 }]
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .ne sender zeroAddr),
        .require (.binary .ne (.var "receiver") zeroAddr),
        .letDecl "fromBalance" (some uint256) (.storage (balanceRef sender (.var "id"))),
        .require (.binary .ge (.var "fromBalance") (.var "amount")),
        .assign .storage (balanceRef sender (.var "id"))
          (.binary .sub (.var "fromBalance") (.var "amount")),
        .letDecl "toBalance" (some uint256) (.storage (balanceRef (.var "receiver") (.var "id"))),
        .assign .storage (balanceRef (.var "receiver") (.var "id"))
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))),
        .return (.boolLit true) ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "sender", ty := addr }, { name := "receiver", ty := addr },
      { name := "id", ty := uint256 }, { name := "amount", ty := uint256 }]
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .ite
          (.binary .and
            (.binary .ne (.var "sender") sender)
            (.unary .not (.storage (operatorApprovalRef (.var "sender") sender))))
          [ .letDecl "currentAllowance" (some uint256)
              (.storage (allowanceRef (.var "sender") sender (.var "id"))),
            .ite (.binary .lt (.var "currentAllowance") maxUint256Lit)
              [ .require (.binary .ge (.var "currentAllowance") (.var "amount")),
                .assign .storage (allowanceRef (.var "sender") sender (.var "id"))
                  (.binary .sub (.var "currentAllowance") (.var "amount")) ]
              [] ]
          [],
        .require (.binary .ne (.var "sender") zeroAddr),
        .require (.binary .ne (.var "receiver") zeroAddr),
        .letDecl "fromBalance" (some uint256)
          (.storage (balanceRef (.var "sender") (.var "id"))),
        .require (.binary .ge (.var "fromBalance") (.var "amount")),
        .assign .storage (balanceRef (.var "sender") (.var "id"))
          (.binary .sub (.var "fromBalance") (.var "amount")),
        .letDecl "toBalance" (some uint256)
          (.storage (balanceRef (.var "receiver") (.var "id"))),
        .assign .storage (balanceRef (.var "receiver") (.var "id"))
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))),
        .return (.boolLit true) ] }

def constructorDecl : ConstructorDecl :=
  { params := []
    body := [] }

def contract : ContractDecl :=
  { name := "ERC6909Bench"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ allowanceTransition,
        approveTransition,
        balanceOfTransition,
        isOperatorTransition,
        setOperatorTransition,
        supportsInterfaceTransition,
        transferTransition,
        transferFromTransition ] }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end OpenZeppelinBench.ERC6909
