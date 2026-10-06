import Solm.Semantics
import Solm.SolidityLayout
import Solm.SolidityStorage
import Solm.MetaSolidityLayout

/-!
# ERC20 — Solm specification for `ERC20.sol`

This is the Solm-level specification for the core ERC20 surface:
`totalSupply`, `balanceOf`, `allowance`, `approve`, `transfer`, and `transferFrom`.
The Solidity contract emits the standard events, but the current Solm statement tracks storage and
return values only.
-/

open Solm ABI

namespace ERC20

def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)

def uint256Storage : StorageType := .elem (.int uint256Int)

def addr : ABIType := .elem .address

def sender : Expr := .env .caller

def valueInUInt256 (expr : Expr) : Expr := .inRange uint256Int expr

def balanceOfRef (owner : Expr) : StorageRef :=
  { base := "balanceOf", steps := [.mindex owner] }

def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowance", steps := [.mindex owner, .mindex spender] }

def totalSupplyRef : StorageRef :=
  { base := "totalSupply" }

def erc20StorageDecls : List StorageDecl :=
  [ { name := "balanceOf", ty := .mapping .address uint256Storage },
    { name := "allowance", ty := .mapping .address (.mapping .address uint256Storage) },
    { name := "totalSupply", ty := uint256Storage } ]

def erc20Uint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def erc20MappingSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (Ethereum.KEC (key.toByteArray ++ baseSlot.toByteArray))

def erc20BalanceOfSlot (owner : KeyValue) : Ethereum.UInt256 :=
  erc20MappingSlot (keyValueToWord owner) ⟨0⟩

def erc20AllowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  erc20MappingSlot (keyValueToWord owner) ⟨1⟩

def erc20AllowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  erc20MappingSlot (keyValueToWord spender) (erc20AllowanceOwnerSlot owner)

@[simp] theorem erc20BalanceOfSlot_eq (owner : KeyValue) :
    erc20BalanceOfSlot owner = erc20MappingSlot (keyValueToWord owner) ⟨0⟩ :=
  rfl

@[simp] theorem erc20AllowanceOwnerSlot_eq (owner : KeyValue) :
    erc20AllowanceOwnerSlot owner = erc20MappingSlot (keyValueToWord owner) ⟨1⟩ :=
  rfl

@[simp] theorem erc20AllowanceSlot_eq (owner spender : KeyValue) :
    erc20AllowanceSlot owner spender =
      erc20MappingSlot (keyValueToWord spender)
        (erc20MappingSlot (keyValueToWord owner) ⟨1⟩) :=
  rfl

/-!
ERC20's storage declarations are all full-word values, so their Solidity base slots are exactly
their declaration indices: `balanceOf` at slot 0, `allowance` at slot 1, and `totalSupply` at slot 2.
Mapping entries then use Solidity's standard `keccak256(key ++ baseSlot)` slot derivation.
-/
def erc20StorageLayout : StorageLayout :=
  solidityLayout! [([] : List StructDecl)] [erc20StorageDecls]

@[simp] theorem erc20StorageLayout_totalSupply :
    erc20StorageLayout { base := "totalSupply", steps := [] } = fun _ => some (erc20Uint256Loc ⟨2⟩) :=
  rfl

@[simp] theorem erc20StorageLayout_balanceOf (owner : KeyValue) :
    erc20StorageLayout { base := "balanceOf", steps := [.mindex owner] } =
      fun _ => some (erc20Uint256Loc (erc20BalanceOfSlot owner)) :=
  rfl

@[simp] theorem erc20StorageLayout_allowance (owner spender : KeyValue) :
    erc20StorageLayout { base := "allowance", steps := [.mindex owner, .mindex spender] } =
      fun _ => some (erc20Uint256Loc (erc20AllowanceSlot owner spender)) :=
  rfl

@[simp] theorem erc20StorageLayout_balanceOf_missingIndex :
    erc20StorageLayout { base := "balanceOf", steps := [] } = fun _ => none :=
  rfl

@[simp] theorem erc20StorageLayout_allowance_missingSpender (owner : KeyValue) :
    erc20StorageLayout { base := "allowance", steps := [.mindex owner] } = fun _ => none :=
  rfl

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "initialSupply", ty := uint256 }]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (balanceOfRef sender) (.var "initialSupply"),
        .assign .storage totalSupplyRef (.var "initialSupply") ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage totalSupplyRef)] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage (balanceOfRef (.var "owner")))] ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage (allowanceRef (.var "owner") (.var "spender")))] ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "value", ty := uint256 }]
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (allowanceRef sender (.var "spender")) (.var "value"),
        .return [(.boolLit true)] ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "to", ty := addr }, { name := "value", ty := uint256 }]
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign .storage (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return [(.boolLit true)] ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "from", ty := addr }, { name := "to", ty := addr },
      { name := "value", ty := uint256 }]
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
        .require (.binary .ge (.var "currentAllowance") (.var "value")),
        .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (allowanceRef (.var "from") sender)
          (.binary .sub (.var "currentAllowance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (valueInUInt256
            (.binary .sub (.storage (balanceOfRef (.var "from"))) (.var "value"))),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign .storage (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return [(.boolLit true)] ] }

def erc20Contract : ContractDecl :=
  { name := "ERC20"
    storage := erc20StorageDecls
    ctor := constructorDecl
    transitions :=
      [ approveTransition,
        totalSupplyTransition,
        transferFromTransition,
        balanceOfTransition,
        transferTransition,
        allowanceTransition ] }

end ERC20

def erc20Config : Config :=
  { storageBackend := solidityStorageBackend ERC20.erc20StorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment ERC20.erc20Contract.ctor.params }

@[simp] theorem erc20Config_storage_totalSupply {evm : EVM.State} :
    erc20Config.storageBackend.locate? { base := "totalSupply", steps := [] } evm =
      some (ERC20.erc20Uint256Loc ⟨2⟩) :=
  rfl

@[simp] theorem erc20Config_storage_balanceOf (owner : KeyValue) {evm : EVM.State} :
    erc20Config.storageBackend.locate? { base := "balanceOf", steps := [.mindex owner] } evm =
      some (ERC20.erc20Uint256Loc (ERC20.erc20BalanceOfSlot owner)) :=
  rfl

@[simp] theorem erc20Config_storage_allowance (owner spender : KeyValue) {evm : EVM.State} :
    erc20Config.storageBackend.locate? { base := "allowance", steps := [.mindex owner, .mindex spender] } evm =
      some (ERC20.erc20Uint256Loc (ERC20.erc20AllowanceSlot owner spender)) :=
  rfl
