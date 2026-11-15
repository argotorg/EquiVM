import Examples.ERC20.Spec
import Stele.VyperLayout
import Stele.MetaVyperLayout

/-!
# Vyper ERC20 — Stele specification and storage layout

The specification keeps the explicit local bindings used by the Vyper proofs. Its bodies are
independent of the Solidity ERC20 example, while scalar types and storage declarations are shared.
Vyper 0.4.3's `layout` output for `ERC20.vy` is:

* `balanceOf`: slot 0
* `allowance`: slot 1
* `totalSupply`: slot 2

For `HashMap`, Vyper derives entries as `keccak256(baseSlot ++ key)`, unlike Solidity's
`keccak256(key ++ baseSlot)`.
-/

open Stele ABI

namespace VyperERC20

abbrev uint256Int : IntType := ERC20.uint256Int
abbrev uint256 : ABIType := ERC20.uint256
abbrev uint256Storage : StorageType := ERC20.uint256Storage
abbrev addr : ABIType := ERC20.addr

abbrev sender : Expr := ERC20.sender

abbrev balanceOfRef (owner : Expr) : StorageRef :=
  ERC20.balanceOfRef owner

abbrev allowanceRef (owner spender : Expr) : StorageRef :=
  ERC20.allowanceRef owner spender

abbrev totalSupplyRef : StorageRef :=
  ERC20.totalSupplyRef

abbrev erc20StorageDecls : List StorageDecl :=
  ERC20.erc20StorageDecls

-- Keep the existing Vyper specification stable when the Solidity presentation changes.
abbrev valueInUInt256 (expr : Expr) : Expr := ERC20.valueInUInt256 expr

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "initialSupply", ty := uint256 }]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (balanceOfRef sender) (.var "initialSupply"),
        .assign .storage totalSupplyRef (.var "initialSupply") ] }

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
        .emit "Transfer" [sender, .var "to", .var "value"],
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
        .emit "Transfer" [.var "from", .var "to", .var "value"],
        .return [(.boolLit true)] ] }

def erc20Contract : ContractDecl :=
  { name := "ERC20"
    storage := erc20StorageDecls
    ctor := constructorDecl
    transitions :=
      [ ERC20.approveTransition,
        ERC20.totalSupplyTransition,
        transferFromTransition,
        ERC20.balanceOfTransition,
        transferTransition,
        ERC20.allowanceTransition ] }

def erc20BalanceOfSlot (owner : KeyValue) : Ethereum.UInt256 :=
  vyperMappingSlot ⟨0⟩ owner

def erc20AllowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  vyperMappingSlot ⟨1⟩ owner

def erc20AllowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  vyperMappingSlot (erc20AllowanceOwnerSlot owner) spender

def erc20StorageLayout : StorageLayout :=
  vyperLayout! [erc20StorageDecls]

@[simp] theorem erc20BalanceOfSlot_eq (owner : KeyValue) :
    erc20BalanceOfSlot owner = vyperMappingSlot ⟨0⟩ owner :=
  rfl

@[simp] theorem erc20AllowanceOwnerSlot_eq (owner : KeyValue) :
    erc20AllowanceOwnerSlot owner = vyperMappingSlot ⟨1⟩ owner :=
  rfl

@[simp] theorem erc20AllowanceSlot_eq (owner spender : KeyValue) :
    erc20AllowanceSlot owner spender =
      vyperMappingSlot (vyperMappingSlot ⟨1⟩ owner) spender :=
  rfl

@[simp] theorem erc20StorageLayout_totalSupply :
    erc20StorageLayout { base := "totalSupply", steps := [] } =
      some (.leaf (vyperUint256Loc ⟨2⟩)) :=
  rfl

@[simp] theorem erc20StorageLayout_balanceOf (owner : KeyValue) :
    erc20StorageLayout { base := "balanceOf", steps := [.mindex owner] } =
      some (.leaf (vyperUint256Loc (erc20BalanceOfSlot owner))) :=
  rfl

@[simp] theorem erc20StorageLayout_allowance (owner spender : KeyValue) :
    erc20StorageLayout { base := "allowance", steps := [.mindex owner, .mindex spender] } =
      some (.leaf (vyperUint256Loc (erc20AllowanceSlot owner spender))) :=
  rfl

end VyperERC20

/-- The ERC20 leaves are full-word integers in the generated Vyper layout. -/
def vyperERC20Config : Config :=
  { storageBackend := vyperStorageBackend VyperERC20.erc20StorageLayout
      (vyperBounds! [VyperERC20.erc20StorageDecls])
    externalABI := (defaultExternalCallABI).withMode DecodeMode.vyper
    selfDeployment := genSolidityConstructorDeployment VyperERC20.erc20Contract.ctor.params }

@[simp] theorem vyperERC20Config_storage_totalSupply :
    vyperERC20Config.storageBackend.locate? { base := "totalSupply", steps := [] } =
      some (.leaf (vyperUint256Loc ⟨2⟩)) :=
  rfl

@[simp] theorem vyperERC20Config_storage_balanceOf (owner : KeyValue) :
    vyperERC20Config.storageBackend.locate? { base := "balanceOf", steps := [.mindex owner] } =
      some (.leaf (vyperUint256Loc (VyperERC20.erc20BalanceOfSlot owner))) :=
  rfl

@[simp] theorem vyperERC20Config_storage_allowance (owner spender : KeyValue) :
    vyperERC20Config.storageBackend.locate? { base := "allowance", steps := [.mindex owner, .mindex spender] } =
      some (.leaf (vyperUint256Loc (VyperERC20.erc20AllowanceSlot owner spender))) :=
  rfl
