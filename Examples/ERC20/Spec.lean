import Solm.Semantics
import Solm.SolidityLayout

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

def erc20StorageLayout : StorageLayout where
  layout :=
    match genSolidityLayout [] erc20StorageDecls with
    | some layout => layout
    | none => fun _ => none

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "initialSupply", ty := uint256 }]
    body :=
      [ .assign (balanceOfRef sender) (.var "initialSupply"),
        .assign totalSupplyRef (.var "initialSupply") ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage totalSupplyRef) ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (balanceOfRef (.var "owner"))) ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (allowanceRef (.var "owner") (.var "spender"))) ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "value", ty := uint256 }]
    returnType := some (.elem .bool)
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign (allowanceRef sender (.var "spender")) (.var "value"),
        .return (.boolLit true) ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "to", ty := addr }, { name := "value", ty := uint256 }]
    returnType := some (.elem .bool)
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return (.boolLit true) ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "from", ty := addr }, { name := "to", ty := addr },
      { name := "value", ty := uint256 }]
    returnType := some (.elem .bool)
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
        .require (.binary .ge (.var "currentAllowance") (.var "value")),
        .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign (allowanceRef (.var "from") sender)
          (.binary .sub (.var "currentAllowance") (.var "value")),
        .assign (balanceOfRef (.var "from")) (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return (.boolLit true) ] }

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
  { storage := ERC20.erc20StorageLayout
    externalABI := defaultExternalCallABI }
