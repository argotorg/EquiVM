import Solm.Semantics
import Solm.SolidityLayout

/-!
# MakerDAO/Sky DSS End benchmark spec

This file is the Solm benchmark entrypoint for upstream `dss/src/end.sol`.
The artifact layer is source-pinned; the transition bodies are added by the DSS spec pass.
-/

open Solm ABI

namespace Benchmarks.Dss.End

def uint256Int : IntType := .uint ⟨256, by decide⟩
def int256Int : IntType := .sint ⟨256, by decide⟩
def uint96Int : IntType := .uint ⟨96, by decide⟩
def uint64Int : IntType := .uint ⟨64, by decide⟩
def uint48Int : IntType := .uint ⟨48, by decide⟩
def uint8Int : IntType := .uint ⟨8, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def int256 : ABIType := .elem (.int int256Int)
def uint96 : ABIType := .elem (.int uint96Int)
def uint64 : ABIType := .elem (.int uint64Int)
def uint48 : ABIType := .elem (.int uint48Int)
def uint8 : ABIType := .elem (.int uint8Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes32 : ABIType := .elem (.bytes bytes32Width)
def bytesDyn : ABIType := .bytes
def uint256Array : ABIType := .dynamicArray (.elem (.int uint256Int))
def addrArray : ABIType := .dynamicArray (.elem .address)

def uint256St : StorageType := .elem (.int uint256Int)
def int256St : StorageType := .elem (.int int256Int)
def uint96St : StorageType := .elem (.int uint96Int)
def uint64St : StorageType := .elem (.int uint64Int)
def uint48St : StorageType := .elem (.int uint48Int)
def addrSt : StorageType := .elem .address
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller

def storageDecls : List StorageDecl := []

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | _, _ => none

def storageLayout : StorageLayout :=
  solidityStorageLayout storageLayoutRaw

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def constructorDecl : ConstructorDecl :=
  { params := []
    body := nonpayable }

def transitions : List TransitionDecl := []

def contract : ContractDecl :=
  { name := "End"
    storage := storageDecls
    ctor := constructorDecl
    transitions := transitions }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Dss.End
