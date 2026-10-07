import Solm.Semantics
import Solm.SolidityLayout
import Solm.MetaSolidityLayout
import Examples.TinyImmutable.Immutables

/-!
# TinyImmutable — a compact immutable-aware Solm specification

The contract has no storage. Its persistent constructor data are two Solidity immutables:
`owner : address` and `scale : uint256`. The constructor always assigns `owner`, but assigns
`scale` only when `useScale` is true; the false path leaves `scale` at Solidity's default `0`,
which is also the value Solm immutables start from.

The public getters return those immutable values. `quote` requires `msg.sender == owner` and returns
`amount * scale` from an `unchecked` Solidity block, so the Solm spec reduces the product modulo
`2^256`, matching EVM `MUL`.
-/

open Solm ABI
open TinyImmutable.Immutables

namespace TinyImmutable

def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def sender : Expr := .env .caller

def wrap256 (e : Expr) : Expr :=
  .binary .mod e (.intLit (Int.ofNat EVM.wordModulus))

/-! ## Constructor and immutable-backed public surface -/

def constructorDecl : ConstructorDecl :=
  { params :=
      [ { name := "_owner", ty := addr },
        { name := "_scale", ty := uint256 },
        { name := "useScale", ty := boolTy } ]
    body :=
      nonpayable ++
      [ .setImmutable "owner" (.var "_owner"),
        .ite (.var "useScale")
          [ .setImmutable "scale" (.var "_scale") ]
          [] ] }

def ownerTransition : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [.immutable "owner"] ] }

def scaleTransition : TransitionDecl :=
  { name := "scale"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [.immutable "scale"] ] }

def quoteTransition : TransitionDecl :=
  { name := "quote"
    params := [{ name := "amount", ty := uint256 }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .require (.binary .eq sender (.immutable "owner")),
        .return [wrap256 (.binary .mul (.var "amount") (.immutable "scale"))] ] }

def transitions : List TransitionDecl :=
  [ ownerTransition,
    quoteTransition,
    scaleTransition ]

def contract : ContractDecl :=
  { name := "TinyImmutable"
    storage := []
    immutables := [⟨"owner", .address⟩, ⟨"scale", .int uint256Int⟩]
    ctor := constructorDecl
    transitions := transitions }

def config : Config :=
  { storageBackend := solidityStorage! [([] : List StructDecl)] [([] : List StorageDecl)]
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end TinyImmutable
