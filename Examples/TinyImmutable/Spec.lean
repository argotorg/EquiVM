import Solm.Semantics
import Solm.SolidityLayout
import Examples.TinyImmutable.Immutables

/-!
# TinyImmutable — a compact immutable-aware Solm specification

The contract has no storage. Its persistent constructor data are two Solidity immutables:
`owner : address` and `scale : uint256`. The constructor always assigns `owner`, but assigns
`scale` only when `useScale` is true; the false path leaves `scale` at Solidity's default `0`.

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
      [ .letDecl "imm_owner" (some addr) (.var "_owner"),
        .ite (.var "useScale")
          [ .letDecl "imm_scale" (some uint256) (.var "_scale") ]
          [ .letDecl "imm_scale" (some uint256) (.intLit 0) ] ] }

def ownerTransition (v : TinyImmutables) : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := [addr]
    body := nonpayable ++ [ .return [owner v] ] }

def scaleTransition (v : TinyImmutables) : TransitionDecl :=
  { name := "scale"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [scale v] ] }

def quoteTransition (v : TinyImmutables) : TransitionDecl :=
  { name := "quote"
    params := [{ name := "amount", ty := uint256 }]
    returnType := [uint256]
    body :=
      nonpayable ++
      [ .require (.binary .eq sender (owner v)),
        .return [wrap256 (.binary .mul (.var "amount") (scale v))] ] }

def transitions (v : TinyImmutables) : List TransitionDecl :=
  [ ownerTransition v,
    quoteTransition v,
    scaleTransition v ]

def contract (v : TinyImmutables) : ContractDecl :=
  { name := "TinyImmutable"
    storage := []
    ctor := constructorDecl
    transitions := transitions v }

def config (v : TinyImmutables) : Config :=
  { storage := { layout := fun _ _ => none }
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment (contract v).ctor.params }

end TinyImmutable
