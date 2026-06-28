import Solm.Semantics
import Solm.SolidityLayout

/-!
# WETH9 benchmark spec

Solm benchmark scaffold for the canonical DappHub/Gnosis `WETH9` contract.

The benchmark targets the deployed optimized runtime.  Events are omitted, as in the other examples.
The named ABI surface is explicit.  The Solidity fallback `function() external payable { deposit(); }`
is not represented by `ContractDecl`'s selector-based transition list yet; it should be handled by a
future fallback-dispatch extension or a contract-specific proof harness.

`name` and `symbol` are string getters.  The current storage layout interface cannot describe
Solidity's compact dynamic-string storage location as a `StorageLoc`, so these getters are modelled
as their source literals in this scaffold.  The real source and bytecode remain present.
-/

open Solm ABI

namespace Benchmarks.WETH9

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool

def uint8St : StorageType := .elem (.int uint8Int)
def uint256St : StorageType := .elem (.int uint256Int)

def sender : Expr := .env .caller

def maxUint256 : Int := (2 : Int) ^ 256 - 1

/-! ## Storage references -/

def nameRef : StorageRef := { base := "name" }
def symbolRef : StorageRef := { base := "symbol" }
def decimalsRef : StorageRef := { base := "decimals" }

def balanceOfRef (owner : Expr) : StorageRef :=
  { base := "balanceOf", steps := [.mindex owner] }

def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowance", steps := [.mindex owner, .mindex spender] }

/-! ## Storage declarations and layout -/

def storageDecls : List StorageDecl :=
  [ { name := "name", ty := .string },
    { name := "symbol", ty := .string },
    { name := "decimals", ty := uint8St },
    { name := "balanceOf", ty := .mapping .address uint256St },
    { name := "allowance", ty := .mapping .address (.mapping .address uint256St) } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def balanceOfSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨3⟩

def allowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨4⟩

def allowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord spender) (allowanceOwnerSlot owner)

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def uint8Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .int uint8Int }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "decimals", [] => some (uint8Loc ⟨2⟩)
    | "balanceOf", [.mindex owner] => some (wordLoc (balanceOfSlot owner))
    | "allowance", [.mindex owner, .mindex spender] =>
        some (wordLoc (allowanceSlot owner spender))
    | _, _ => none

/-! ## Shared expressions and source bodies -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def emptyBytes : Expr :=
  .newBytes (.intLit 0)

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      [ .assign .storage decimalsRef (.intLit 18) ] }

/-! ## Public ABI surface -/

def nameTransition : TransitionDecl :=
  { name := "name"
    params := []
    returnType := some .string
    body := nonpayable ++ [ .return (.bytesLit (String.toByteArray "Wrapped Ether")) ] }

def symbolTransition : TransitionDecl :=
  { name := "symbol"
    params := []
    returnType := some .string
    body := nonpayable ++ [ .return (.bytesLit (String.toByteArray "WETH")) ] }

def decimalsTransition : TransitionDecl :=
  { name := "decimals"
    params := []
    returnType := some uint8
    body := nonpayable ++ [ .return (.storage decimalsRef) ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (balanceOfRef (.var "owner"))) ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "guy", ty := addr }]
    returnType := some uint256
    body := nonpayable ++ [ .return (.storage (allowanceRef (.var "owner") (.var "guy"))) ] }

def depositTransition : TransitionDecl :=
  { name := "deposit"
    params := []
    returnType := none
    body :=
      [ .assign .storage (balanceOfRef sender)
          (.binary .add (.storage (balanceOfRef sender)) (.env .callvalue)) ] }

def withdrawTransition : TransitionDecl :=
  { name := "withdraw"
    params := [{ name := "wad", ty := uint256 }]
    returnType := none
    body :=
      nonpayable ++
        [ .require (.binary .ge (.storage (balanceOfRef sender)) (.var "wad")),
          .assign .storage (balanceOfRef sender)
            (.binary .sub (.storage (balanceOfRef sender)) (.var "wad")),
          .lowLevelCall sender (.var "wad") emptyBytes "success" "_data",
          .require (.var "success") ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := some uint256
    body := nonpayable ++ [ .return (.env .selfbalance) ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "guy", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := some boolTy
    body :=
      nonpayable ++
        [ .assign .storage (allowanceRef sender (.var "guy")) (.var "wad"),
          .return (.boolLit true) ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "dst", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := some boolTy
    body :=
      nonpayable ++
        [ .internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok",
          .return (.var "_ok") ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params :=
      [ { name := "src", ty := addr }, { name := "dst", ty := addr },
        { name := "wad", ty := uint256 } ]
    returnType := some boolTy
    body :=
      nonpayable ++
        [ .require (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")),
          .ite
            (.binary .and
              (.binary .ne (.var "src") sender)
              (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)))
            [ .require (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")),
              .assign .storage (allowanceRef (.var "src") sender)
                (.binary .sub (.storage (allowanceRef (.var "src") sender)) (.var "wad")) ]
            [],
          .assign .storage (balanceOfRef (.var "src"))
            (.binary .sub (.storage (balanceOfRef (.var "src"))) (.var "wad")),
          .assign .storage (balanceOfRef (.var "dst"))
            (.binary .add (.storage (balanceOfRef (.var "dst"))) (.var "wad")),
          .return (.boolLit true) ] }

def contract : ContractDecl :=
  { name := "WETH9"
    storage := storageDecls
    ctor := constructorDecl
    functions := []
    transitions :=
      [ nameTransition,
        approveTransition,
        totalSupplyTransition,
        transferFromTransition,
        withdrawTransition,
        decimalsTransition,
        balanceOfTransition,
        symbolTransition,
        transferTransition,
        depositTransition,
        allowanceTransition ] }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.WETH9
