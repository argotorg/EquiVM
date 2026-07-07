import Solm.Semantics
import Solm.SolidityLayout
import Benchmarks.WETH9.StringLayout

/-!
# WETH9 benchmark spec

Solm benchmark scaffold for the canonical DappHub/Gnosis `WETH9` contract.

The benchmark targets the deployed optimized runtime.  Events are omitted, as in the other examples.
The named ABI surface is explicit, and the payable Solidity fallback is modeled as the deposit body.

`name` and `symbol` are Solidity compact dynamic-string storage values initialized by the creation
bytecode and read by the deployed runtime getters.
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
def stringTy : ABIType := .string

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

def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "name", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨0⟩ evm)
  | { base := "symbol", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨1⟩ evm)
  | { base := "decimals", steps := [] }, _ => some (uint8Loc ⟨2⟩)
  | { base := "balanceOf", steps := [.mindex owner] }, _ =>
      some (wordLoc (balanceOfSlot owner))
  | { base := "allowance", steps := [.mindex owner, .mindex spender] }, _ =>
      some (wordLoc (allowanceSlot owner spender))
  | _, _ => none

-- solc 0.5.16 compact-string semantics (total header decode + unconditional data-word clear on
-- write) differ from the shared ≥0.8-faithful `solidityStorageLayout` defaults; see StringLayout.lean.
def storageLayout : StorageLayout :=
  weth9StorageLayout storageLayoutRaw

/-! ## Shared expressions and source bodies -/

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def emptyBytes : Expr :=
  .newBytes (.intLit 0)

-- WETH9.sol has no explicit constructor, so solc 0.5.16 emits a non-payable implicit one: the
-- creation bytecode reverts on nonzero `msg.value` (creation.hex pc 105–115) before the field inits.
def constructorDecl : ConstructorDecl :=
  { params := []
    body := nonpayable ++
      [ .assign .storage nameRef (.bytesLit (String.toByteArray "Wrapped Ether")),
        .assign .storage symbolRef (.bytesLit (String.toByteArray "WETH")),
        .assign .storage decimalsRef (.intLit 18) ] }

/-! ## Public ABI surface -/

def nameTransition : TransitionDecl :=
  { name := "name"
    params := []
    returnType := [stringTy]
    body := nonpayable ++ [ .return [.storage nameRef] ] }

def symbolTransition : TransitionDecl :=
  { name := "symbol"
    params := []
    returnType := [stringTy]
    body := nonpayable ++ [ .return [.storage symbolRef] ] }

def decimalsTransition : TransitionDecl :=
  { name := "decimals"
    params := []
    returnType := [uint8]
    body := nonpayable ++ [ .return [.storage decimalsRef] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (balanceOfRef (.var "owner"))] ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "guy", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [.storage (allowanceRef (.var "owner") (.var "guy"))] ] }

def depositTransition : TransitionDecl :=
  { name := "deposit"
    params := []
    returnType := []
    body :=
      [ .assign .storage (balanceOfRef sender)
          (.binary .add (.storage (balanceOfRef sender)) (.env .callvalue)) ] }

def fallbackTransition : TransitionDecl :=
  { name := "fallback"
    params := []
    returnType := []
    body := depositTransition.body }

def withdrawTransition : TransitionDecl :=
  { name := "withdraw"
    params := [{ name := "wad", ty := uint256 }]
    returnType := []
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
    returnType := [uint256]
    body := nonpayable ++ [ .return [.env .selfbalance] ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "guy", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := [boolTy]
    body :=
      nonpayable ++
        [ .assign .storage (allowanceRef sender (.var "guy")) (.var "wad"),
          .return [.boolLit true] ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "dst", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := [boolTy]
    body :=
      nonpayable ++
        [ .internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok",
          .return [.var "_ok"] ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params :=
      [ { name := "src", ty := addr }, { name := "dst", ty := addr },
        { name := "wad", ty := uint256 } ]
    returnType := [boolTy]
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
          .return [.boolLit true] ] }

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
        allowanceTransition ]
    fallback := some fallbackTransition }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.legacySolc05
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.WETH9
