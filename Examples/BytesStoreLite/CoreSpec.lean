import Solm.Semantics
import Solm.SolidityLayout

/-!
# BytesStoreLiteCore — bytes storage equivalence target

This is the `bytes` analogue of `StringStoreLite`: one dynamic byte array in slot 0 with
whole-value set, clear, and length getter transitions.  The larger `BytesStoreLite.Spec` remains
the storage-layout exercise for byte indexing, arrays, structs, and mappings.
-/

open Solm ABI Ethereum

namespace BytesStoreLiteCore

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def bytesTy : ABIType := .bytes

def uint8St : StorageType := .elem (.int uint8Int)
def bytesSt : StorageType := .bytes

/-! ## Storage refs -/

def currentRef : StorageRef := { base := "current" }

def currentByteRef (i : Expr) : StorageRef := { base := "current", steps := [.aindex i] }

def storageDecls : List StorageDecl :=
  [ { name := "current", ty := bytesSt } ]

/-! ## Transitions -/

def setTransition : TransitionDecl :=
  { name := "set"
    params := [{ name := "value", ty := bytesTy }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some bytesTy) (.var "value"),
        .assign .storage currentRef (.var "copy"),
        .return (.arrayLength .localVar { base := "copy" }) ] }

def clearCurrentTransition : TransitionDecl :=
  { name := "clearCurrent"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some bytesTy) (.storage currentRef),
        .delete currentRef,
        .return (.arrayLength .localVar { base := "copy" }) ] }

def currentLengthGetter : TransitionDecl :=
  { name := "currentLength"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage currentRef) ] }

def bytesStoreLiteCoreContract : ContractDecl :=
  { name := "BytesStoreLiteCore"
    storage := storageDecls
    ctor := { params := [], body := [] }
    transitions := [setTransition, clearCurrentTransition, currentLengthGetter] }

/-! ## Solidity bytes storage layout -/

def uint8Loc (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int uint8Int }

def bytesLikeDataBase (baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC baseSlot.toByteArray)

abbrev bytesLikeLengthLoc := Solm.bytesLikeLengthLoc

def bytesLikeByteLoc? (baseSlot : Ethereum.UInt256) (index : KeyValue)
    (evm : EVM.State) : Option StorageLoc :=
  match index with
  | .int i =>
      if i < 0 then
        none
      else
        let idx := i.toNat
        if checkBytesPacked baseSlot evm then
          if hidx : idx < 31 then
            some (uint8Loc baseSlot ⟨31 - idx, by omega⟩)
          else
            none
        else
          some (uint8Loc
            (bytesLikeDataBase baseSlot + Ethereum.UInt256.ofNat (idx / 32))
            ⟨31 - (idx % 32), by
              have hmod : idx % 32 < 32 := Nat.mod_lt idx (by decide)
              omega⟩)
  | _ => none

def bytesStoreLiteCoreLayout : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "current", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨0⟩ evm)
  | { base := "current", steps := [.aindex i] }, evm => bytesLikeByteLoc? ⟨0⟩ i evm
  | _, _ => none

def bytesStoreLiteCoreStorageLayout : StorageLayout :=
  solidityStorageLayout bytesStoreLiteCoreLayout

end BytesStoreLiteCore

def bytesStoreLiteCoreConfig : Config :=
  { storage := BytesStoreLiteCore.bytesStoreLiteCoreStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment BytesStoreLiteCore.bytesStoreLiteCoreContract.ctor.params }

@[simp] theorem bytesStoreLiteCoreConfig_storage_current_length :
    bytesStoreLiteCoreConfig.storage.layout { base := "current", steps := [.length] } =
      fun evm => some (BytesStoreLiteCore.bytesLikeLengthLoc ⟨0⟩ evm) :=
  rfl
