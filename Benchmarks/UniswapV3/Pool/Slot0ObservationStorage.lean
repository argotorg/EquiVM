import Benchmarks.UniswapV3.Pool.MaskedUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def slot0ObservationName (cardinality : Bool) : Ident :=
  if cardinality then "observationCardinality" else "observationIndex"

def slot0ObservationLoc (cardinality : Bool) : StorageLoc :=
  {slot := ⟨0⟩, offset := if cardinality then 25 else 23, size := 2,
    type := .int (.uint ⟨16, by decide⟩), hbound := by cases cardinality <;> decide}

def slot0ObservationWord (old value : UInt256) (cardinality : Bool) : UInt256 :=
  packedFieldUpdate old value (if cardinality then 200 else 184) 16

def storeSlot0ObservationField (evm : EVM.State) (cardinality : Bool) (value : UInt256) : EVM.State :=
  modifyStorageWord evm ⟨0⟩ (fun old ↦ slot0ObservationWord old value cardinality)

theorem slot0ObservationWord_evm (old value : UInt256) (cardinality : Bool) :
    slot0ObservationWord old value cardinality =
      UInt256.lor
        (UInt256.mul (UInt256.land (UInt256.ofNat 65535) value)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat (if cardinality then 200 else 184))))
        (UInt256.land
          (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535)
            (UInt256.ofNat (if cardinality then 200 else 184)))) old) := by
  have hmask : packedFieldMask (if cardinality then 200 else 184) 16 =
      UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535)
        (UInt256.ofNat (if cardinality then 200 else 184))) := by
    cases cardinality <;> native_decide
  have hshift : UInt256.ofNat (2 ^ (if cardinality then 200 else 184)) =
      UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat (if cardinality then 200 else 184)) := by
    cases cardinality <;> native_decide
  simp only [slot0ObservationWord, packedFieldUpdate, packedFieldValue, hmask, hshift,
    show UInt256.ofNat (2 ^ 16 - 1) = UInt256.ofNat 65535 from rfl]
  rw [u256_lor_comm, u256_land_comm old, u256_land_comm value]

theorem storageLocStore_slot0ObservationField (evm : EVM.State) (cardinality : Bool)
    (value : UInt256) :
    storageLocStore evm (slot0ObservationLoc cardinality) (.int (Int.ofNat value.toNat)) =
      some (storeSlot0ObservationField evm cardinality value) := by
  have h := storageLocStore_packedValue evm (slot0ObservationLoc cardinality)
    (.int (Int.ofNat value.toNat)) value (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
  cases cardinality <;> exact h

theorem assignSlot0ObservationField (evm : EVM.State) (locals imms : Store) (cardinality : Bool)
    (value : UInt256) (hbase : locals.get? "slot0" = none) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"slot0", [.field (slot0ObservationName cardinality)]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        storeSlot0ObservationField evm cardinality value) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨16, by decide⟩)))
    (er := ⟨"slot0", [.field (slot0ObservationName cardinality)]⟩)
    (loc := slot0ObservationLoc cardinality) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bind, EvalResult.bind, pure])
    (by cases cardinality <;> rfl) poolStorageBackend_eq (by cases cardinality <;> rfl)
    (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_slot0ObservationField evm cardinality value

theorem slot0ObservationWords_comm (old index cardinality : UInt256) :
    slot0ObservationWord (slot0ObservationWord old index false) cardinality true =
      slot0ObservationWord (slot0ObservationWord old cardinality true) index false := by
  apply wordMaskedUpdate_comm
  · exact wordMask_preserves_of_contains _ _ _
      (packedFieldValue_mask index 184 16 (by decide) (by decide)) (by native_decide)
  · exact wordMask_preserves_of_contains _ _ _
      (packedFieldValue_mask cardinality 200 16 (by decide) (by decide)) (by native_decide)

theorem storeSlot0ObservationPair_eq (evm : EVM.State) (index cardinality : UInt256) :
    storeSlot0ObservationField (storeSlot0ObservationField evm false index) true cardinality =
      modifyStorageWord evm ⟨0⟩
        (fun old ↦ slot0ObservationWord (slot0ObservationWord old cardinality true) index false) := by
  unfold storeSlot0ObservationField
  rw [modifyStorageWord_comp]
  congr 1
  funext old
  exact slot0ObservationWords_comm old index cardinality

end Benchmarks.UniswapV3.Pool
