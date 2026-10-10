import Benchmarks.UniswapV3.Pool.Slot0ObservationStorage
import Benchmarks.UniswapV3.Pool.SourceFrame
import Benchmarks.UniswapV3.Pool.Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapSlotFieldName (tick : Bool) : Ident := if tick then "tick" else "sqrtPriceX96"

def swapSlotFieldLoc (tick : Bool) : StorageLoc :=
  {slot := ⟨0⟩, offset := if tick then 20 else 0, size := if tick then 3 else 20
   type := .int (if tick then .sint ⟨24, by decide⟩ else .uint ⟨160, by decide⟩)
   hbound := by cases tick <;> decide}

def swapSlotFieldWord (old value : UInt256) (tick : Bool) : UInt256 :=
  packedFieldUpdate old value (if tick then 160 else 0) (if tick then 24 else 160)

def swapSlotFieldState (evm : EVM.State) (tick : Bool) (value : UInt256) : EVM.State :=
  modifyStorageWord evm ⟨0⟩ (fun old ↦ swapSlotFieldWord old value tick)

theorem storageLocStore_swapSlotField (evm : EVM.State) (tick : Bool) (value : Int) :
    storageLocStore evm (swapSlotFieldLoc tick) (.int value) =
      some (swapSlotFieldState evm tick (EVM.wordOfInt value)) := by
  have h := storageLocStore_packedValue evm (swapSlotFieldLoc tick) (.int value)
    (EVM.wordOfInt value) rfl rfl
  cases tick <;> exact h

theorem assignSwapSlotField (evm : EVM.State) (locals imms : Store) (tick : Bool)
    (value : Int) (hbase : locals.get? "slot0" = none) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage ⟨"slot0", [.field (swapSlotFieldName tick)]⟩ (.int value) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        swapSlotFieldState evm tick (EVM.wordOfInt value)) := by
  apply assignStorageRef_storage_scalar_value
    (ty := .elem (.int (if tick then .sint ⟨24, by decide⟩ else .uint ⟨160, by decide⟩)))
    (er := ⟨"slot0", [.field (swapSlotFieldName tick)]⟩) (loc := swapSlotFieldLoc tick) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bind, EvalResult.bind, pure])
    (by cases tick <;> rfl) poolStorageBackend_eq (by cases tick <;> rfl)
    (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_swapSlotField evm tick value

theorem assignSwapSlotField_frame {frame : Frame} (evm : EVM.State) (tick : Bool)
    (value : Int) (hf : frame.contract = contract) (hbase : frame.locals.get? "slot0" = none) :
    assignStorageRef? config frame evm .storage ⟨"slot0", [.field (swapSlotFieldName tick)]⟩
      (.int value) = .ok (frame, swapSlotFieldState evm tick (EVM.wordOfInt value)) := by
  have h := assignSwapSlotField evm frame.locals frame.immutables tick value hbase
  rw [← frame_eq_of_parts hf rfl] at h
  exact h

theorem assignSlot0ObservationField_frame {frame : Frame} (evm : EVM.State)
    (cardinality : Bool) (value : UInt256)
    (hf : frame.contract = contract) (hbase : frame.locals.get? "slot0" = none) :
    assignStorageRef? config frame evm .storage
      ⟨"slot0", [.field (slot0ObservationName cardinality)]⟩ (.int (Int.ofNat value.toNat)) =
      .ok (frame, storeSlot0ObservationField evm cardinality value) := by
  have h := assignSlot0ObservationField evm frame.locals frame.immutables cardinality value hbase
  rw [← frame_eq_of_parts hf rfl] at h
  exact h

theorem SourceState.swapSlotField {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (tick : Bool) (value : UInt256) :
    SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ ⟨0⟩ (swapSlotFieldWord (solcSlotWordAt ⟨0⟩ σ ee) value tick))
      (swapSlotFieldState evm tick value) := by
  simpa only [swapSlotFieldState, modifyStorageWord, hs.env, solcSlotWordAt] using
    hs.readModifyWrite ⟨0⟩ (fun old ↦ swapSlotFieldWord old value tick)

def swapSlotFieldsWord (old price tick index cardinality : UInt256) : UInt256 :=
  slot0ObservationWord
    (slot0ObservationWord (swapSlotFieldWord (swapSlotFieldWord old price false) tick true)
      index false) cardinality true

def swapSlotFieldsState (evm : EVM.State) (price tick index cardinality : UInt256) : EVM.State :=
  storeSlot0ObservationField
    (storeSlot0ObservationField
      (swapSlotFieldState (swapSlotFieldState evm false price) true tick) false index)
    true cardinality

theorem swapSlotFieldsState_eq (evm : EVM.State) (price tick index cardinality : UInt256) :
    swapSlotFieldsState evm price tick index cardinality =
      modifyStorageWord evm ⟨0⟩ (fun old ↦ swapSlotFieldsWord old price tick index cardinality) :=
        by
  simp only [swapSlotFieldsState, storeSlot0ObservationField, swapSlotFieldState,
    modifyStorageWord_comp]
  rfl

theorem SourceState.swapSlotFields {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (price tick index cardinality : UInt256) :
    SourceState s0 ee (sstoreAccountMap ee.codeOwner σ ⟨0⟩
      (swapSlotFieldsWord (solcSlotWordAt ⟨0⟩ σ ee) price tick index cardinality))
      (swapSlotFieldsState evm price tick index cardinality) := by
  rw [swapSlotFieldsState_eq]
  simpa only [modifyStorageWord, hs.env, solcSlotWordAt] using
    hs.readModifyWrite ⟨0⟩ (fun old ↦ swapSlotFieldsWord old price tick index cardinality)

end Benchmarks.UniswapV3.Pool
