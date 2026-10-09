import Benchmarks.CompoundIII.Comet.LiquidatorPoints
import Benchmarks.CompoundIII.Comet.AggregateStorage
import Benchmarks.CompoundIII.Comet.UserBasicLocal
import Benchmarks.CompoundIII.Comet.PackedStateWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

structure LiquidatorPointsData where
  absorbs : UInt256
  absorbed : UInt256
  spend : UInt256
  reserved : UInt256

def liquidatorPointsData (word : UInt256) : LiquidatorPointsData :=
  ⟨liquidatorFieldWord word 0, liquidatorFieldWord word 1,
    liquidatorFieldWord word 2, liquidatorFieldWord word 3⟩

def liquidatorPointsField (p : LiquidatorPointsData) (i : Fin 4) : UInt256 :=
  match i.val with
  | 0 => p.absorbs
  | 1 => p.absorbed
  | 2 => p.spend
  | _ => p.reserved

def liquidatorPointsSet (p : LiquidatorPointsData) (i : Fin 4) (word : UInt256) :
    LiquidatorPointsData :=
  match i.val with
  | 0 => { p with absorbs := word }
  | 1 => { p with absorbed := word }
  | 2 => { p with spend := word }
  | _ => { p with reserved := word }

theorem liquidatorPointsData_field (word : UInt256) (i : Fin 4) :
    liquidatorPointsField (liquidatorPointsData word) i = liquidatorFieldWord word i := by
  fin_cases i <;> rfl

theorem liquidatorPointsData_bound (word : UInt256) (i : Fin 4) :
    (liquidatorPointsField (liquidatorPointsData word) i).toNat <
      2 ^ (liquidatorFieldWidth i).val := by
  rw [liquidatorPointsData_field]
  exact packedUint_lt word _ (by fin_cases i <;> decide)

def liquidatorPointsTypes : List (Ident × StorageType) :=
  [("numAbsorbs", .elem (.int (.uint ⟨32, by decide⟩))),
    ("numAbsorbed", .elem (.int (.uint ⟨64, by decide⟩))),
    ("approxSpend", .elem (.int (.uint ⟨128, by decide⟩))),
    ("_reserved", .elem (.int (.uint ⟨32, by decide⟩)))]

def liquidatorPointsType : StorageType := .struct "LiquidatorPoints" liquidatorPointsTypes

def liquidatorPointsValue (p : LiquidatorPointsData) : Value :=
  .struct "LiquidatorPoints"
    [("numAbsorbs", .int p.absorbs.toNat), ("numAbsorbed", .int p.absorbed.toNat),
      ("approxSpend", .int p.spend.toNat), ("_reserved", .int p.reserved.toNat)]

theorem readLiquidatorPointsField (evm : State) (addr : AccountAddress) (i : Fin 4) :
    config.storageBackend.read
      ⟨"liquidatorPoints", [.mindex (.address addr), .field (liquidatorFieldName i)]⟩
      (.elem (.int (.uint (liquidatorFieldWidth i)))) evm =
    .ok (.int (liquidatorFieldWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liquidatorSlot addr)) i).toNat) := by
  rw [readStorage?_elem (hbackend := rfl)
    (loc := {
      slot := liquidatorSlot addr, offset := liquidatorFieldOffset i,
      size := liquidatorFieldSize i, hbound := by fin_cases i <;> decide,
      type := .int (.uint (liquidatorFieldWidth i)) })
    (by fin_cases i <;> simp only [liquidatorSlot, liquidatorFieldName,
      liquidatorFieldOffset, liquidatorFieldSize, liquidatorFieldWidth, solcMappingSlot,
      keyValueToWord_address] <;> rfl)]
  rw [packedUint_load evm (liquidatorSlot addr) (liquidatorFieldOffset i)
    (liquidatorFieldSize i) (liquidatorFieldWidth i) rfl]
  rfl

theorem readLiquidatorPoints (evm : State) (addr : AccountAddress) :
    config.storageBackend.read ⟨"liquidatorPoints", [.mindex (.address addr)]⟩
      liquidatorPointsType evm =
    .ok (liquidatorPointsValue (liquidatorPointsData
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liquidatorSlot addr)))) := by
  change solidityReadStorage? config.storageBackend.locate? evm _ _ = _
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liquidatorSlot addr)
  have hf := solidityReadFields_from_fields config.storageBackend.locate? evm
    ⟨"liquidatorPoints", [.mindex (.address addr)]⟩ liquidatorPointsTypes
    [("numAbsorbs", .int (liquidatorFieldWord w 0).toNat),
      ("numAbsorbed", .int (liquidatorFieldWord w 1).toNat),
      ("approxSpend", .int (liquidatorFieldWord w 2).toNat),
      ("_reserved", .int (liquidatorFieldWord w 3).toNat)]
    (.cons ⟨rfl, readLiquidatorPointsField evm addr 0⟩
      (.cons ⟨rfl, readLiquidatorPointsField evm addr 1⟩
        (.cons ⟨rfl, readLiquidatorPointsField evm addr 2⟩
          (.cons ⟨rfl, readLiquidatorPointsField evm addr 3⟩ .nil))))
  simp only [liquidatorPointsType, solidityReadStorage?, hf, bind, EvalResult.bind, pure]
  rfl

theorem evalLiquidatorPoints (frame : Frame) (evm : State) (addr : AccountAddress)
    (arg : Expr) (hc : frame.contract = contract)
    (hlocal : frame.locals.get? "liquidatorPoints" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address addr)) :
    evalExpr? config frame evm (.storage ⟨"liquidatorPoints", [.mindex arg]⟩) =
    .ok (liquidatorPointsValue (liquidatorPointsData
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liquidatorSlot addr)))) := by
  apply evalExpr_storage_typed hlocal
    (er := ⟨"liquidatorPoints", [.mindex (.address addr)]⟩) (ty := liquidatorPointsType)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact readLiquidatorPoints evm addr

def storeLiquidatorPoints (evm : State) (addr : AccountAddress) (p : LiquidatorPointsData) :
    State :=
  let evm := storePackedWord evm (liquidatorSlot addr) p.absorbs 0 4
  let evm := storePackedWord evm (liquidatorSlot addr) p.absorbed 4 8
  let evm := storePackedWord evm (liquidatorSlot addr) p.spend 12 16
  storePackedWord evm (liquidatorSlot addr) p.reserved 28 4

theorem writeLiquidatorPointsField (evm : State) (addr : AccountAddress) (i : Fin 4)
    (word : UInt256) :
    config.storageBackend.write
      ⟨"liquidatorPoints", [.mindex (.address addr), .field (liquidatorFieldName i)]⟩
      (.elem (.int (.uint (liquidatorFieldWidth i)))) (.int word.toNat) evm =
    .ok (storePackedWord evm (liquidatorSlot addr) word
      (liquidatorFieldOffset i).val (liquidatorFieldSize i).val) := by
  apply solidityStorageBackend_write_elem _ _ _ _ _ _
    { slot := liquidatorSlot addr, offset := liquidatorFieldOffset i,
      size := liquidatorFieldSize i, hbound := by fin_cases i <;> decide,
      type := .int (.uint (liquidatorFieldWidth i)) }
  · fin_cases i <;> simp only [liquidatorSlot, liquidatorFieldName, liquidatorFieldOffset,
      liquidatorFieldSize, liquidatorFieldWidth, solcMappingSlot, keyValueToWord_address] <;> rfl
  · exact storageLocStore_packed_int evm _ word _ _ _

theorem writeLiquidatorPoints (evm : State) (addr : AccountAddress) (p : LiquidatorPointsData) :
    config.storageBackend.write ⟨"liquidatorPoints", [.mindex (.address addr)]⟩
      liquidatorPointsType (liquidatorPointsValue p) evm =
    .ok (storeLiquidatorPoints evm addr p) := by
  change solidityWriteStorage? config.storageBackend.locate? evm _ _ _ = _
  rw [liquidatorPointsType, liquidatorPointsValue, solidityWriteStorage?, if_pos rfl]
  apply solidityWriteFields_cons
  · exact writeLiquidatorPointsField evm addr 0 p.absorbs
  apply solidityWriteFields_cons
  · exact writeLiquidatorPointsField _ addr 1 p.absorbed
  apply solidityWriteFields_cons
  · exact writeLiquidatorPointsField _ addr 2 p.spend
  apply solidityWriteFields_cons
  · exact writeLiquidatorPointsField _ addr 3 p.reserved
  simp only [solidityWriteFields?]
  rfl

theorem assignLiquidatorPoints (frame : Frame) (evm : State) (addr : AccountAddress)
    (arg : Expr) (p : LiquidatorPointsData) (hc : frame.contract = contract)
    (hlocal : frame.locals.get? "liquidatorPoints" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address addr)) :
    assignStorageRef? config frame evm .storage ⟨"liquidatorPoints", [.mindex arg]⟩
      (liquidatorPointsValue p) = .ok (frame, storeLiquidatorPoints evm addr p) := by
  apply assignStorageRef_storage_typed hlocal
    (er := ⟨"liquidatorPoints", [.mindex (.address addr)]⟩) (ty := liquidatorPointsType)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact writeLiquidatorPoints evm addr p

theorem evalLiquidatorPointsLocalField {cfg frame evm expr p}
    (i : Fin 4) (he : evalExpr? cfg frame evm expr = .ok (liquidatorPointsValue p)) :
    evalExpr? cfg frame evm (.field expr (liquidatorFieldName i)) =
    .ok (.int (liquidatorPointsField p i).toNat) := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  fin_cases i <;> rfl

theorem assignLiquidatorPointsLocalField {cfg frame evm name p}
    (i : Fin 4) (next : UInt256)
    (hget : frame.locals.get? name = some (liquidatorPointsValue p)) :
    assignStorageRef? cfg frame evm .localVar ⟨name, [.field (liquidatorFieldName i)]⟩
      (.int next.toNat) =
    .ok ({ frame with
      locals := frame.locals.insert name (liquidatorPointsValue (liquidatorPointsSet p i next)) },
      evm) := by
  apply assignLocalPath_frame hget
  fin_cases i <;>
    simp only [updateLocalPath?, liquidatorPointsValue, liquidatorFieldName, liquidatorPointsSet,
      lookupField?, lookupAssoc, updateField?, updateAssoc, EvalResult.ofOption,
      bind, EvalResult.bind, pure] <;> rfl

end Benchmarks.CompoundIII.Comet
