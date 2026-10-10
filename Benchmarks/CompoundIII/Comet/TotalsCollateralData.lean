import Benchmarks.CompoundIII.Comet.CollateralStorage
import Benchmarks.CompoundIII.Comet.AggregateStorage
import Benchmarks.CompoundIII.Comet.UserBasicLocal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def totalsCollateralTypes : List (Ident × StorageType) :=
  [("totalSupplyAsset", .elem (.int (.uint ⟨128, by decide⟩))),
    ("_reserved", .elem (.int (.uint ⟨128, by decide⟩)))]

def totalsCollateralType : StorageType := .struct "TotalsCollateral" totalsCollateralTypes

def totalsCollateralValue (total reserved : UInt256) : Value :=
  .struct "TotalsCollateral"
    [("totalSupplyAsset", .int total.toNat), ("_reserved", .int reserved.toNat)]

def storeTotalsCollateral (evm : EVM.State) (asset : AccountAddress)
    (total reserved : UInt256) : EVM.State :=
  storePackedWord (storePackedWord evm (totalsCollateralSlot asset) total 0 16)
    (totalsCollateralSlot asset) reserved 16 16

theorem readTotalsCollateralField (evm : EVM.State) (asset : AccountAddress) (upper : Bool) :
    config.storageBackend.read
      ⟨"totalsCollateral", [.mindex (.address asset),
        .field (if upper then "_reserved" else "totalSupplyAsset")]⟩
      (.elem (.int (.uint ⟨128, by decide⟩))) evm =
    .ok (.int ((if upper then high128 else low128)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset))).toNat) := by
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true]
  · rw [readStorage?_elem (hbackend := rfl)
      (loc := {
        slot := totalsCollateralSlot asset, offset := 0, size := ⟨16, by decide⟩,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      (by simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]; rfl)]
    rw [low128_load]
  · rw [readStorage?_elem (hbackend := rfl)
      (loc := {
        slot := totalsCollateralSlot asset, offset := ⟨16, by decide⟩, size := ⟨16, by decide⟩,
        hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      (by simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]; rfl)]
    rw [high128_load]

theorem readTotalsCollateral (evm : EVM.State) (asset : AccountAddress) :
    config.storageBackend.read ⟨"totalsCollateral", [.mindex (.address asset)]⟩
      totalsCollateralType evm =
    .ok (totalsCollateralValue
      (low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset)))
      (high128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset)))) := by
  change solidityReadStorage? config.storageBackend.locate? evm _ _ = _
  have hf := solidityReadFields_from_fields config.storageBackend.locate? evm
    ⟨"totalsCollateral", [.mindex (.address asset)]⟩ totalsCollateralTypes
    [("totalSupplyAsset", .int (low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (totalsCollateralSlot asset))).toNat),
      ("_reserved", .int (high128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (totalsCollateralSlot asset))).toNat)]
    (.cons ⟨rfl, readTotalsCollateralField evm asset false⟩
      (.cons ⟨rfl, readTotalsCollateralField evm asset true⟩ .nil))
  simp only [totalsCollateralType, solidityReadStorage?, hf, bind, EvalResult.bind, pure]
  rfl

theorem evalTotalsCollateral (frame : Frame) (evm : EVM.State) (asset : AccountAddress)
    (arg : Expr) (hc : frame.contract = contract)
    (hlocal : frame.locals.get? "totalsCollateral" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address asset)) :
    evalExpr? config frame evm (.storage ⟨"totalsCollateral", [.mindex arg]⟩) =
    .ok (totalsCollateralValue
      (low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset)))
      (high128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset)))) := by
  apply evalExpr_storage_typed hlocal
    (er := ⟨"totalsCollateral", [.mindex (.address asset)]⟩) (ty := totalsCollateralType)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact readTotalsCollateral evm asset

theorem writeTotalsCollateralReserved (evm : EVM.State) (asset : AccountAddress)
    (word : UInt256) :
    config.storageBackend.write
      ⟨"totalsCollateral", [.mindex (.address asset), .field "_reserved"]⟩
      (.elem (.int (.uint ⟨128, by decide⟩))) (.int word.toNat) evm =
    .ok (storePackedWord evm (totalsCollateralSlot asset) word 16 16) := by
  apply solidityStorageBackend_write_elem _ _ _ _ _ _
    { slot := totalsCollateralSlot asset, offset := 16, size := 16, hbound := by decide,
      type := .int (.uint ⟨128, by decide⟩) }
  · simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]; rfl
  · exact storageLocStore_packed_int evm _ word _ _ _

theorem writeTotalsCollateral (evm : EVM.State) (asset : AccountAddress)
    (total reserved : UInt256) :
    config.storageBackend.write ⟨"totalsCollateral", [.mindex (.address asset)]⟩
      totalsCollateralType (totalsCollateralValue total reserved) evm =
    .ok (storeTotalsCollateral evm asset total reserved) := by
  change solidityWriteStorage? config.storageBackend.locate? evm _ _ _ = _
  rw [totalsCollateralType, totalsCollateralValue, solidityWriteStorage?, if_pos rfl]
  apply solidityWriteFields_cons
  · exact writeTotalsCollateralBalance evm asset total
  apply solidityWriteFields_cons
  · exact writeTotalsCollateralReserved _ asset reserved
  simp only [solidityWriteFields?]
  rfl

theorem assignTotalsCollateral (frame : Frame) (evm : EVM.State) (asset : AccountAddress)
    (arg : Expr) (total reserved : UInt256) (hc : frame.contract = contract)
    (hlocal : frame.locals.get? "totalsCollateral" = none)
    (harg : evalExpr? config frame evm arg = .ok (.address asset)) :
    assignStorageRef? config frame evm .storage ⟨"totalsCollateral", [.mindex arg]⟩
      (totalsCollateralValue total reserved) =
    .ok (frame, storeTotalsCollateral evm asset total reserved) := by
  apply assignStorageRef_storage_typed hlocal
    (er := ⟨"totalsCollateral", [.mindex (.address asset)]⟩) (ty := totalsCollateralType)
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, harg,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact writeTotalsCollateral evm asset total reserved

theorem evalTotalsCollateralTotal {cfg frame evm expr total reserved}
    (he : evalExpr? cfg frame evm expr = .ok (totalsCollateralValue total reserved)) :
    evalExpr? cfg frame evm (.field expr "totalSupplyAsset") = .ok (.int total.toNat) := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  rfl

theorem assignLocalCollateralTotal {cfg frame evm name total reserved} (next : UInt256)
    (hget : frame.locals.get? name = some (totalsCollateralValue total reserved)) :
    assignStorageRef? cfg frame evm .localVar ⟨name, [.field "totalSupplyAsset"]⟩
      (.int next.toNat) =
    .ok ({ frame with
      locals := frame.locals.insert name (totalsCollateralValue next reserved) }, evm) := by
  apply assignLocalPath_frame hget
  simp only [updateLocalPath?, totalsCollateralValue, lookupField?, lookupAssoc,
    updateField?, updateAssoc, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

end Benchmarks.CompoundIII.Comet
