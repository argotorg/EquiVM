import Benchmarks.Midnight.HealthSourceFrame
import Benchmarks.Midnight.HealthStorage

/-! Named-index collateral expressions shared by supply, withdrawal, and liquidation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketCollateralExpr (indexName : Ident) : Expr :=
  .index (.field (.var "market") "collateralParams") (.var indexName)

theorem evalMarketCollateralAt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {index : UInt256} (indexName : Ident)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? indexName = some (.int index.toNat)) (hbound : index.toNat < m.collaterals.length) :
    evalExpr? cfg frame evm (marketCollateralExpr indexName) =
      .ok (Model.collateralValue m.collaterals[index.toNat].value) := by
  have harray : evalExpr? cfg frame evm (.field (.var "market") "collateralParams") =
      .ok (.array ((m.collaterals.map CollateralData.value).map Model.collateralValue)) := by
    simp only [evalExpr?, hm, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  rw [marketCollateralExpr, evalExpr?, harray]
  simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?]
  rw [if_pos (by simp only [List.length_map, Int.natCast_nonneg, true_and, Int.ofNat_lt]
                 exact hbound)]
  simp only [Int.toNat_natCast]
  rw [lookupNth_get _ index.toNat (by simpa using hbound)]
  simp only [List.getElem_map]
  rfl

theorem evalMarketCollateralAtRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {index : UInt256} (indexName : Ident)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? indexName = some (.int index.toNat))
    (hbound : ¬ index.toNat < m.collaterals.length) :
    evalExpr? cfg frame evm (marketCollateralExpr indexName) = .revert := by
  have harray : evalExpr? cfg frame evm (.field (.var "market") "collateralParams") =
      .ok (.array ((m.collaterals.map CollateralData.value).map Model.collateralValue)) := by
    simp only [evalExpr?, hm, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  rw [marketCollateralExpr, evalExpr?, harray]
  simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?,
    List.length_map, Int.natCast_nonneg, true_and, Int.ofNat_lt, hbound, if_false]

theorem resolvePositionAccount {frame : Frame} {evm : EVM.State} {id user : UInt256} (accountName : Ident)
    (hc : frame.contract = contract) (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (huser : frame.locals.get? accountName = some (.address (AccountAddress.ofNat user.toNat))) :
    resolveStorageRef? config frame evm { base := "position", steps :=
      [.mindex (.var "id"), .mindex (.var accountName)] } =
      .ok (positionRef id user, positionType) := by
  apply resolveStorageRef?_ok hbase
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hid, huser,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
    rfl
  · rw [hc]; rfl

def positionCollateralExpr (indexName : Ident) : Expr := .storage
  { base := "_position", steps := [.field "collateral", .aindex (.var indexName)] }

theorem resolvePositionCollateral {frame : Frame} {evm : EVM.State} {id user index : UInt256}
    (indexName : Ident) (hc : frame.contract = contract)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hindex : frame.locals.get? indexName = some (.int index.toNat)) (hi : index.toNat < 128) :
    resolveStorageRef? config frame evm
      { base := "_position", steps := [.field "collateral", .aindex (.var indexName)] } =
      .ok (collateralEvaledRef id user index, .elem (.int packedUInt128Int)) := by
  have hty : storageTypeAt? frame.contract.storage
      { (positionRef id user) with steps := (positionRef id user).steps ++ [.field "collateral"] } =
      some (.array (.elem (.int packedUInt128Int)) 128) := by rw [hc]; rfl

  have hfield : storageTypeStep? positionType (.field "collateral") =
      some (.array (.elem (.int packedUInt128Int)) 128) := rfl
  simp only [resolveStorageRef?, hget, evalStorageRefFrom?, evalStorageRefStep, hfield,
    evalExpr?, hindex, EvalResult.ofOption, bind, pure, EvalResult.bind, valueToKey?,
    arrayIndexInBounds?, hty, Int.natCast_nonneg, Nat.cast_lt, hi, and_self, if_true]
  rfl

theorem collateralLoc_layout (id user index : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) :
    midnightStorageLayout (collateralEvaledRef id user index) =
      some (.leaf (collateralLoc id user index)) := by

  change some (StorageAddr.leaf {
    slot := solcMappingSlot
      (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
      (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨3⟩ +
      UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 2),
    offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat % 2 * 16),
    size := 16, hbound := _, type := .int packedUInt128Int }) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
    keyValueToWord_address_of_canonical user hcanon,
    keyValueToWord_int_ofNat_of_lt (show index.toNat < UInt256.size from index.val.isLt),
    u256_ofNat_toNat]
  congr 3
  apply Fin.ext
  change (index.toNat % 2 * 16) % 32 = 16 * (index.toNat % 2)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem evalPositionCollateral {frame : Frame} {evm : EVM.State} {id user index : UInt256} (indexName : Ident)
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hindex : frame.locals.get? indexName = some (.int index.toNat)) (hi : index.toNat < 128) :
    evalExpr? config frame evm (positionCollateralExpr indexName) = .ok (.int
      (healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
        (positionSlot id user + ⟨3⟩) index).toNat) := by
  have hresolve := resolvePositionCollateral (evm := evm) indexName hc hget hindex hi
  have hloc := collateralLoc_layout id user index hcanon
  rw [positionCollateralExpr, evalExpr?]
  simp only [hresolve, bind, EvalResult.bind,
    readStorage?_elem (cfg := config) (layout := midnightStorageLayout) rfl hloc,
    collateralLoc_load]
  rfl

theorem evalPositionCollateralRevert {frame : Frame} {evm : EVM.State}
    {id user index : UInt256} (indexName : Ident) (hc : frame.contract = contract)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hindex : frame.locals.get? indexName = some (.int index.toNat)) (hi : ¬ index.toNat < 128) :
    evalExpr? config frame evm (positionCollateralExpr indexName) = .revert := by
  have hty : storageTypeAt? frame.contract.storage
      { (positionRef id user) with steps := (positionRef id user).steps ++ [.field "collateral"] } =
      some (.array (.elem (.int packedUInt128Int)) 128) := by rw [hc]; rfl
  have hfield : storageTypeStep? positionType (.field "collateral") =
      some (.array (.elem (.int packedUInt128Int)) 128) := rfl
  simp only [positionCollateralExpr, evalExpr?, resolveStorageRef?, hget, evalStorageRefFrom?,
    evalStorageRefStep, hfield, hindex, EvalResult.ofOption, bind, pure, EvalResult.bind,
    valueToKey?, arrayIndexInBounds?, hty, Int.natCast_nonneg, Nat.cast_lt, hi,
    and_false, if_false]

theorem assignPositionCollateral {frame : Frame} {evm evm' : EVM.State}
    {id user index : UInt256} {value : Value} (indexName : Ident)
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hindex : frame.locals.get? indexName = some (.int index.toNat)) (hi : index.toNat < 128)
    (hstore : storageLocStore evm (collateralLoc id user index) value = some evm') :
    assignStorageRef? config frame evm .storage
      { base := "_position", steps := [.field "collateral", .aindex (.var indexName)] } value =
      .ok (frame, evm') := by
  have hr := resolvePositionCollateral (evm := evm) indexName hc hget hindex hi
  have hl := collateralLoc_layout id user index hcanon
  have hb : config.storageBackend = solidityStorageBackend midnightStorageLayout := rfl
  simp only [assignStorageRef?, hr, hb, solidityStorageBackend, solidityWriteStorage?,
    solidityLeafLoc?_of_leaf hl, hstore, EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
