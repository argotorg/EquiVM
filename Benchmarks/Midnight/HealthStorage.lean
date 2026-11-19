import Benchmarks.Midnight.PositionFields
import Benchmarks.Midnight.CollateralStorage
import Benchmarks.Midnight.HealthArithmeticTrace

/-! Storage reads used by the health-check source body. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem resolvePositionBorrower {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (huser : frame.locals.get? "borrower" = some (.address (AccountAddress.ofNat user.toNat))) :
    resolveStorageRef? config frame evm { base := "position", steps :=
      [.mindex (.var "id"), .mindex (.var "borrower")] } =
      .ok (positionRef id user, positionType) := by
  apply resolveStorageRef?_ok hbase
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hid, huser,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
    rfl
  · rw [hc]; rfl

def healthPositionWord (evm : EVM.State) (id user : UInt256) : UInt256 :=
  Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user + ⟨2⟩)

theorem evalHealthDebt {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)) :
    evalExpr? config frame evm (.storage { base := "_position", steps := [.field "debt"] }) =
      .ok (.int (low128 (healthPositionWord evm id user)).toNat) := by
  apply evalStorageAliasField (loc := {
    slot := positionSlot id user + ⟨2⟩, offset := 0, size := 16, hbound := by decide,
    type := .int packedUInt128Int }) hget rfl rfl
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot
        (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
        (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨2⟩,
      offset := 0, size := 16, hbound := _, type := .int packedUInt128Int }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
      keyValueToWord_address_of_canonical user hcanon]
    rfl
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)

theorem evalHealthBitmap {frame : Frame} {evm : EVM.State} {id user : UInt256}
    (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)) :
    evalExpr? config frame evm
      (.storage { base := "_position", steps := [.field "collateralBitmap"] }) =
      .ok (.int (UInt256.shiftRight (healthPositionWord evm id user) (UInt256.ofNat 128)).toNat) := by
  apply evalStorageAliasField (loc := {
    slot := positionSlot id user + ⟨2⟩, offset := 16, size := 16, hbound := by decide,
    type := .int packedUInt128Int }) hget rfl rfl
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot
        (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
        (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨2⟩,
      offset := 16, size := 16, hbound := _, type := .int packedUInt128Int }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
      keyValueToWord_address_of_canonical user hcanon]
    rfl
  · exact storageLocLoad_uint128_high evm _

def healthCollateralExpr : Expr := .storage
  { base := "_position", steps := [.field "collateral", .aindex (.var "i")] }

theorem evalHealthCollateral {frame : Frame} {evm : EVM.State} {id user index : UInt256}
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hindex : frame.locals.get? "i" = some (.int index.toNat)) (hi : index.toNat < 128) :
    evalExpr? config frame evm healthCollateralExpr = .ok (.int
      (healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
        (positionSlot id user + ⟨3⟩) index).toNat) := by
  have hty : storageTypeAt? frame.contract.storage
      { (positionRef id user) with steps := (positionRef id user).steps ++ [.field "collateral"] } =
      some (.array (.elem (.int packedUInt128Int)) 128) := by rw [hc]; rfl
  have hresolve : resolveStorageRef? config frame evm
      { base := "_position", steps := [.field "collateral", .aindex (.var "i")] } =
      .ok (collateralEvaledRef id user index, .elem (.int packedUInt128Int)) := by
    have hfield : storageTypeStep? positionType (.field "collateral") =
        some (.array (.elem (.int packedUInt128Int)) 128) := rfl
    simp only [resolveStorageRef?, hget, evalStorageRefFrom?, evalStorageRefStep, hfield,
      evalExpr?, hindex, EvalResult.ofOption, bind, pure, EvalResult.bind, valueToKey?,
      arrayIndexInBounds?, hty, Int.natCast_nonneg, Nat.cast_lt, hi, and_self, if_true]
    rfl
  have hloc : midnightStorageLayout (collateralEvaledRef id user index) =
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
  rw [healthCollateralExpr, evalExpr?]
  simp only [hresolve, bind, EvalResult.bind,
    readStorage?_elem (cfg := config) (layout := midnightStorageLayout) rfl hloc,
    collateralLoc_load]
  rfl

end Benchmarks.Midnight
