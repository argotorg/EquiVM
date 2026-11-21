import Benchmarks.Midnight.HealthStorage

/-! Position references and field reads with arbitrary source-local names. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES resolvePositionRef: the address argument need not be named "user".
theorem resolveNamedPositionRef {frame : Frame} {evm : State} {id user : UInt256} {name : Ident}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "position" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hu : frame.locals.get? name = some (.address (AccountAddress.ofNat user.toNat))) :
    resolveStorageRef? config frame evm { base := "position", steps :=
      [.mindex (.var "id"), .mindex (.var name)] } = .ok (positionRef id user, positionType) := by
  apply resolveStorageRef?_ok hbase
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hid, hu,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
    rfl
  · rw [hc]; rfl

-- GENERALIZES evalPositionAliasField: support buyerPos and sellerPos as well as _position.
theorem evalNamedPositionField {frame : Frame} {evm : State} {id user : UInt256} {name : Ident}
    (i : Fin 4) (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? name = some (.storageRef (positionRef id user) positionType)) :
    evalExpr? config frame evm (.storage { base := name, steps := [.field (positionFieldName i)] }) =
      .ok (.int (positionFieldWord evm id user i).toNat) :=
  evalStorageAliasField hget (positionField_type i) rfl
    (positionField_layout id user i hcanon) (positionField_load evm id user i)

-- GENERALIZES evalHealthDebt: support any local position alias.
theorem evalNamedPositionDebt {frame : Frame} {evm : State} {id user : UInt256} {name : Ident}
    (hcanon : user.toNat < EVM.addressModulus)
    (hget : frame.locals.get? name = some (.storageRef (positionRef id user) positionType)) :
    evalExpr? config frame evm (.storage { base := name, steps := [.field "debt"] }) =
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

end Benchmarks.Midnight
