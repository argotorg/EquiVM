import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage

/-! Pending-cap timestamp reads and the explicit uint184 value cast. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def acceptCapValue (evm : State) (id : UInt256) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ id))
    (UInt256.ofNat (2 ^ 184 - 1))

theorem acceptCapValue_toNat (evm : State) (id : UInt256) :
    (acceptCapValue evm id).toNat =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (solcMappingSlot ⟨16⟩ id)).toNat % 2 ^ 184 := by
  rw [acceptCapValue, uland_toNat,
    UInt256.toNat_ofNat_of_lt (by decide : 2 ^ 184 - 1 < UInt256.size)]
  exact nat_land_mask_eq_mod _ _

theorem acceptCapValue_bound (evm : State) (id : UInt256) :
    (acceptCapValue evm id).toNat < 2 ^ 184 := by
  rw [acceptCapValue_toNat]
  exact Nat.mod_lt _ (by decide)

theorem pendingCapTimeRead {frame : Frame} {evm : State} {id : UInt256} {index : Expr}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "pendingCap" = none)
    (hid : evalExpr? config frame evm index = .ok (wordBytes32Value id)) :
    evalExpr? config frame evm (.storage ⟨"pendingCap", [.mindex index, .field "validAt"]⟩) =
      .ok (uint256Value (marketRemovalPendingAt evm id)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .field "validAt"]⟩)
    (t := .int (.uint ⟨64, by decide⟩)) hbase
    (evalStorageRef_bytes32FieldExpr "pendingCap" "validAt" index _
      (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
    (loc :=
      { slot := solcMappingSlot ⟨16⟩ id, offset := 24, size := 8,
        hbound := by decide, type := .int (.uint ⟨64, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨16⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }) = _
    rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
      keyValueToWord_fixedBytes32 id]
  · exact storageLocLoad_uint_high evm (solcMappingSlot ⟨16⟩ id)
      24 8 ⟨64, by decide⟩ rfl rfl

-- LIBRARY CANDIDATE: explicit unsigned casts retain the residue at the target width.
theorem uintCastNatSource {cfg : Config} {frame : Frame} {evm : State} {expr : Expr}
    {n : Nat} (width : ABI.BitWidth)
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint width)))) =
      .ok (.int (Int.ofNat (n % 2 ^ width.val))) := by
  simp only [evalExpr?, he, bind, EvalResult.bind, castValue?, normalizeInt,
    EVM.twoPow, EvalResult.ofOption, Int.ofNat_eq_natCast, Int.natCast_emod]

theorem pendingCapValueCastRead {frame : Frame} {evm : State} {id : UInt256} {index : Expr}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "pendingCap" = none)
    (hid : evalExpr? config frame evm index = .ok (wordBytes32Value id)) :
    evalExpr? config frame evm
      (.cast (.storage ⟨"pendingCap", [.mindex index, .field "value"]⟩)
        (.elem (.int (.uint ⟨184, by decide⟩)))) = .ok (uint256Value (acceptCapValue evm id)) := by
  have hv : evalExpr? config frame evm
      (.storage ⟨"pendingCap", [.mindex index, .field "value"]⟩) =
      .ok (uint256Value (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ id))
        (UInt256.ofNat (2 ^ 192 - 1)))) := by
    apply evalExpr_storage_scalar_value
      (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
        .field "value"]⟩)
      (t := .int (.uint ⟨192, by decide⟩)) hbase
      (evalStorageRef_bytes32FieldExpr "pendingCap" "value" index _
        (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
      (loc :=
        { slot := solcMappingSlot ⟨16⟩ id, offset := 0, size := 24,
          hbound := by decide, type := .int (.uint ⟨192, by decide⟩) })
    · change some (StorageAddr.leaf
        { slot := solcMappingSlot ⟨16⟩
            (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
          offset := 0, size := 24, hbound := by decide,
          type := .int (.uint ⟨192, by decide⟩) }) = _
      rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
        keyValueToWord_fixedBytes32 id]
    · exact storageLocLoad_uint_offset0 evm _ 24 ⟨192, by decide⟩ rfl (by decide)
  rw [uintCastNatSource ⟨184, by decide⟩ hv, uint256Value, acceptCapValue_toNat]
  congr 3
  rw [uland_toNat, UInt256.toNat_ofNat_of_lt (by decide : 2 ^ 192 - 1 < UInt256.size)]
  change Nat.land _ (2 ^ 192 - 1) % 2 ^ 184 = _
  rw [nat_land_mask_eq_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 184 ∣ 2 ^ 192)]

theorem pendingCapPresent {evm : State} {id : UInt256}
    (hn : marketRemovalPendingAt evm id ≠ ⟨0⟩) :
    ∃ acc, evm.accountMap.get? evm.executionEnv.codeOwner = some acc := by
  cases ha : evm.accountMap.get? evm.executionEnv.codeOwner with
  | some acc => exact ⟨acc, rfl⟩
  | none =>
      apply False.elim
      apply hn
      simp only [marketRemovalPendingAt, Solm.EVM.storageLoad, State.lookupAccount, ha,
        Option.option]
      decide

end Benchmarks.Morpho.MetaMorphoV1_1
