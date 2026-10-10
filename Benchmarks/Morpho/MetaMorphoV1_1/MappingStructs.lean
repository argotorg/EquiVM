import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.PackedStorage
import Reasoning.ABIViews

/-! Packed struct fields stored in bytes32-keyed mappings. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- GENERALIZES Reasoning.Storage.storageLocLoad_bool_offset0 to every byte offset.
theorem storageLocLoad_bool_shift (evm : EVM.State) (slot : UInt256) (offset : Fin 32) :
    storageLocLoad evm
      { slot := slot, offset := offset, size := 1,
        hbound := by have := offset.isLt; omega, type := .bool } =
      wordToElem .bool (UInt256.land
        (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (8 * offset.val))) ⟨255⟩) := by
  have hoff : 8 * offset.val < 256 := by have := offset.isLt; omega
  unfold storageLocLoad
  apply congrArg (wordToElem .bool)
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract
      offset.val (offset.val + 1)) = _
  rw [List.extract_eq_take_drop, Nat.add_sub_cancel_left,
    fromBytes'_drop_take_wordLE_land_div_mask _ _ 1 hoff (by decide),
    wordShiftRight_eq_div _ _ hoff]
  rw [Nat.pow_mul]
  rfl

-- LIBRARY CANDIDATE: a decoded bytes32 mapping key equals the corresponding calldata word.
theorem calldataBytes32Key {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    keyValueToWord (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32)) =
      calldataWord cd 4 := by
  have hlen' : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size - 4) = 32
    omega
  simp only [keyValueToWord, abiBytes32Width, hlen', ↓reduceIte, Nat.sub_self, Nat.mul_zero,
    pow_zero, Nat.mul_one]
  convert decode_word_at_eq cd 4 (by omega) (by decide) using 1
  simp [bytesToWord, EVM.Word.ofNat, fromByteArrayBigEndian, byteArray_toList_eq]

-- LIBRARY CANDIDATE: resolve a struct field after a bytes32-valued mapping-key expression.
theorem evalStorageRef_bytes32FieldExpr {cfg : Config} {solm : Frame} {evm : EVM.State}
    (base field : Ident) (key : Expr) (bs : List UInt8) (hlen : bs.length = 32)
    (hkey : evalExpr? cfg solm evm key = .ok (.fixedBytes abiBytes32Width bs)) :
    evalStorageRef cfg solm evm ⟨base, [.mindex key, .field field]⟩ =
      .ok ⟨base, [.mindex (.fixedBytes abiBytes32Width bs), .field field]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hkey,
    valueToKey_bytes32_of_length hlen, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem evalStorageRef_bytes32Field {cfg : Config} {solm : Frame} {evm : EVM.State}
    (base name field : Ident) (bs : List UInt8) (hlen : bs.length = 32)
    (hget : solm.locals.get? name = some (.fixedBytes abiBytes32Width bs)) :
    evalStorageRef cfg solm evm ⟨base, [.mindex (.var name), .field field]⟩ =
      .ok ⟨base, [.mindex (.fixedBytes abiBytes32Width bs), .field field]⟩ := by
  exact evalStorageRef_bytes32FieldExpr base field (.var name) bs hlen
    (by simp only [evalExpr?, hget, EvalResult.ofOption])

theorem evalStorage_pendingCapValue (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (w : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? "pendingCap" = none)
    (hget : locals.get? "arg0" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"pendingCap", [.mindex (.var "arg0"), .field "value"]⟩) =
      .ok (.int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ w))
        (UInt256.ofNat (2 ^ 192 - 1))).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width bs), .field "value"]⟩)
    (t := .int (.uint ⟨192, by decide⟩)) hbase
    (evalStorageRef_bytes32Field "pendingCap" "arg0" "value" bs hlen hget) rfl rfl
    (loc :=
      { slot := solcMappingSlot ⟨16⟩ w, offset := 0, size := 24,
        hbound := by decide, type := .int (.uint ⟨192, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨16⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
        offset := 0, size := 24, hbound := by decide,
        type := .int (.uint ⟨192, by decide⟩) }) = _
    rw [hkey]
  · exact storageLocLoad_uint_offset0 evm _ 24 ⟨192, by decide⟩ rfl (by decide)

theorem evalStorage_pendingCapValidAt (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (w : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? "pendingCap" = none)
    (hget : locals.get? "arg0" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"pendingCap", [.mindex (.var "arg0"), .field "validAt"]⟩) =
      .ok (.int (Int.ofNat (UInt256.shiftRight
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨16⟩ w))
        ⟨192⟩).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"pendingCap", [.mindex (.fixedBytes abiBytes32Width bs), .field "validAt"]⟩)
    (t := .int (.uint ⟨64, by decide⟩)) hbase
    (evalStorageRef_bytes32Field "pendingCap" "arg0" "validAt" bs hlen hget) rfl rfl
    (loc :=
      { slot := solcMappingSlot ⟨16⟩ w, offset := 24, size := 8,
        hbound := by decide, type := .int (.uint ⟨64, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨16⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
        offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }) = _
    rw [hkey]
  · exact storageLocLoad_uint_high evm _ 24 8 ⟨64, by decide⟩ rfl rfl

theorem evalStorage_configCap (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (w : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? "config" = none)
    (hget : locals.get? "arg0" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"config", [.mindex (.var "arg0"), .field "cap"]⟩) =
      .ok (.int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w))
        (UInt256.ofNat (2 ^ 184 - 1))).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width bs), .field "cap"]⟩)
    (t := .int (.uint ⟨184, by decide⟩)) hbase
    (evalStorageRef_bytes32Field "config" "arg0" "cap" bs hlen hget) rfl rfl
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ w, offset := 0, size := 23,
        hbound := by decide, type := .int (.uint ⟨184, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
        offset := 0, size := 23, hbound := by decide,
        type := .int (.uint ⟨184, by decide⟩) }) = _
    rw [hkey]
  · exact storageLocLoad_uint_offset0 evm _ 23 ⟨184, by decide⟩ rfl (by decide)

theorem evalStorage_configEnabled (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (w : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? "config" = none)
    (hget : locals.get? "arg0" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"config", [.mindex (.var "arg0"), .field "enabled"]⟩) =
      .ok (wordToElem .bool (UInt256.land
        (UInt256.shiftRight
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w))
          ⟨184⟩) ⟨255⟩)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width bs), .field "enabled"]⟩)
    (t := .bool) hbase
    (evalStorageRef_bytes32Field "config" "arg0" "enabled" bs hlen hget) rfl rfl
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ w, offset := 23, size := 1,
        hbound := by decide, type := .bool })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
        offset := 23, size := 1, hbound := by decide, type := .bool }) = _
    rw [hkey]
  · exact storageLocLoad_bool_shift evm _ 23

theorem evalStorage_configRemovableAt (evm : EVM.State) (locals imms : Store)
    (bs : List UInt8) (w : UInt256) (hlen : bs.length = 32)
    (hbase : locals.get? "config" = none)
    (hget : locals.get? "arg0" = some (.fixedBytes abiBytes32Width bs))
    (hkey : keyValueToWord (.fixedBytes abiBytes32Width bs) = w) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"config", [.mindex (.var "arg0"), .field "removableAt"]⟩) =
      .ok (.int (Int.ofNat (UInt256.shiftRight
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ w))
        ⟨192⟩).toNat)) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width bs), .field "removableAt"]⟩)
    (t := .int (.uint ⟨64, by decide⟩)) hbase
    (evalStorageRef_bytes32Field "config" "arg0" "removableAt" bs hlen hget) rfl rfl
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ w, offset := 24, size := 8,
        hbound := by decide, type := .int (.uint ⟨64, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩ (keyValueToWord (.fixedBytes abiBytes32Width bs)),
        offset := 24, size := 8, hbound := by decide,
        type := .int (.uint ⟨64, by decide⟩) }) = _
    rw [hkey]
  · exact storageLocLoad_uint_high evm _ 24 8 ⟨64, by decide⟩ rfl rfl

end Benchmarks.Morpho.MetaMorphoV1_1
