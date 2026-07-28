import Benchmarks.Dss.Vat.Gem
import Benchmarks.Dss.Vat.HealBase
import Benchmarks.Dss.Vat.Hope

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

/-! ## `flux(bytes32,address,address,uint256)` -/

abbrev fluxIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fluxSrcWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fluxSrcMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fluxSrcWord I)

abbrev fluxDstWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fluxDstMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fluxDstWord I)

abbrev fluxWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev fluxIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev fluxSrcValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (fluxSrcWord I).toNat)

abbrev fluxDstValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (fluxDstWord I).toNat)

abbrev fluxWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (fluxWadWord I).toNat)

abbrev fluxStore (I : ExecutionEnv) : Store :=
  ((((∅ : Store).insert "ilk" (fluxIlkValue I)).insert "src" (fluxSrcValue I)).insert
    "dst" (fluxDstValue I)).insert "wad" (fluxWadValue I)

abbrev fluxIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev fluxSrcKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (fluxSrcWord I).toNat)

abbrev fluxDstKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (fluxDstWord I).toNat)

abbrev fluxSourceKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev fluxSrcEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gem", steps := [.mindex (fluxIlkKey I), .mindex (fluxSrcKey I)] }

abbrev fluxDstEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gem", steps := [.mindex (fluxIlkKey I), .mindex (fluxDstKey I)] }

abbrev fluxWishEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "can", steps := [.mindex (fluxSrcKey I), .mindex (fluxSourceKey I)] }

def fluxSrcGemSlot (I : ExecutionEnv) : UInt256 :=
  gemSlot (fluxIlkKey I) (fluxSrcKey I)

def fluxDstGemSlot (I : ExecutionEnv) : UInt256 :=
  gemSlot (fluxIlkKey I) (fluxDstKey I)

def fluxWishSlot (I : ExecutionEnv) : UInt256 :=
  canSlot (fluxSrcKey I) (fluxSourceKey I)

abbrev fluxWishWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.eq (vatSlotWord (fluxWishSlot I) σ I) ⟨1⟩)
    (UInt256.eq (fluxSrcMaskedWord I) (hopeSourceWord I))

def fluxPostState (evm : EVM.State) (I : ExecutionEnv)
    (srcGemNew dstGemNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fluxSrcGemSlot I) srcGemNew)
    evm.executionEnv.codeOwner (fluxDstGemSlot I) dstGemNew

abbrev fluxStoreSrcGemNew (I : ExecutionEnv) (srcGemNew : UInt256) : Store :=
  (fluxStore I).insert "srcGemNew" (.int (Int.ofNat srcGemNew.toNat))

abbrev fluxStoreDstGemNew (I : ExecutionEnv) (srcGemNew dstGemNew : UInt256) : Store :=
  (fluxStoreSrcGemNew I srcGemNew).insert "dstGemNew" (.int (Int.ofNat dstGemNew.toNat))

theorem fluxStore_get_ilk (I : ExecutionEnv) :
    (fluxStore I).get? "ilk" = some (fluxIlkValue I) := by
  unfold fluxStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem fluxStore_get_src (I : ExecutionEnv) :
    (fluxStore I).get? "src" = some (fluxSrcValue I) := by
  unfold fluxStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem fluxStore_get_dst (I : ExecutionEnv) :
    (fluxStore I).get? "dst" = some (fluxDstValue I) := by
  unfold fluxStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem fluxStore_get_wad (I : ExecutionEnv) :
    (fluxStore I).get? "wad" = some (fluxWadValue I) := by
  simp [fluxStore]

theorem fluxStore_index_src (I : ExecutionEnv) :
    (fluxStore I)["src"] = fluxSrcValue I := by
  unfold fluxStore
  rw [Std.HashMap.getElem_insert]
  simp
  rw [Std.HashMap.getElem_insert]
  simp

theorem fluxStore_gem (I : ExecutionEnv) :
    (fluxStore I).get? "gem" = none := by
  unfold fluxStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem fluxStore_can (I : ExecutionEnv) :
    (fluxStore I).get? "can" = none := by
  unfold fluxStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem fluxStoreSrcGemNew_get_wad (I : ExecutionEnv) (srcGemNew : UInt256) :
    (fluxStoreSrcGemNew I srcGemNew).get? "wad" = some (fluxWadValue I) := by
  rw [fluxStoreSrcGemNew, store_get_ne _ _ (by native_decide), fluxStore_get_wad]

theorem fluxStoreSrcGemNew_get_srcGemNew (I : ExecutionEnv) (srcGemNew : UInt256) :
    (fluxStoreSrcGemNew I srcGemNew).get? "srcGemNew" =
      some (.int (Int.ofNat srcGemNew.toNat)) := by
  simp [fluxStoreSrcGemNew]

theorem fluxStoreSrcGemNew_get_ilk (I : ExecutionEnv) (srcGemNew : UInt256) :
    (fluxStoreSrcGemNew I srcGemNew).get? "ilk" = some (fluxIlkValue I) := by
  rw [fluxStoreSrcGemNew, store_get_ne _ _ (by native_decide), fluxStore_get_ilk]

theorem fluxStoreSrcGemNew_get_dst (I : ExecutionEnv) (srcGemNew : UInt256) :
    (fluxStoreSrcGemNew I srcGemNew).get? "dst" = some (fluxDstValue I) := by
  rw [fluxStoreSrcGemNew, store_get_ne _ _ (by native_decide), fluxStore_get_dst]

theorem fluxStoreSrcGemNew_get_src (I : ExecutionEnv) (srcGemNew : UInt256) :
    (fluxStoreSrcGemNew I srcGemNew).get? "src" = some (fluxSrcValue I) := by
  rw [fluxStoreSrcGemNew, store_get_ne _ _ (by native_decide), fluxStore_get_src]

theorem fluxStoreDstGemNew_get_dstGemNew (I : ExecutionEnv)
    (srcGemNew dstGemNew : UInt256) :
    (fluxStoreDstGemNew I srcGemNew dstGemNew).get? "dstGemNew" =
      some (.int (Int.ofNat dstGemNew.toNat)) := by
  simp [fluxStoreDstGemNew]

theorem fluxStoreDstGemNew_get_ilk (I : ExecutionEnv) (srcGemNew dstGemNew : UInt256) :
    (fluxStoreDstGemNew I srcGemNew dstGemNew).get? "ilk" = some (fluxIlkValue I) := by
  rw [fluxStoreDstGemNew, store_get_ne _ _ (by native_decide),
    fluxStoreSrcGemNew_get_ilk]

theorem fluxStoreDstGemNew_get_dst (I : ExecutionEnv) (srcGemNew dstGemNew : UInt256) :
    (fluxStoreDstGemNew I srcGemNew dstGemNew).get? "dst" = some (fluxDstValue I) := by
  rw [fluxStoreDstGemNew, store_get_ne _ _ (by native_decide),
    fluxStoreSrcGemNew_get_dst]

theorem fluxStoreSrcGemNew_gem (I : ExecutionEnv) (srcGemNew : UInt256) :
    (fluxStoreSrcGemNew I srcGemNew).get? "gem" = none := by
  rw [fluxStoreSrcGemNew, store_get_ne _ _ (by native_decide), fluxStore_gem]

theorem fluxStoreDstGemNew_gem (I : ExecutionEnv) (srcGemNew dstGemNew : UInt256) :
    (fluxStoreDstGemNew I srcGemNew dstGemNew).get? "gem" = none := by
  rw [fluxStoreDstGemNew, store_get_ne _ _ (by native_decide),
    fluxStoreSrcGemNew_gem]

theorem fluxIlkKeyWord_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (fluxIlkKey I) = fluxIlkWord I := by
  unfold fluxIlkKey fluxIlkWord calldataWord
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      uInt256OfByteArray (I.calldata.readBytes 4 32) :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [keyValueToWord, bytes32Width, ABI.bytesToWord, fromByteArrayBigEndian,
    byteArray_toList_eq, show 32 ≤ I.calldata.size - 4 by omega] at hword ⊢
  exact hword

theorem fluxSrcGemSlot_eq (I : ExecutionEnv) (hsz132 : 132 ≤ I.calldata.size) :
    fluxSrcGemSlot I =
      solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I)) (fluxSrcMaskedWord I) := by
  unfold fluxSrcGemSlot gemSlot gemIlkSlot fluxSrcKey fluxSrcMaskedWord mapSlot solcMappingSlot
  rw [fluxIlkKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem fluxDstGemSlot_eq (I : ExecutionEnv) (hsz132 : 132 ≤ I.calldata.size) :
    fluxDstGemSlot I =
      solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I)) (fluxDstMaskedWord I) := by
  unfold fluxDstGemSlot gemSlot gemIlkSlot fluxDstKey fluxDstMaskedWord mapSlot solcMappingSlot
  rw [fluxIlkKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem fluxWishSlot_eq (I : ExecutionEnv) :
    fluxWishSlot I =
      solcMappingSlot (solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I)) (hopeSourceWord I) := by
  unfold fluxWishSlot canSlot canOwnerSlot fluxSrcKey fluxSourceKey fluxSrcMaskedWord
    hopeSourceWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem fluxSrcMaskedWord_canonical (I : ExecutionEnv) :
    (fluxSrcMaskedWord I).toNat < EVM.addressModulus := by
  unfold fluxSrcMaskedWord
  rw [u256_land_comm solcAddrMask (fluxSrcWord I)]
  exact solcAddrMask_result_canonical (fluxSrcWord I)

theorem fluxDstMaskedWord_canonical (I : ExecutionEnv) :
    (fluxDstMaskedWord I).toNat < EVM.addressModulus := by
  unfold fluxDstMaskedWord
  rw [u256_land_comm solcAddrMask (fluxDstWord I)]
  exact solcAddrMask_result_canonical (fluxDstWord I)

theorem evalStorageRef_flux_src_gem (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := fluxStore I } evm
      (gemRef (.var "ilk") (.var "src")) = .ok (fluxSrcEvaledRef I) := by
  have hlen :
      ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    simp [bytes32Width]
    omega
  simp [fluxSrcEvaledRef, fluxIlkValue, fluxSrcValue, fluxIlkKey, fluxSrcKey, gemRef,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    fluxStore_get_ilk, fluxStore_get_src, hlen]

theorem evalStorageRef_flux_can (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := fluxStore I } evm
      (canRef (.var "src") sender) = .ok (fluxWishEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, fluxWishEvaledRef, hsrc, fluxSrcValue, fluxSourceKey, fluxSrcKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    fluxStore_index_src]

theorem evalStorageRef_flux_dst_gem_after_src (evm : EVM.State) (I : ExecutionEnv)
    (srcGemNew : UInt256) (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
      evm (gemRef (.var "ilk") (.var "dst")) = .ok (fluxDstEvaledRef I) := by
  have hlen :
      ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    simp [bytes32Width]
    omega
  simp [fluxDstEvaledRef, fluxIlkValue, fluxDstValue, fluxIlkKey, fluxDstKey, gemRef,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    fluxStoreSrcGemNew_get_ilk, fluxStoreSrcGemNew_get_dst, hlen]

theorem evalStorageRef_flux_src_gem_after_src (evm : EVM.State) (I : ExecutionEnv)
    (srcGemNew : UInt256) (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
      evm (gemRef (.var "ilk") (.var "src")) = .ok (fluxSrcEvaledRef I) := by
  have hlen :
      ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    simp [bytes32Width]
    omega
  simp [fluxSrcEvaledRef, fluxIlkValue, fluxSrcValue, fluxIlkKey, fluxSrcKey, gemRef,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    fluxStoreSrcGemNew_get_ilk, fluxStoreSrcGemNew_get_src, hlen]

theorem evalStorageRef_flux_dst_gem_after_dst (evm : EVM.State) (I : ExecutionEnv)
    (srcGemNew dstGemNew : UInt256) (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config
      { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew } evm
      (gemRef (.var "ilk") (.var "dst")) = .ok (fluxDstEvaledRef I) := by
  have hlen :
      ((I.calldata.toList.drop 4).take 32).length = ↑bytes32Width + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    simp [bytes32Width]
    omega
  simp [fluxDstEvaledRef, fluxIlkValue, fluxDstValue, fluxIlkKey, fluxDstKey, gemRef,
    evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
    EvalResult.ofOption, EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    fluxStoreDstGemNew_get_ilk, fluxStoreDstGemNew_get_dst, hlen]

theorem fluxStorageType_src_gem (I : ExecutionEnv) :
    storageTypeAt? contract.storage (fluxSrcEvaledRef I) = some (.elem (.int uint256Int)) := by
  change storageTypeAt? storageDecls (fluxSrcEvaledRef I) = some (.elem (.int uint256Int))
  simp [fluxSrcEvaledRef, storageTypeAt?, storageTypeStep?, storageDecls, uint256St]

theorem fluxStorageType_dst_gem (I : ExecutionEnv) :
    storageTypeAt? contract.storage (fluxDstEvaledRef I) = some (.elem (.int uint256Int)) := by
  change storageTypeAt? storageDecls (fluxDstEvaledRef I) = some (.elem (.int uint256Int))
  simp [fluxDstEvaledRef, storageTypeAt?, storageTypeStep?, storageDecls, uint256St]

theorem fluxStorageType_can (I : ExecutionEnv) :
    storageTypeAt? contract.storage (fluxWishEvaledRef I) = some (.elem (.int uint256Int)) := by
  change storageTypeAt? storageDecls (fluxWishEvaledRef I) = some (.elem (.int uint256Int))
  simp [fluxWishEvaledRef, storageTypeAt?, storageTypeStep?, storageDecls, uint256St]

theorem fluxStorageLayout_src_gem (I : ExecutionEnv) :
    config.storage.layout (fluxSrcEvaledRef I) =
      fun _ => some (wordLoc (fluxSrcGemSlot I)) := by
  funext evm
  change storageLayoutRaw (fluxSrcEvaledRef I) evm = some (wordLoc (fluxSrcGemSlot I))
  simp [storageLayoutRaw, fluxSrcEvaledRef, fluxSrcGemSlot]

theorem fluxStorageLayout_dst_gem (I : ExecutionEnv) :
    config.storage.layout (fluxDstEvaledRef I) =
      fun _ => some (wordLoc (fluxDstGemSlot I)) := by
  funext evm
  change storageLayoutRaw (fluxDstEvaledRef I) evm = some (wordLoc (fluxDstGemSlot I))
  simp [storageLayoutRaw, fluxDstEvaledRef, fluxDstGemSlot]

theorem fluxStorageLayout_can (I : ExecutionEnv) :
    config.storage.layout (fluxWishEvaledRef I) =
      fun _ => some (wordLoc (fluxWishSlot I)) := by
  funext evm
  change storageLayoutRaw (fluxWishEvaledRef I) evm = some (wordLoc (fluxWishSlot I))
  simp [storageLayoutRaw, fluxWishEvaledRef, fluxWishSlot]

set_option maxHeartbeats 1000000 in
theorem evalExpr_flux_src_gem_old {evm : EVM.State} {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (.storage (gemRef (.var "ilk") (.var "src"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxSrcGemSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := fluxStore_gem I)
    (her := evalStorageRef_flux_src_gem evm I (by omega))
    (hty := fluxStorageType_src_gem I)
    (hloc := fluxStorageLayout_src_gem I)
    (hload := vatStorageLocLoad_uint256 evm (fluxSrcGemSlot I))

set_option maxHeartbeats 1000000 in
theorem evalExpr_flux_dst_gem_after_src {evm : EVM.State} {I : ExecutionEnv}
    (srcGemNew : UInt256) (hsz132 : 132 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew } evm
      (.storage (gemRef (.var "ilk") (.var "dst"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxDstGemSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := fluxStoreSrcGemNew_gem I srcGemNew)
    (her := evalStorageRef_flux_dst_gem_after_src evm I srcGemNew (by omega))
    (hty := fluxStorageType_dst_gem I)
    (hloc := fluxStorageLayout_dst_gem I)
    (hload := vatStorageLocLoad_uint256 evm (fluxDstGemSlot I))

set_option maxHeartbeats 1000000 in
theorem evalExpr_flux_dst_gem_after_dst {evm : EVM.State} {I : ExecutionEnv}
    (srcGemNew dstGemNew : UInt256) (hsz132 : 132 ≤ I.calldata.size) :
    evalExpr? config
      { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew } evm
      (.storage (gemRef (.var "ilk") (.var "dst"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxDstGemSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := fluxStoreDstGemNew_gem I srcGemNew dstGemNew)
    (her := evalStorageRef_flux_dst_gem_after_dst evm I srcGemNew dstGemNew (by omega))
    (hty := fluxStorageType_dst_gem I)
    (hloc := fluxStorageLayout_dst_gem I)
    (hload := vatStorageLocLoad_uint256 evm (fluxDstGemSlot I))

set_option maxHeartbeats 1000000 in
theorem evalExpr_flux_src_gem_after_src {evm : EVM.State} {I : ExecutionEnv}
    (srcGemNew : UInt256) (hsz132 : 132 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew } evm
      (.storage (gemRef (.var "ilk") (.var "src"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxSrcGemSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := fluxStoreSrcGemNew_gem I srcGemNew)
    (her := evalStorageRef_flux_src_gem_after_src evm I srcGemNew (by omega))
    (hty := fluxStorageType_src_gem I)
    (hloc := fluxStorageLayout_src_gem I)
    (hload := vatStorageLocLoad_uint256 evm (fluxSrcGemSlot I))

theorem evalExpr_flux_can {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (.storage (canRef (.var "src") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxWishSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := fluxStore_can I)
    (her := evalStorageRef_flux_can evm I hsrc)
    (hty := fluxStorageType_can I)
    (hloc := fluxStorageLayout_can I)
    (hload := vatStorageLocLoad_uint256 evm (fluxWishSlot I))

theorem fluxEvalExpr_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem fluxEvalExpr_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem fluxHopeSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (hopeSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [hopeSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem evalExpr_flux_src_sender_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (heq : fluxSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (.binary .eq (.var "src") sender) = .ok (.bool true) := by
  have hsrcValue :
      fluxSrcValue I = .address evm.executionEnv.source := by
    rw [fluxSrcValue, solcAddressValue_masked (fluxSrcWord I)]
    change Value.address (AccountAddress.ofNat (fluxSrcMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [fluxHopeSource_ofNat I, ← hsrc]
  have hbeq : (fluxSrcValue I == Value.address evm.executionEnv.source) = true := by
    rw [hsrcValue]
    simp
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [fluxStore_get_src I, hsrcValue]
  simp [evalBinaryOp?]

theorem evalExpr_flux_src_sender_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hne : fluxSrcMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (.binary .eq (.var "src") sender) = .ok (.bool false) := by
  have hneValue :
      fluxSrcValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (fluxSrcMaskedWord I).toNat) =
          Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (fluxSrcWord I), ← hval]
    have hword : fluxSrcMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (fluxSrcMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (fluxSrcMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (fluxSrcMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsrc]
      exact hnat
    exact hne hword
  have hbeq : (fluxSrcValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [fluxStore_get_src I]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_flux_can_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_flux_can (evm := evm) (I := I) hsrc, hcan,
    show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_flux_can_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_flux_can (evm := evm) (I := I) hsrc, hneNat]

theorem evalExpr_flux_wish_true_src {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (heq : fluxSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact fluxEvalExpr_or_true_left
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_flux_src_sender_eq_true (evm := evm) (I := I) hsrc heq)

theorem evalExpr_flux_wish_true_can {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hne : fluxSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact fluxEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_flux_src_sender_eq_false (evm := evm) (I := I) hsrc hne)
    (evalExpr_flux_can_eq_true (evm := evm) (I := I) hsrc hcan)

theorem evalExpr_flux_wish_false {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hne : fluxSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (fluxWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fluxStore I } evm
      (wishExpr (.var "src") sender) = .ok (.bool false) := by
  exact fluxEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_flux_src_sender_eq_false (evm := evm) (I := I) hsrc hne)
    (evalExpr_flux_can_eq_false (evm := evm) (I := I) hsrc hcan)

theorem fluxWishWord_true_src {σ : AccountMap} {I : ExecutionEnv}
    (heq : fluxSrcMaskedWord I = hopeSourceWord I) :
    fluxWishWord σ I ≠ ⟨0⟩ := by
  by_cases hcan : vatSlotWord (fluxWishSlot I) σ I = ⟨1⟩
  · unfold fluxWishWord
    rw [heq, hcan, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold fluxWishWord
    rw [heq, u256_eq_refl, u256_eq_of_ne hcan]
    rw [u256_lor_comm, u256_lor_zero]
    exact one_ne_zero_uint

theorem fluxWishWord_true_can {σ : AccountMap} {I : ExecutionEnv}
    (hcan : vatSlotWord (fluxWishSlot I) σ I = ⟨1⟩) :
    fluxWishWord σ I ≠ ⟨0⟩ := by
  by_cases hsrc : fluxSrcMaskedWord I = hopeSourceWord I
  · unfold fluxWishWord
    rw [hcan, hsrc, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold fluxWishWord
    rw [hcan, u256_eq_refl, u256_eq_of_ne hsrc]
    rw [u256_lor_zero]
    exact one_ne_zero_uint

theorem fluxWishWord_false {σ : AccountMap} {I : ExecutionEnv}
    (hne : fluxSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : vatSlotWord (fluxWishSlot I) σ I ≠ ⟨1⟩) :
    fluxWishWord σ I = ⟨0⟩ := by
  unfold fluxWishWord
  rw [u256_eq_of_ne hcan, u256_eq_of_ne hne]
  rfl

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxWishLoaded
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2468⟩
      [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      [vatSlotWord (fluxWishSlot I) σ I, ⟨1⟩, ⟨0⟩, fluxSrcMaskedWord I,
        hopeSourceWord I, UInt256.ofNat I.source.val, fluxSrcMaskedWord I, ⟨2478⟩,
        fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I))
        (twoWordHashMem (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6557 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2478⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push2 ⟨6557⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd6568raw := evm_run rd6557 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (fluxSrcMaskedWord I) =
        fluxSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left (fluxSrcMaskedWord_canonical I)
  have rd6568 := rd6568raw
  rw [hmask] at rd6568
  have rd6573pre := evm_run rd6568 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6573 := rd6573pre.mstore 0 (wordAt0Mem (fluxSrcMaskedWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6580pre := evm_run rd6573 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6580 := rd6580pre.mstore 0
    (twoWordHashMem (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6585pre := evm_run rd6580 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)
            |>.readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I) :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I) solcFreePtrMem_size
  have rd6585 := rd6585pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd6588raw := evm_run rd6585 with [
    raw swap6 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hcallerMask :
      UInt256.land (UInt256.ofNat I.source.val)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        hopeSourceWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    change UInt256.land solcAddrMask (hopeSourceWord I) = hopeSourceWord I
    exact solcAddrMask_clean_left (by
      rw [hopeSourceWord_toNat]
      exact I.source.isLt)
  have rd6588 := rd6588raw
  rw [hcallerMask] at rd6588
  have rd6591pre := evm_run rd6588 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  have rd6591 := rd6591pre.mstore 0
    (wordAt0Mem (hopeSourceWord I)
      (twoWordHashMem (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6595pre := evm_run rd6591 with [
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd6595 := rd6595pre.mstore 0
    (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I))
      (twoWordHashMem (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6597pre := evm_run rd6595 with [
    raw dup3 (by native_decide) (by evm_ov)]
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I))
            (twoWordHashMem (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)).readWithPadding 0 64))) =
        fluxWishSlot I := by
    rw [fluxWishSlot_eq I]
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I))
      (hopeSourceWord I)
      (twoWordHashMem_size_96 (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem_size)
  have rd6597 := rd6597pre.keccak256 0 (fluxWishSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6599raw⟩ := rd6597.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [vatSlotWord, solcSlotWord] using rd6599raw⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxWishBranchOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      [vatSlotWord (fluxWishSlot I) σ I, ⟨1⟩, ⟨0⟩, fluxSrcMaskedWord I,
        hopeSourceWord I, UInt256.ofNat I.source.val, fluxSrcMaskedWord I, ⟨2478⟩,
        fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwish : fluxWishWord σ I ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6608pre := evm_run h with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw push2 ⟨6612⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have rd6605 := rd6608pre.eq (by native_decide) (by evm_ov)
  have rd6608mid := evm_run rd6605 with [
    raw swap2 (by native_decide) (by evm_ov)]
  have rd6608 := rd6608mid.eq (by native_decide) (by evm_ov)
  have rd6791 := evm_run rd6608 with [
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd6792 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd6793 := rd6792.lor (by native_decide) (by evm_ov)
  have rd6612raw := evm_run rd6793 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd6612 := rd6612raw
  have rd2478raw := evm_run rd6612 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2545⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd2478raw.jumpiT (by native_decide) hwish (by jump_dest) (by simp)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxWishBranchRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      [vatSlotWord (fluxWishSlot I) σ I, ⟨1⟩, ⟨0⟩, fluxSrcMaskedWord I,
        hopeSourceWord I, UInt256.ofNat I.source.val, fluxSrcMaskedWord I, ⟨2478⟩,
        fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hwish : fluxWishWord σ I = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd6608pre := evm_run h with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw push2 ⟨6612⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have rd6605 := rd6608pre.eq (by native_decide) (by evm_ov)
  have rd6608mid := evm_run rd6605 with [
    raw swap2 (by native_decide) (by evm_ov)]
  have rd6608 := rd6608mid.eq (by native_decide) (by evm_ov)
  have rd6791 := evm_run rd6608 with [
    raw push2 ⟨6791⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd6792 := evm_run rd6791 with [
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd6793 := rd6792.lor (by native_decide) (by evm_ov)
  have rd6612raw := evm_run rd6793 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd2478raw := evm_run rd6612raw with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2545⟩ (by native_decide) (by evm_ov)]
  have rd2483 := rd2478raw.jumpiNT (by native_decide) hwish (by simp)
  exact RD.solcErrorStringRevertTail
    (code := vatBytecode) (pc := ⟨2483⟩) (len := ⟨15⟩)
    (rawWord := ⟨112128532177926167570164739106265433⟩) (shift := ⟨138⟩)
    (word := UInt256.shiftLeft ⟨112128532177926167570164739106265433⟩ ⟨138⟩)
    (op := .PUSH15) (width := 15)
    rd2483
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl hmem hread64 (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxSourceSubSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hle :
      (fluxWadWord I).toNat ≤
        (solcSlotWord σ I
          (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
            (fluxSrcMaskedWord I))).toNat) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2590⟩
      (UInt256.sub
          (solcSlotWord σ I
            (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
              (fluxSrcMaskedWord I)))
          (fluxWadWord I) ::
        fluxWadWord I :: fluxDstMaskedWord I :: fluxSrcMaskedWord I ::
        fluxIlkWord I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (fluxSrcMaskedWord I)
        (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
        (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let inner := solcMappingSlot ⟨4⟩ (fluxIlkWord I)
  let slot := solcMappingSlot inner (fluxSrcMaskedWord I)
  let old := solcSlotWord σ I slot
  have rd2546 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2548 := rd2546.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2549 := rd2548.dup5 (by native_decide) (by evm_ov)
  have rd2550pre := rd2549.dup2 (by native_decide) (by evm_ov)
  have rd2550 := rd2550pre.mstore 0 (wordAt0Mem (fluxIlkWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2557pre := evm_run rd2550 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2557 := rd2557pre.mstore 0
    (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2562pre := evm_run rd2557 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        inner := by
    simpa [inner] using twoWordHashMem_solcMappingSlot ⟨4⟩ (fluxIlkWord I) hmem
  have rd2562 := rd2562pre.keccak256 0 inner (UInt256.ofNat 3)
    (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd2572raw := evm_run rd2562 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (fluxSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        fluxSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    exact solcAddrMask_clean_left (fluxSrcMaskedWord_canonical I)
  have rd2572 := rd2572raw
  rw [hmask] at rd2572
  have rd2574pre := evm_run rd2572 with [
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2574 := rd2574pre.mstore 0
    (wordAt0Mem (fluxSrcMaskedWord I) (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2577pre := evm_run rd2574 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2577 := rd2577pre.mstore 0
    (twoWordHashMem (fluxSrcMaskedWord I) inner (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2579pre := evm_run rd2577 with [
    raw swap1 (by native_decide) (by evm_ov)]
  have hmemInner : (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (fluxIlkWord I) ⟨4⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (fluxSrcMaskedWord I) inner
            (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot inner (fluxSrcMaskedWord I) hmemInner
  have rd2579 := rd2579pre.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2581raw⟩ := rd2579.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd2581 := rd2581raw
  rw [hold] at rd2581
  have rd6621pre := evm_run rd2581 with [
    raw push2 ⟨2590⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubSuccess
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := old) (b := fluxWadWord I) (ret := ⟨2590⟩)
    (R := [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel])
    (by simpa [old, slot, inner] using rd6621)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot, inner] using hle) (by jump_dest) (by jump_dest) (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxSourceSubRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hlt :
      (solcSlotWord σ I
        (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
          (fluxSrcMaskedWord I))).toNat < (fluxWadWord I).toNat) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let inner := solcMappingSlot ⟨4⟩ (fluxIlkWord I)
  let slot := solcMappingSlot inner (fluxSrcMaskedWord I)
  let old := solcSlotWord σ I slot
  have rd2546 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2548 := rd2546.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2549 := rd2548.dup5 (by native_decide) (by evm_ov)
  have rd2550pre := rd2549.dup2 (by native_decide) (by evm_ov)
  have rd2550 := rd2550pre.mstore 0 (wordAt0Mem (fluxIlkWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2557pre := evm_run rd2550 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2557 := rd2557pre.mstore 0
    (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2562pre := evm_run rd2557 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem).readWithPadding 0 64))) =
        inner := by
    simpa [inner] using twoWordHashMem_solcMappingSlot ⟨4⟩ (fluxIlkWord I) hmem
  have rd2562 := rd2562pre.keccak256 0 inner (UInt256.ofNat 3)
    (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd2572raw := evm_run rd2562 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (fluxSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        fluxSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    exact solcAddrMask_clean_left (fluxSrcMaskedWord_canonical I)
  have rd2572 := rd2572raw
  rw [hmask] at rd2572
  have rd2574pre := evm_run rd2572 with [
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2574 := rd2574pre.mstore 0
    (wordAt0Mem (fluxSrcMaskedWord I) (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2577pre := evm_run rd2574 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2577 := rd2577pre.mstore 0
    (twoWordHashMem (fluxSrcMaskedWord I) inner (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2579pre := evm_run rd2577 with [
    raw swap1 (by native_decide) (by evm_ov)]
  have hmemInner : (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 (fluxIlkWord I) ⟨4⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (fluxSrcMaskedWord I) inner
            (twoWordHashMem (fluxIlkWord I) ⟨4⟩ mem)).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot inner (fluxSrcMaskedWord I) hmemInner
  have rd2579 := rd2579pre.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2581raw⟩ := rd2579.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd2581 := rd2581raw
  rw [hold] at rd2581
  have rd6621pre := evm_run rd2581 with [
    raw push2 ⟨2590⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := old) (b := fluxWadWord I) (ret := ⟨2590⟩)
    (R := [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel])
    (by simpa [old, slot, inner] using rd6621)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot, inner] using hlt)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxSourceStoreValue
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {srcGemNew wad dst src ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨2590⟩
      (srcGemNew :: wad :: dst :: src :: ilk :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hsrcClean : UInt256.land solcAddrMask src = src)
    (hperm : ee.perm = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨2630⟩
      (solcAddrMask :: ⟨0⟩ :: ⟨64⟩ :: wad :: dst :: src :: ilk :: ret :: R)
      (twoWordHashMem src (solcMappingSlot ⟨4⟩ ilk)
        (twoWordHashMem ilk ⟨4⟩ mem))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) src) srcGemNew) k' C' := by
  let inner := solcMappingSlot ⟨4⟩ ilk
  let slot := solcMappingSlot inner src
  have rd2591 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2595pre := evm_run rd2591 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2595 := rd2595pre.mstore 0 (wordAt0Mem ilk mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2602pre := evm_run rd2595 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2602 := rd2602pre.mstore 0
    (twoWordHashMem ilk ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2607pre := evm_run rd2602 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨4⟩ mem).readWithPadding 0 64))) =
        inner := by
    simpa [inner] using twoWordHashMem_solcMappingSlot ⟨4⟩ ilk hmem
  have rd2607 := rd2607pre.keccak256 0 inner (UInt256.ofNat 3)
    (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd2618raw := evm_run rd2607 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          src =
        src := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hsrcClean
  have rd2618 := rd2618raw
  rw [hmask] at rd2618
  have rd2620pre := evm_run rd2618 with [
    raw dup6 (by native_decide) (by evm_ov)]
  have rd2620 := rd2620pre.mstore 0
    (wordAt0Mem src (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2622pre := evm_run rd2620 with [
    raw swap3 (by native_decide) (by evm_ov)]
  have rd2622 := rd2622pre.mstore 0
    (twoWordHashMem src inner (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2625pre := evm_run rd2622 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hmemInner : (twoWordHashMem ilk ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨4⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem src inner
            (twoWordHashMem ilk ⟨4⟩ mem)).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot inner src hmemInner
  have rd2625 := rd2625pre.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd2629pre := evm_run rd2625 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2630raw⟩ := rd2629pre.sstore hperm (by native_decide)
    (by simp [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, by simpa [slot, inner] using rd2630raw⟩

set_option maxHeartbeats 1000000 in
theorem wordAt0Mem_twoWordHashMem_solcMappingSlot (baseSlot key oldKey : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  have hbase : (twoWordHashMem oldKey baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 oldKey baseSlot hmem
  have hread64 :
      (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).readWithPadding 0 64 =
        UInt256.toByteArray key ++ UInt256.toByteArray baseSlot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
        (by rw [wordAt0Mem_size_96 key hbase]; omega)]
    have hleft :
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 32 =
          UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0
          (by rw [wordAt0Mem_size_96 key hbase]; omega),
        wordAt0Mem_read0]
    have hright :
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 32 64 =
          UInt256.toByteArray baseSlot := by
      rw [← readWithPadding_eq_extract _ 32
          (by rw [wordAt0Mem_size_96 key hbase]; omega)]
      unfold wordAt0Mem
      rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by rw [hbase]; omega)
        (by omega) (by rw [hbase]; norm_num)]
      exact twoWordHashMem_read32 oldKey baseSlot hmem
    rw [show (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 64 =
        (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 0 32 ++
          (wordAt0Mem key (twoWordHashMem oldKey baseSlot mem)).extract 32 64 by
        rw [ByteArray.extract_append_extract]
        norm_num]
    rw [hleft, hright]
  rw [hread64]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxDestAddSuccess
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {wad dst src ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨2630⟩
      (solcAddrMask :: ⟨0⟩ :: ⟨64⟩ :: wad :: dst :: src :: ilk :: ret :: R)
      (twoWordHashMem src (solcMappingSlot ⟨4⟩ ilk)
        (twoWordHashMem ilk ⟨4⟩ mem))
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hdstClean : UInt256.land dst solcAddrMask = dst)
    (hfit :
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) dst)).toNat +
          wad.toNat < UInt256.size)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨2645⟩
      ((solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) dst) + wad) ::
        wad :: dst :: src :: ilk :: ret :: R)
      (wordAt0Mem dst
        (twoWordHashMem src (solcMappingSlot ⟨4⟩ ilk)
          (twoWordHashMem ilk ⟨4⟩ mem)))
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  let inner := solcMappingSlot ⟨4⟩ ilk
  let slot := solcMappingSlot inner dst
  let old := solcSlotWord σ ee slot
  have rd2631raw := evm_run h with [
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have rd2631 := rd2631raw
  rw [hdstClean] at rd2631
  have rd2633pre := evm_run rd2631 with [
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2633 := rd2633pre.mstore 0
    (wordAt0Mem dst
      (twoWordHashMem src inner (twoWordHashMem ilk ⟨4⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem dst
            (twoWordHashMem src inner (twoWordHashMem ilk ⟨4⟩ mem))).readWithPadding 0 64))) =
        slot := by
    have hinnerMem : (twoWordHashMem ilk ⟨4⟩ mem).size = 96 :=
      twoWordHashMem_size_96 ilk ⟨4⟩ hmem
    simpa [slot] using
      wordAt0Mem_twoWordHashMem_solcMappingSlot inner dst src hinnerMem
  have rd2634 := rd2633.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2636raw⟩ := rd2634.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd2636 := rd2636raw
  rw [hold] at rd2636
  have rd6637pre := evm_run rd2636 with [
    raw push2 ⟨2645⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6637⟩ (by native_decide) (by evm_ov)]
  have rd6637 := rd6637pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedAddSuccess
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := old) (b := wad) (ret := ⟨2645⟩)
    (R := [wad, dst, src, ilk, ret] ++ R)
    (by simpa [old, slot, inner] using rd6637)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot, inner] using hfit) (by jump_dest) (by jump_dest)
    (by simp [List.length_cons, List.length_append] at hov ⊢; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxDestAddRevert
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {wad dst src ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨2630⟩
      (solcAddrMask :: ⟨0⟩ :: ⟨64⟩ :: wad :: dst :: src :: ilk :: ret :: R)
      (twoWordHashMem src (solcMappingSlot ⟨4⟩ ilk)
        (twoWordHashMem ilk ⟨4⟩ mem))
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hdstClean : UInt256.land dst solcAddrMask = dst)
    (hover :
      UInt256.size ≤
        (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) dst)).toNat +
          wad.toNat)
    (hov : R.length + 14 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  let inner := solcMappingSlot ⟨4⟩ ilk
  let slot := solcMappingSlot inner dst
  let old := solcSlotWord σ ee slot
  have rd2631raw := evm_run h with [
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have rd2631 := rd2631raw
  rw [hdstClean] at rd2631
  have rd2633pre := evm_run rd2631 with [
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2633 := rd2633pre.mstore 0
    (wordAt0Mem dst
      (twoWordHashMem src inner (twoWordHashMem ilk ⟨4⟩ mem)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem dst
            (twoWordHashMem src inner (twoWordHashMem ilk ⟨4⟩ mem))).readWithPadding 0 64))) =
        slot := by
    have hinnerMem : (twoWordHashMem ilk ⟨4⟩ mem).size = 96 :=
      twoWordHashMem_size_96 ilk ⟨4⟩ hmem
    simpa [slot] using
      wordAt0Mem_twoWordHashMem_solcMappingSlot inner dst src hinnerMem
  have rd2634 := rd2633.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2636raw⟩ := rd2634.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd2636 := rd2636raw
  rw [hold] at rd2636
  have rd6637pre := evm_run rd2636 with [
    raw push2 ⟨2645⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6637⟩ (by native_decide) (by evm_ov)]
  have rd6637 := rd6637pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := old) (b := wad) (ret := ⟨2645⟩)
    (R := [wad, dst, src, ilk, ret] ++ R)
    (by simpa [old, slot, inner] using rd6637)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot, inner] using hover)
    (by simp [List.length_cons, List.length_append] at hov ⊢; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatFluxDestStoreReturn
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {dstGemNew wad dst src ilk ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨2645⟩
      (dstGemNew :: wad :: dst :: src :: ilk :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hdstClean : UInt256.land dst solcAddrMask = dst)
    (hperm : ee.perm = true)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret R
      (twoWordHashMem dst (solcMappingSlot ⟨4⟩ ilk)
        (twoWordHashMem ilk ⟨4⟩ mem))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (solcMappingSlot (solcMappingSlot ⟨4⟩ ilk) dst) dstGemNew) k' C' := by
  let inner := solcMappingSlot ⟨4⟩ ilk
  let slot := solcMappingSlot inner dst
  have rd2646 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2650pre := evm_run rd2646 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  have rd2650 := rd2650pre.mstore 0 (wordAt0Mem ilk mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2657pre := evm_run rd2650 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2657 := rd2657pre.mstore 0
    (twoWordHashMem ilk ⟨4⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2662pre := evm_run rd2657 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨4⟩ mem).readWithPadding 0 64))) =
        inner := by
    simpa [inner] using twoWordHashMem_solcMappingSlot ⟨4⟩ ilk hmem
  have rd2662 := rd2662pre.keccak256 0 inner (UInt256.ofNat 3)
    (by native_decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd2673raw := evm_run rd2662 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land dst
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        dst := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hdstClean
  have rd2673 := rd2673raw
  rw [hmask] at rd2673
  have rd2675pre := evm_run rd2673 with [
    raw dup8 (by native_decide) (by evm_ov)]
  have rd2675 := rd2675pre.mstore 0
    (wordAt0Mem dst (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2678pre := evm_run rd2675 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2678 := rd2678pre.mstore 0
    (twoWordHashMem dst inner (twoWordHashMem ilk ⟨4⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2682pre := evm_run rd2678 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have hmemInner : (twoWordHashMem ilk ⟨4⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨4⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem dst inner (twoWordHashMem ilk ⟨4⟩ mem)).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot inner dst hmemInner
  have rd2682 := rd2682pre.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2684raw⟩ := rd2682.sstore hperm (by native_decide)
    (by simp [List.length_cons] at hov ⊢; omega)
  have rd2684 := rd2684raw.pop (by native_decide) (by evm_ov)
  have rd2685 := rd2684.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [slot, inner] using rd2685.jump (by native_decide) hret (by evm_ov)⟩

theorem assignStorageRef_flux_src_gem {evm evm' : EVM.State} {I : ExecutionEnv}
    {srcGemNew : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hevm' :
      evm' = Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (fluxSrcGemSlot I) srcGemNew) :
    assignStorageRef? config
      { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew } evm .storage
      (gemRef (.var "ilk") (.var "src")) (.int (Int.ofNat srcGemNew.toNat)) =
      .ok ({ contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }, evm') := by
  have hstore :
      storageLocStore evm (wordLoc (fluxSrcGemSlot I)) (.int (Int.ofNat srcGemNew.toNat)) =
        some evm' := by
    rw [hevm']
    exact vatStorageLocStore_uint256 evm (fluxSrcGemSlot I) srcGemNew
  exact assignStorageRef_storage_scalar
    (hbase := fluxStoreSrcGemNew_gem I srcGemNew)
    (her := evalStorageRef_flux_src_gem_after_src evm I srcGemNew (by omega))
    (hty := fluxStorageType_src_gem I)
    (hloc := fluxStorageLayout_src_gem I)
    (hstore := hstore)

theorem assignStorageRef_flux_dst_gem {evm evm' : EVM.State} {I : ExecutionEnv}
    {srcGemNew dstGemNew : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hevm' :
      evm' = Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (fluxDstGemSlot I) dstGemNew) :
    assignStorageRef? config
      { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew } evm .storage
      (gemRef (.var "ilk") (.var "dst")) (.int (Int.ofNat dstGemNew.toNat)) =
      .ok ({ contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew }, evm') := by
  have hstore :
      storageLocStore evm (wordLoc (fluxDstGemSlot I)) (.int (Int.ofNat dstGemNew.toNat)) =
        some evm' := by
    rw [hevm']
    exact vatStorageLocStore_uint256 evm (fluxDstGemSlot I) dstGemNew
  exact assignStorageRef_storage_scalar
    (hbase := fluxStoreDstGemNew_gem I srcGemNew dstGemNew)
    (her := evalStorageRef_flux_dst_gem_after_dst evm I srcGemNew dstGemNew (by omega))
    (hty := fluxStorageType_dst_gem I)
    (hloc := fluxStorageLayout_dst_gem I)
    (hstore := hstore)

theorem fluxEvalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem fluxEvalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem fluxEvalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

set_option maxHeartbeats 1000000 in
theorem vatFluxSourceOk
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz132 : 132 ≤ I.calldata.size) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let srcOld := vatSlotWord (fluxSrcGemSlot I) σ_solm I
    let srcGemNew := UInt256.sub srcOld (fluxWadWord I)
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (fluxSrcGemSlot I) srcGemNew
    let dstOld := Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (fluxDstGemSlot I)
    let dstGemNew := dstOld + fluxWadWord I
    evalExpr? config { contract := contract, locals := fluxStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool true) →
    (fluxWadWord I).toNat ≤ srcOld.toNat →
    dstOld.toNat + (fluxWadWord I).toNat < UInt256.size →
    ExecTransitionBody config contract evm0 (fluxStore I) fluxTransition.body
      (.returned { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew }
        (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
          (fluxDstGemSlot I) dstGemNew) none) := by
  intro evm0 srcOld srcGemNew evm1 dstOld dstGemNew hwish hsrcEnough hdstFit
  have hsrcLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (fluxSrcGemSlot I) = srcOld := by
    simp [evm0, srcOld, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hdstLoad :
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (fluxDstGemSlot I) = dstOld := by
    simp [dstOld]
  have hwad :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0 (.var "wad") =
        .ok (.int (Int.ofNat (fluxWadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := fluxStore I) (name := "wad")
      (value := fluxWadWord I) (fluxStore_get_wad I)
  have hsrc :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0
          (.storage (gemRef (.var "ilk") (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using evalExpr_flux_src_gem_old (evm := evm0) (I := I) hsz132
  have hsub :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0
          (sub256 (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad")) =
        .ok (.int (Int.ofNat srcGemNew.toNat)) :=
    vatEvalExpr_sub256_ok hsrc hwad (by simp [srcGemNew]) hsrcEnough
  have hsrcGemNewEval :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm0 (.var "srcGemNew") =
        .ok (.int (Int.ofNat srcGemNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := fluxStoreSrcGemNew I srcGemNew)
      (name := "srcGemNew") (value := srcGemNew)
      (fluxStoreSrcGemNew_get_srcGemNew I srcGemNew)
  have hsrcAgain :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm0 (.storage (gemRef (.var "ilk") (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using
      evalExpr_flux_src_gem_after_src (evm := evm0) (I := I) srcGemNew hsz132
  have hsrcGemNewNat : srcGemNew.toNat = srcOld.toNat - (fluxWadWord I).toNat := by
    simp [srcGemNew, usub_toNat hsrcEnough]
  have hreqSub :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm0 (.binary .le (.var "srcGemNew")
            (.storage (gemRef (.var "ilk") (.var "src")))) =
        .ok (.bool true) :=
    vatEvalExpr_le_uint256_true hsrcGemNewEval hsrcAgain
      (by rw [hsrcGemNewNat]; omega)
  have hassignSrc :
      assignStorageRef? config
        { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew } evm0 .storage
        (gemRef (.var "ilk") (.var "src")) (.int (Int.ofNat srcGemNew.toNat)) =
        .ok ({ contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }, evm1) :=
    assignStorageRef_flux_src_gem (evm := evm0) (evm' := evm1) (I := I)
      (srcGemNew := srcGemNew) hsz132 (by simp [evm1])
  have hwadAfterSrc :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm1 (.var "wad") =
        .ok (.int (Int.ofNat (fluxWadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm1) (locals := fluxStoreSrcGemNew I srcGemNew)
      (name := "wad") (value := fluxWadWord I)
      (fluxStoreSrcGemNew_get_wad I srcGemNew)
  have hdst :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm1 (.storage (gemRef (.var "ilk") (.var "dst"))) =
        .ok (.int (Int.ofNat dstOld.toNat)) := by
    simpa [hdstLoad] using
      evalExpr_flux_dst_gem_after_src (evm := evm1) (I := I) srcGemNew hsz132
  have hadd :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm1 (add256 (.storage (gemRef (.var "ilk") (.var "dst"))) (.var "wad")) =
        .ok (.int (Int.ofNat dstGemNew.toNat)) :=
    fluxEvalExpr_add256_ok hdst hwadAfterSrc (by simp [dstGemNew]) hdstFit
  have hdstGemNewEval :
      evalExpr? config { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew }
          evm1 (.var "dstGemNew") =
        .ok (.int (Int.ofNat dstGemNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm1)
      (locals := fluxStoreDstGemNew I srcGemNew dstGemNew)
      (name := "dstGemNew") (value := dstGemNew)
      (fluxStoreDstGemNew_get_dstGemNew I srcGemNew dstGemNew)
  have hdstAgain :
      evalExpr? config { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew }
          evm1 (.storage (gemRef (.var "ilk") (.var "dst"))) =
        .ok (.int (Int.ofNat dstOld.toNat)) := by
    simpa [hdstLoad] using
      evalExpr_flux_dst_gem_after_dst (evm := evm1) (I := I) srcGemNew dstGemNew hsz132
  have hdstGemNewNat : dstGemNew.toNat = dstOld.toNat + (fluxWadWord I).toNat := by
    rw [show dstGemNew = dstOld + fluxWadWord I by simp [dstGemNew]]
    rw [uadd_toNat, Nat.mod_eq_of_lt hdstFit]
  have hreqAdd :
      evalExpr? config { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew }
          evm1 (.binary .ge (.var "dstGemNew")
            (.storage (gemRef (.var "ilk") (.var "dst")))) =
        .ok (.bool true) :=
    fluxEvalExpr_ge_uint256_true hdstGemNewEval hdstAgain
      (by rw [hdstGemNewNat]; omega)
  have hassignDst :
      assignStorageRef? config
        { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew } evm1 .storage
        (gemRef (.var "ilk") (.var "dst")) (.int (Int.ofNat dstGemNew.toNat)) =
        .ok ({ contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew },
          Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
            (fluxDstGemSlot I) dstGemNew) :=
    assignStorageRef_flux_dst_gem (evm := evm1)
      (evm' := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (fluxDstGemSlot I) dstGemNew)
      (I := I) (srcGemNew := srcGemNew) (dstGemNew := dstGemNew) hsz132 rfl
  have hblock :
      ExecBlock config { contract := contract, locals := fluxStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcGemNew" (.storage (gemRef (.var "ilk") (.var "src")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew") ] ++
          checkedAddUintInto "dstGemNew" (.storage (gemRef (.var "ilk") (.var "dst")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ])
        (.ok { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew }
          (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
            (fluxDstGemSlot I) dstGemNew)) := by
    change ExecBlock config { contract := contract, locals := fluxStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcGemNew" (some uint256)
          (sub256 (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad")),
        .require (.binary .le (.var "srcGemNew")
          (.storage (gemRef (.var "ilk") (.var "src")))),
        .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew"),
        .letDecl "dstGemNew" (some uint256)
          (add256 (.storage (gemRef (.var "ilk") (.var "dst"))) (.var "wad")),
        .require (.binary .ge (.var "dstGemNew")
          (.storage (gemRef (.var "ilk") (.var "dst")))),
        .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ]
      (.ok { contract := contract, locals := fluxStoreDstGemNew I srcGemNew dstGemNew }
        (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
          (fluxDstGemSlot I) dstGemNew))
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSub) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hsrcGemNewEval hassignSrc) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hadd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAdd) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hdstGemNewEval hassignDst) ExecBlock.nil
  simpa [ExecTransitionBody, fluxTransition, evm0, evm1, nonpayable,
    checkedSubUintInto, checkedAddUintInto, List.append_assoc] using
    ExecFuncBody.execBlockOK hblock

theorem vatFluxSourceRevertWish
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    evalExpr? config { contract := contract, locals := fluxStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool false) →
    ExecTransitionBody config contract evm0 (fluxStore I) fluxTransition.body .reverted := by
  intro evm0 hwish
  have hblock :
      ExecBlock config { contract := contract, locals := fluxStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcGemNew" (.storage (gemRef (.var "ilk") (.var "src")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew") ] ++
          checkedAddUintInto "dstGemNew" (.storage (gemRef (.var "ilk") (.var "dst")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := fluxStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcGemNew" (some uint256)
          (sub256 (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad")),
        .require (.binary .le (.var "srcGemNew")
          (.storage (gemRef (.var "ilk") (.var "src")))),
        .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew"),
        .letDecl "dstGemNew" (some uint256)
          (add256 (.storage (gemRef (.var "ilk") (.var "dst"))) (.var "wad")),
        .require (.binary .ge (.var "dstGemNew")
          (.storage (gemRef (.var "ilk") (.var "dst")))),
        .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hwish)
  simpa [ExecTransitionBody, fluxTransition, evm0, nonpayable, checkedSubUintInto,
    checkedAddUintInto, List.append_assoc] using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem vatFluxSourceRevertSrcUnderflow
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz132 : 132 ≤ I.calldata.size) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let srcOld := vatSlotWord (fluxSrcGemSlot I) σ_solm I
    evalExpr? config { contract := contract, locals := fluxStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool true) →
    srcOld.toNat < (fluxWadWord I).toNat →
    ExecTransitionBody config contract evm0 (fluxStore I) fluxTransition.body .reverted := by
  intro evm0 srcOld hwish hunder
  have hsrcLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (fluxSrcGemSlot I) = srcOld := by
    simp [evm0, srcOld, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hwad :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0 (.var "wad") =
        .ok (.int (Int.ofNat (fluxWadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := fluxStore I) (name := "wad")
      (value := fluxWadWord I) (fluxStore_get_wad I)
  have hsrc :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0
          (.storage (gemRef (.var "ilk") (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using evalExpr_flux_src_gem_old (evm := evm0) (I := I) hsz132
  have hsub :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0
          (sub256 (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad")) = .revert :=
    vatEvalExpr_sub256_revert hsrc hwad hunder
  have hblock :
      ExecBlock config { contract := contract, locals := fluxStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcGemNew" (.storage (gemRef (.var "ilk") (.var "src")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew") ] ++
          checkedAddUintInto "dstGemNew" (.storage (gemRef (.var "ilk") (.var "dst")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := fluxStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcGemNew" (some uint256)
          (sub256 (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad")),
        .require (.binary .le (.var "srcGemNew")
          (.storage (gemRef (.var "ilk") (.var "src")))),
        .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew"),
        .letDecl "dstGemNew" (some uint256)
          (add256 (.storage (gemRef (.var "ilk") (.var "dst"))) (.var "wad")),
        .require (.binary .ge (.var "dstGemNew")
          (.storage (gemRef (.var "ilk") (.var "dst")))),
        .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hsub)
  simpa [ExecTransitionBody, fluxTransition, evm0, nonpayable, checkedSubUintInto,
    checkedAddUintInto, List.append_assoc] using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem vatFluxSourceRevertDstOverflow
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz132 : 132 ≤ I.calldata.size) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let srcOld := vatSlotWord (fluxSrcGemSlot I) σ_solm I
    let srcGemNew := UInt256.sub srcOld (fluxWadWord I)
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (fluxSrcGemSlot I) srcGemNew
    let dstOld := Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (fluxDstGemSlot I)
    evalExpr? config { contract := contract, locals := fluxStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool true) →
    (fluxWadWord I).toNat ≤ srcOld.toNat →
    UInt256.size ≤ dstOld.toNat + (fluxWadWord I).toNat →
    ExecTransitionBody config contract evm0 (fluxStore I) fluxTransition.body .reverted := by
  intro evm0 srcOld srcGemNew evm1 dstOld hwish hsrcEnough hover
  have hsrcLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (fluxSrcGemSlot I) = srcOld := by
    simp [evm0, srcOld, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hdstLoad :
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (fluxDstGemSlot I) = dstOld := by
    simp [dstOld]
  have hwad :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0 (.var "wad") =
        .ok (.int (Int.ofNat (fluxWadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := fluxStore I) (name := "wad")
      (value := fluxWadWord I) (fluxStore_get_wad I)
  have hsrc :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0
          (.storage (gemRef (.var "ilk") (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using evalExpr_flux_src_gem_old (evm := evm0) (I := I) hsz132
  have hsub :
      evalExpr? config { contract := contract, locals := fluxStore I } evm0
          (sub256 (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad")) =
        .ok (.int (Int.ofNat srcGemNew.toNat)) :=
    vatEvalExpr_sub256_ok hsrc hwad (by simp [srcGemNew]) hsrcEnough
  have hsrcGemNewEval :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm0 (.var "srcGemNew") =
        .ok (.int (Int.ofNat srcGemNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := fluxStoreSrcGemNew I srcGemNew)
      (name := "srcGemNew") (value := srcGemNew)
      (fluxStoreSrcGemNew_get_srcGemNew I srcGemNew)
  have hsrcAgain :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm0 (.storage (gemRef (.var "ilk") (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using
      evalExpr_flux_src_gem_after_src (evm := evm0) (I := I) srcGemNew hsz132
  have hsrcGemNewNat : srcGemNew.toNat = srcOld.toNat - (fluxWadWord I).toNat := by
    simp [srcGemNew, usub_toNat hsrcEnough]
  have hreqSub :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm0 (.binary .le (.var "srcGemNew")
            (.storage (gemRef (.var "ilk") (.var "src")))) =
        .ok (.bool true) :=
    vatEvalExpr_le_uint256_true hsrcGemNewEval hsrcAgain
      (by rw [hsrcGemNewNat]; omega)
  have hassignSrc :
      assignStorageRef? config
        { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew } evm0 .storage
        (gemRef (.var "ilk") (.var "src")) (.int (Int.ofNat srcGemNew.toNat)) =
        .ok ({ contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }, evm1) :=
    assignStorageRef_flux_src_gem (evm := evm0) (evm' := evm1) (I := I)
      (srcGemNew := srcGemNew) hsz132 (by simp [evm1])
  have hwadAfterSrc :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm1 (.var "wad") =
        .ok (.int (Int.ofNat (fluxWadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm1) (locals := fluxStoreSrcGemNew I srcGemNew)
      (name := "wad") (value := fluxWadWord I)
      (fluxStoreSrcGemNew_get_wad I srcGemNew)
  have hdst :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm1 (.storage (gemRef (.var "ilk") (.var "dst"))) =
        .ok (.int (Int.ofNat dstOld.toNat)) := by
    simpa [hdstLoad] using
      evalExpr_flux_dst_gem_after_src (evm := evm1) (I := I) srcGemNew hsz132
  have hadd :
      evalExpr? config { contract := contract, locals := fluxStoreSrcGemNew I srcGemNew }
          evm1 (add256 (.storage (gemRef (.var "ilk") (.var "dst"))) (.var "wad")) =
        .revert :=
    fluxEvalExpr_add256_revert hdst hwadAfterSrc hover
  have hblock :
      ExecBlock config { contract := contract, locals := fluxStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcGemNew" (.storage (gemRef (.var "ilk") (.var "src")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew") ] ++
          checkedAddUintInto "dstGemNew" (.storage (gemRef (.var "ilk") (.var "dst")))
            (.var "wad") ++
          [ .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := fluxStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcGemNew" (some uint256)
          (sub256 (.storage (gemRef (.var "ilk") (.var "src"))) (.var "wad")),
        .require (.binary .le (.var "srcGemNew")
          (.storage (gemRef (.var "ilk") (.var "src")))),
        .assign .storage (gemRef (.var "ilk") (.var "src")) (.var "srcGemNew"),
        .letDecl "dstGemNew" (some uint256)
          (add256 (.storage (gemRef (.var "ilk") (.var "dst"))) (.var "wad")),
        .require (.binary .ge (.var "dstGemNew")
          (.storage (gemRef (.var "ilk") (.var "dst")))),
        .assign .storage (gemRef (.var "ilk") (.var "dst")) (.var "dstGemNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSub) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hsrcGemNewEval hassignSrc) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)
  simpa [ExecTransitionBody, fluxTransition, evm0, nonpayable, checkedSubUintInto,
    checkedAddUintInto, List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem decodeABIValues_bytes32_address_address_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32) :
    decodeABIValues? [bytes32, addr, addr, uint256] bytes 0 0 128 128 DecodeMode.legacySolc05 =
      some
        ([ .fixedBytes bytes32Width (bytes.take 32),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
           .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat) ],
         128) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hge64 : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  have hge96 : 32 ≤ bytes.length - 96 := by
    rw [List.length_take, List.length_drop] at hlen96
    omega
  have htakeBytes32 :
      List.take (↑bytes32Width + 1) (List.take 32 bytes) = List.take 32 bytes := by
    simp [bytes32Width]
  have hltWord96 :
      ↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val < EVM.wordModulus := by
    change (ABI.bytesToWord ((bytes.drop 96).take 32)).val.val < EVM.twoPow 256
    exact (ABI.bytesToWord ((bytes.drop 96).take 32)).val.isLt
  have hmod96Val :
      (↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val) % EVM.wordModulus =
        ↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val :=
    Nat.mod_eq_of_lt hltWord96
  have hmod96Int :
      ((↑(↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val) : Int) %
          (↑EVM.wordModulus : Int)) =
        (↑(↑(ABI.bytesToWord ((bytes.drop 96).take 32)).val) : Int) := by
    exact Int.emod_eq_of_lt (Int.ofNat_nonneg _) (by exact_mod_cast hltWord96)
  simp [decodeABIValues?, decodeABIValue?, readBytes?, readWord?, decodeABIWord?,
    bytes32, addr, uint256, bytes32Width, uint256Int, isDynamicABIType,
    staticABIEncodedSize?, hlen0, hlen32, hlen64, hlen96, htakeBytes32, hge32, hge64,
    hge96, UInt256.toNat, show EVM.twoPow 256 = EVM.wordModulus by rfl]
  rw [hmod96Int]

set_option maxHeartbeats 0 in
theorem decodeCalldata_legacyBytes32_address_address_uint256_ok {cd : ByteArray}
    {w x y z : Solm.Ident} (hsz132 : 132 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [w, x, y, z]
      [bytes32, addr, addr, uint256] cd =
      some (((((∅ : Store).insert w
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 100).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, uint256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 by native_decide]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 128)]
  rw [decodeABIValues_bytes32_address_address_uint256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake100)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword100]
  simp [decodeCalldata.insertValues]

set_option maxHeartbeats 0 in
theorem vatDecode_flux_ok {I : ExecutionEnv} (hsz132 : 132 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fluxTransition.params.map Param.name)
      (transitionSignature fluxTransition).paramTypes I.calldata = some (fluxStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "src", "dst", "wad"]
    [bytes32, addr, addr, uint256] I.calldata = _
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "src", "dst", "wad"]
    [bytes32, addr, addr, uint256] I.calldata = some (fluxStore I)
  simpa [fluxStore, fluxIlkValue, fluxSrcValue, fluxDstValue, fluxWadValue, fluxSrcWord,
    fluxDstWord, fluxWadWord, calldataWord] using
      decodeCalldata_legacyBytes32_address_address_uint256_ok
        (cd := I.calldata) (w := "ilk") (x := "src") (y := "dst") (z := "wad") hsz132

theorem vatDecode_flux_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132) :
    decodeCalldataWithMode config.abiDecodeMode (fluxTransition.params.map Param.name)
      (transitionSignature fluxTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "src", "dst", "wad"]
    [bytes32, addr, addr, uint256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "src", "dst", "wad"]
    [bytes32, addr, addr, uint256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, addr, uint256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 128)]

theorem vatDispatchFlux {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 8)) :
    dispatchMsg contract I.calldata = some fluxTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fluxTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes]
  native_decide

theorem vatReachFluxBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 8)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨757⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x6111be2e⟩ :=
    vatSelWord_eq_of_beq I hsz 0x61 0x11 0xbe 0x2e ⟨0x6111be2e⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms321Body 1 (by omega) ⟨757⟩ hcode hwv hsz hsize
    hroot hlow hlowhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatFluxX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨757⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2468⟩
        [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨757⟩) (ret := ⟨524⟩)
    (decoded := ⟨779⟩) (need := ⟨128⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz132) hsize)
  have rd780 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd781 := rd780.pop (by native_decide) (by evm_ov)
  have rd782 := rd781.dup1 (by native_decide) (by evm_ov)
  have rd783 := rd782.calldataload (by native_decide) (by evm_ov)
  have rd784 := rd783.swap1 (by native_decide) (by evm_ov)
  have rd786 := rd784.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd788 := rd786.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd790 := rd788.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd791 := rd790.shl (by native_decide) (by evm_ov)
  have rd792 := rd791.sub (by native_decide) (by evm_ov)
  have rd794 := rd792.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd795 := rd794.dup3 (by native_decide) (by evm_ov)
  have rd796 := rd795.add (by native_decide) (by evm_ov)
  have rd797 := rd796.calldataload (by native_decide) (by evm_ov)
  have rd798 := rd797.dup2 (by native_decide) (by evm_ov)
  have rd799 := rd798.and (by native_decide) (by evm_ov)
  have hsrcMask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32)) =
        fluxSrcMaskedWord I := by
    rw [show (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) = 36 by decide]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
  rw [hsrcMask] at rd799
  have rd800 := rd799.swap2 (by native_decide) (by evm_ov)
  have rd802 := rd800.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd803 := rd802.dup2 (by native_decide) (by evm_ov)
  have rd804 := rd803.add (by native_decide) (by evm_ov)
  have rd805 := rd804.calldataload (by native_decide) (by evm_ov)
  have rd806 := rd805.swap1 (by native_decide) (by evm_ov)
  have rd807 := rd806.swap2 (by native_decide) (by evm_ov)
  have rd808 := rd807.and (by native_decide) (by evm_ov)
  have hdstMask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32)) =
        fluxDstMaskedWord I := by
    rw [show (((⟨4⟩ : UInt256) + ⟨64⟩).toNat) = 68 by decide]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
  rw [hdstMask] at rd808
  have rd809 := rd808.swap1 (by native_decide) (by evm_ov)
  have rd811 := rd809.push1 ⟨96⟩ (by native_decide) (by evm_ov)
  have rd812 := rd811.add (by native_decide) (by evm_ov)
  have rd813 := rd812.calldataload (by native_decide) (by evm_ov)
  have rd816 := rd813.push2 ⟨2468⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [fluxWadWord, fluxDstMaskedWord, fluxSrcMaskedWord, fluxDstWord, fluxSrcWord,
      fluxIlkWord, calldataWord] using
      rd816.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem vatFluxX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨757⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 128
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨757⟩) (ret := ⟨524⟩)
    (decoded := ⟨779⟩) (need := ⟨128⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem vatFluxAuthorizedPath
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {k C : ℕ} {memWish : ByteArray}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz132 : 132 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some fluxTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fluxTransition.params.map Param.name)
        (transitionSignature fluxTransition).paramTypes I.calldata = some (fluxStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmemWish : memWish.size = 96)
    (hwishSolm :
      evalExpr? config
        { contract := contract, locals := fluxStore I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (wishExpr (.var "src") sender) = .ok (.bool true))
    (h2545 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2545⟩
      [fluxWadWord I, fluxDstMaskedWord I, fluxSrcMaskedWord I, fluxIlkWord I, ⟨524⟩,
        vatSelWord I]
      memWish (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hsrcWord :
      vatSlotWord (fluxSrcGemSlot I) σ_evm I =
        vatSlotWord (fluxSrcGemSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fluxSrcGemSlot I) ⟨0⟩
  let srcOldE := vatSlotWord (fluxSrcGemSlot I) σ_evm I
  let srcGemNew := UInt256.sub srcOldE (fluxWadWord I)
  by_cases hsrcUnder : srcOldE.toNat < (fluxWadWord I).toNat
  · have hbody :
        ExecTransitionBody config contract evm0 (fluxStore I) fluxTransition.body .reverted := by
      exact vatFluxSourceRevertSrcUnderflow
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hwv hsz132
        (by simpa [evm0] using hwishSolm)
        (by simpa [evm0, srcOldE, hsrcWord] using hsrcUnder)
    have hsrcUnderSolc :
        (solcSlotWord σ_evm I
          (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
            (fluxSrcMaskedWord I))).toNat < (fluxWadWord I).toNat := by
      simpa [srcOldE, vatSlotWord, fluxSrcGemSlot_eq I hsz132] using hsrcUnder
    have hrev := RD.vatFluxSourceSubRevert
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
      h2545 hmemWish hsrcUnderSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hsrcEnough : (fluxWadWord I).toNat ≤ srcOldE.toNat := le_of_not_gt hsrcUnder
    have hsrcEnoughSolc :
        (fluxWadWord I).toNat ≤
          (solcSlotWord σ_evm I
            (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
              (fluxSrcMaskedWord I))).toNat := by
      simpa [srcOldE, vatSlotWord, fluxSrcGemSlot_eq I hsz132] using hsrcEnough
    obtain ⟨_, _, h2590⟩ := RD.vatFluxSourceSubSuccess
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
      h2545 hmemWish hsrcEnoughSolc
    let memSrcSub :=
      twoWordHashMem (fluxSrcMaskedWord I)
        (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
        (twoWordHashMem (fluxIlkWord I) ⟨4⟩ memWish)
    have hmemSrcSub : memSrcSub.size = 96 := by
      dsimp [memSrcSub]
      apply twoWordHashMem_size_96
      apply twoWordHashMem_size_96
      exact hmemWish
    have hsrcClean : UInt256.land solcAddrMask (fluxSrcMaskedWord I) = fluxSrcMaskedWord I :=
      solcAddrMask_clean_left (fluxSrcMaskedWord_canonical I)
    obtain ⟨_, _, h2630⟩ := RD.vatFluxSourceStoreValue
      (h := h2590) hmemSrcSub hsrcClean hperm (by simp)
    let σSrcE := sstoreAccountMap I.codeOwner σ_evm (fluxSrcGemSlot I) srcGemNew
    let σSrcS := sstoreAccountMap I.codeOwner σ_solm (fluxSrcGemSlot I) srcGemNew
    have hsrcSlotEq :
        solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I)) (fluxSrcMaskedWord I) =
          fluxSrcGemSlot I := by
      exact (fluxSrcGemSlot_eq I hsz132).symm
    have hsrcValEq :
        UInt256.sub
            (solcSlotWord σ_evm I
              (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
                (fluxSrcMaskedWord I)))
            (fluxWadWord I) =
          srcGemNew := by
      simp [srcGemNew, srcOldE, vatSlotWord, fluxSrcGemSlot_eq I hsz132]
    have h2630Flux := h2630
    rw [hsrcSlotEq] at h2630Flux
    have hsrcValEqFlux :
        UInt256.sub (solcSlotWord σ_evm I (fluxSrcGemSlot I)) (fluxWadWord I) =
          srcGemNew := by
      simp [srcGemNew, srcOldE, vatSlotWord]
    rw [hsrcValEqFlux] at h2630Flux
    have hAccountsSrc : accountMapEquiv σSrcE σSrcS := by
      simpa [σSrcE, σSrcS] using
        accountMapEquiv_sstoreAccountMap I.codeOwner (fluxSrcGemSlot I) srcGemNew hAccounts
    have hdstWord :
        vatSlotWord (fluxDstGemSlot I) σSrcE I =
          vatSlotWord (fluxDstGemSlot I) σSrcS I :=
      accountMapEquiv_storage_findD hAccountsSrc I.codeOwner (fluxDstGemSlot I) ⟨0⟩
    let dstOldE := vatSlotWord (fluxDstGemSlot I) σSrcE I
    let dstGemNew := dstOldE + fluxWadWord I
    have hdstSlotEq :
        solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I)) (fluxDstMaskedWord I) =
          fluxDstGemSlot I := by
      exact (fluxDstGemSlot_eq I hsz132).symm
    have hdstClean : UInt256.land (fluxDstMaskedWord I) solcAddrMask = fluxDstMaskedWord I := by
      rw [u256_land_comm]
      exact solcAddrMask_clean_left (fluxDstMaskedWord_canonical I)
    have hsrcGemNewSolm :
        UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I) (fluxWadWord I) =
          srcGemNew := by
      simp [srcGemNew, srcOldE, hsrcWord]
    have hloadDstSolm :
        Solm.EVM.storageLoad
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
              (fluxSrcGemSlot I)
              (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                (fluxWadWord I)))
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
              (fluxSrcGemSlot I)
              (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                (fluxWadWord I))).executionEnv.codeOwner
            (fluxDstGemSlot I) =
          vatSlotWord (fluxDstGemSlot I) σSrcS I := by
      rw [hsrcGemNewSolm]
      simp [evm0, σSrcS, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
        storageStore_accountMap, vatSlotWord, solcSlotWord]
    by_cases hdstOverflow : UInt256.size ≤ dstOldE.toNat + (fluxWadWord I).toNat
    · have hdstOverflowSolm :
          UInt256.size ≤
            (Solm.EVM.storageLoad
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I)))
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I))).executionEnv.codeOwner
                (fluxDstGemSlot I)).toNat + (fluxWadWord I).toNat := by
        rw [hloadDstSolm]
        have htmp :
            UInt256.size ≤
              (vatSlotWord (fluxDstGemSlot I) σSrcE I).toNat +
                (fluxWadWord I).toNat := by
          simpa [dstOldE] using hdstOverflow
        rw [hdstWord] at htmp
        exact htmp
      have hbody :
          ExecTransitionBody config contract evm0 (fluxStore I) fluxTransition.body
            .reverted := by
        exact vatFluxSourceRevertDstOverflow
          (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hwv hsz132
          (by simpa [evm0] using hwishSolm)
          (by simpa [srcOldE, hsrcWord] using hsrcEnough)
          hdstOverflowSolm
      have hdstOverflowSolc :
          UInt256.size ≤
            (solcSlotWord σSrcE I
              (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
                (fluxDstMaskedWord I))).toNat + (fluxWadWord I).toNat := by
        simpa [dstOldE, vatSlotWord, σSrcE, fluxDstGemSlot_eq I hsz132] using hdstOverflow
      have hrev := RD.vatFluxDestAddRevert
        (h := h2630Flux)
        hmemSrcSub hdstClean hdstOverflowSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdstFit : dstOldE.toNat + (fluxWadWord I).toNat < UInt256.size :=
        Nat.lt_of_not_ge hdstOverflow
      have hdstFitSolc :
          (solcSlotWord σSrcE I
                (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
                  (fluxDstMaskedWord I))).toNat +
              (fluxWadWord I).toNat < UInt256.size := by
        simpa [dstOldE, vatSlotWord, σSrcE, fluxDstGemSlot_eq I hsz132] using hdstFit
      obtain ⟨_, _, h2645⟩ := RD.vatFluxDestAddSuccess
        (h := h2630Flux)
        hmemSrcSub hdstClean hdstFitSolc (by simp)
      have hdstValEq :
          solcSlotWord σSrcE I
                (solcMappingSlot (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
                  (fluxDstMaskedWord I)) +
              fluxWadWord I =
            dstGemNew := by
        simp [dstGemNew, dstOldE, vatSlotWord, fluxDstGemSlot_eq I hsz132]
      have h2645Flux := h2645
      rw [hdstValEq] at h2645Flux
      let memDestAdd :=
        wordAt0Mem (fluxDstMaskedWord I)
          (twoWordHashMem (fluxSrcMaskedWord I)
            (solcMappingSlot ⟨4⟩ (fluxIlkWord I))
            (twoWordHashMem (fluxIlkWord I) ⟨4⟩ memSrcSub))
      have hmemDestAdd : memDestAdd.size = 96 := by
        dsimp [memDestAdd]
        apply wordAt0Mem_size_96
        apply twoWordHashMem_size_96
        apply twoWordHashMem_size_96
        exact hmemSrcSub
      obtain ⟨_, _, hretPcRaw⟩ := RD.vatFluxDestStoreReturn
        (h := h2645Flux)
        hmemDestAdd hdstClean hperm (by jump_dest) (by simp)
      have hretPc := hretPcRaw
      rw [hdstSlotEq] at hretPc
      have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
      have hret :
          RDret vatBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (cA, sstoreAccountMap I.codeOwner σSrcE (fluxDstGemSlot I) dstGemNew)
            ByteArray.empty := by
        exact RD.stop hretPc' (by native_decide) (by simp)
      have hdstFitSolm :
          (Solm.EVM.storageLoad
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                (fluxSrcGemSlot I)
                (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                  (fluxWadWord I)))
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                (fluxSrcGemSlot I)
                (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                  (fluxWadWord I))).executionEnv.codeOwner
              (fluxDstGemSlot I)).toNat + (fluxWadWord I).toNat < UInt256.size := by
        rw [hloadDstSolm]
        have htmp :
            (vatSlotWord (fluxDstGemSlot I) σSrcE I).toNat +
                (fluxWadWord I).toNat < UInt256.size := by
          simpa [dstOldE] using hdstFit
        rw [hdstWord] at htmp
        exact htmp
      have hbody := vatFluxSourceOk
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hwv hsz132
        (by simpa [evm0] using hwishSolm)
        (by simpa [srcOldE, hsrcWord] using hsrcEnough)
        hdstFitSolm
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σSrcE (fluxDstGemSlot I) dstGemNew).1 =
            (Solm.EVM.storageStore
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I)))
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I))).executionEnv.codeOwner
                (fluxDstGemSlot I)
                ((Solm.EVM.storageLoad
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (fluxSrcGemSlot I)
                      (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                        (fluxWadWord I)))
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (fluxSrcGemSlot I)
                      (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                        (fluxWadWord I))).executionEnv.codeOwner
                    (fluxDstGemSlot I)) + fluxWadWord I)).createdAccounts := by
        simp [evm0, initState, storageStore_createdAccounts]
      have haccountsFinal :
          accountMapEquiv
            (cA, sstoreAccountMap I.codeOwner σSrcE (fluxDstGemSlot I) dstGemNew).2
            (Solm.EVM.storageStore
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I)))
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I))).executionEnv.codeOwner
                (fluxDstGemSlot I)
                ((Solm.EVM.storageLoad
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (fluxSrcGemSlot I)
                      (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                        (fluxWadWord I)))
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (fluxSrcGemSlot I)
                      (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                        (fluxWadWord I))).executionEnv.codeOwner
                    (fluxDstGemSlot I)) + fluxWadWord I)).accountMap := by
        have hdstGemNewSolm :
            (Solm.EVM.storageLoad
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I)))
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I))).executionEnv.codeOwner
                (fluxDstGemSlot I)) + fluxWadWord I =
              dstGemNew := by
          rw [hloadDstSolm]
          simp [dstGemNew, dstOldE, hdstWord]
        have hAccountsDst :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner σSrcE (fluxDstGemSlot I) dstGemNew)
              (sstoreAccountMap I.codeOwner σSrcS (fluxDstGemSlot I) dstGemNew) :=
          accountMapEquiv_sstoreAccountMap I.codeOwner (fluxDstGemSlot I) dstGemNew
            hAccountsSrc
        have hloadDstSolmOwner :
            Solm.EVM.storageLoad
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (fluxSrcGemSlot I)
                  (UInt256.sub (vatSlotWord (fluxSrcGemSlot I) σ_solm I)
                    (fluxWadWord I)))
                evm0.executionEnv.codeOwner
                (fluxDstGemSlot I) =
              vatSlotWord (fluxDstGemSlot I) σSrcS I := by
          simpa [storageStore_executionEnv] using hloadDstSolm
        have hdstGemNewSolmOwner :
            vatSlotWord (fluxDstGemSlot I) σSrcS I + fluxWadWord I = dstGemNew := by
          simp [dstGemNew, dstOldE, hdstWord]
        rw [storageStore_accountMap, storageStore_executionEnv]
        rw [hloadDstSolmOwner, hdstGemNewSolmOwner]
        rw [storageStore_accountMap]
        rw [hsrcGemNewSolm]
        change accountMapEquiv
          (sstoreAccountMap I.codeOwner σSrcE (fluxDstGemSlot I) dstGemNew)
          (sstoreAccountMap evm0.executionEnv.codeOwner σSrcS (fluxDstGemSlot I) dstGemNew)
        rw [show evm0.executionEnv.codeOwner = I.codeOwner by simp [evm0, initState]]
        exact hAccountsDst
      have henc : returnEquiv ByteArray.empty none fluxTransition.returnType := by
        rw [show fluxTransition.returnType = [] by rfl]
        exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccountsFinal henc

set_option maxHeartbeats 1000000 in
theorem vatFluxBodyCore : VatBodyTheorem 8 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 8) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fluxTransition :=
    vatDispatchFlux hsel
  have hreach := vatReachFluxBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz132 : 132 ≤ I.calldata.size
  · have hdecode := vatDecode_flux_ok (I := I) hsz132
    obtain ⟨_, _, hdecoded⟩ := vatFluxX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz132 hsize hreach
    obtain ⟨_, _, hloaded⟩ := RD.vatFluxWishLoaded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecoded
    let memWish :=
      twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (fluxSrcMaskedWord I))
        (twoWordHashMem (fluxSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)
    have hmemWish : memWish.size = 96 := by
      dsimp [memWish]
      apply twoWordHashMem_size_96
      apply twoWordHashMem_size_96
      exact solcFreePtrMem_size
    have hread64Wish : memWish.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
      dsimp [memWish]
      apply twoWordHashMem_read64
      · apply twoWordHashMem_size_96
        exact solcFreePtrMem_size
      · apply twoWordHashMem_read64
        · exact solcFreePtrMem_size
        · exact solcFreePtrMem_read64
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    by_cases hsrcEq : fluxSrcMaskedWord I = hopeSourceWord I
    · have hwishSolm :
          evalExpr? config { contract := contract, locals := fluxStore I } evm0
            (wishExpr (.var "src") sender) = .ok (.bool true) :=
        evalExpr_flux_wish_true_src (evm := evm0) (I := I)
          (by simp [evm0, initState]) hsrcEq
      have hwishEvm : fluxWishWord σ_evm I ≠ ⟨0⟩ :=
        fluxWishWord_true_src (σ := σ_evm) (I := I) hsrcEq
      obtain ⟨_, _, h2545⟩ := RD.vatFluxWishBranchOk hloaded hwishEvm
      exact vatFluxAuthorizedPath
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hperm hwv hsz132
        hdispatch hdecode hAccounts hmemWish
        (by simpa [evm0] using hwishSolm) h2545
    · by_cases hcanEvm : vatSlotWord (fluxWishSlot I) σ_evm I = ⟨1⟩
      · have hcanSolm :
            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (fluxWishSlot I) = ⟨1⟩ := by
          have hcanWord :
              vatSlotWord (fluxWishSlot I) σ_evm I =
                vatSlotWord (fluxWishSlot I) σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (fluxWishSlot I) ⟨0⟩
          rw [hcanWord] at hcanEvm
          simpa [evm0, initState, vatSlotWord, solcSlotWord, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage] using hcanEvm
        have hwishSolm :
            evalExpr? config { contract := contract, locals := fluxStore I } evm0
              (wishExpr (.var "src") sender) = .ok (.bool true) :=
          evalExpr_flux_wish_true_can (evm := evm0) (I := I)
            (by simp [evm0, initState]) hsrcEq hcanSolm
        have hwishEvm : fluxWishWord σ_evm I ≠ ⟨0⟩ :=
          fluxWishWord_true_can (σ := σ_evm) (I := I) hcanEvm
        obtain ⟨_, _, h2545⟩ := RD.vatFluxWishBranchOk hloaded hwishEvm
        exact vatFluxAuthorizedPath
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hperm hwv hsz132
          hdispatch hdecode hAccounts hmemWish
          (by simpa [evm0] using hwishSolm) h2545
      · have hcanSolm :
            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (fluxWishSlot I) ≠ ⟨1⟩ := by
          intro hbad
          apply hcanEvm
          have hcanWord :
              vatSlotWord (fluxWishSlot I) σ_evm I =
                vatSlotWord (fluxWishSlot I) σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (fluxWishSlot I) ⟨0⟩
          rw [hcanWord]
          simpa [evm0, initState, vatSlotWord, solcSlotWord, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage] using hbad
        have hwishSolm :
            evalExpr? config { contract := contract, locals := fluxStore I } evm0
              (wishExpr (.var "src") sender) = .ok (.bool false) :=
          evalExpr_flux_wish_false (evm := evm0) (I := I)
            (by simp [evm0, initState]) hsrcEq hcanSolm
        have hbody :
            ExecTransitionBody config contract evm0 (fluxStore I) fluxTransition.body
              .reverted :=
          vatFluxSourceRevertWish
            (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hwishSolm
        have hrev := RD.vatFluxWishBranchRevert hloaded hmemWish hread64Wish
          (fluxWishWord_false (σ := σ_evm) (I := I) hsrcEq hcanEvm)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 132 := Nat.lt_of_not_ge hsz132
    have hrev := vatFluxX_shortarg
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
      hsz4 hshort hsize hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (vatDecode_flux_none_short hsz4 hshort)


end Benchmarks.Dss.Vat
