import Benchmarks.Dss.Vat.Flux

namespace Benchmarks.Dss.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

/-! ## `move(address,address,uint256)` -/

abbrev moveSrcWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev moveSrcMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (moveSrcWord I)

abbrev moveDstWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev moveDstMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (moveDstWord I)

abbrev moveRadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev moveSrcValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (moveSrcWord I).toNat)

abbrev moveDstValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (moveDstWord I).toNat)

abbrev moveRadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (moveRadWord I).toNat)

abbrev moveStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "src" (moveSrcValue I)).insert "dst" (moveDstValue I)).insert
    "rad" (moveRadValue I)

abbrev moveSrcKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (moveSrcWord I).toNat)

abbrev moveDstKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (moveDstWord I).toNat)

abbrev moveSourceKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev moveSrcDaiEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "dai", steps := [.mindex (moveSrcKey I)] }

abbrev moveDstDaiEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "dai", steps := [.mindex (moveDstKey I)] }

abbrev moveWishEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "can", steps := [.mindex (moveSrcKey I), .mindex (moveSourceKey I)] }

def moveSrcDaiSlot (I : ExecutionEnv) : UInt256 :=
  daiSlot (moveSrcKey I)

def moveDstDaiSlot (I : ExecutionEnv) : UInt256 :=
  daiSlot (moveDstKey I)

def moveWishSlot (I : ExecutionEnv) : UInt256 :=
  canSlot (moveSrcKey I) (moveSourceKey I)

abbrev moveWishWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.eq (vatSlotWord (moveWishSlot I) σ I) ⟨1⟩)
    (UInt256.eq (moveSrcMaskedWord I) (hopeSourceWord I))

abbrev moveStoreSrcDaiNew (I : ExecutionEnv) (srcDaiNew : UInt256) : Store :=
  (moveStore I).insert "srcDaiNew" (.int (Int.ofNat srcDaiNew.toNat))

abbrev moveStoreDstDaiNew (I : ExecutionEnv) (srcDaiNew dstDaiNew : UInt256) : Store :=
  (moveStoreSrcDaiNew I srcDaiNew).insert "dstDaiNew" (.int (Int.ofNat dstDaiNew.toNat))

theorem moveStore_get_src (I : ExecutionEnv) :
    (moveStore I).get? "src" = some (moveSrcValue I) := by
  unfold moveStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem moveStore_get_dst (I : ExecutionEnv) :
    (moveStore I).get? "dst" = some (moveDstValue I) := by
  unfold moveStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem moveStore_get_rad (I : ExecutionEnv) :
    (moveStore I).get? "rad" = some (moveRadValue I) := by
  simp [moveStore]

theorem moveStore_index_src (I : ExecutionEnv) :
    (moveStore I)["src"] = moveSrcValue I := by
  unfold moveStore
  rw [Std.HashMap.getElem_insert]
  simp
  rw [Std.HashMap.getElem_insert]
  simp

theorem moveStore_dai (I : ExecutionEnv) :
    (moveStore I).get? "dai" = none := by
  unfold moveStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem moveStore_can (I : ExecutionEnv) :
    (moveStore I).get? "can" = none := by
  unfold moveStore
  repeat rw [store_get_ne _ _ (by native_decide)]
  simp

theorem moveStoreSrcDaiNew_get_rad (I : ExecutionEnv) (srcDaiNew : UInt256) :
    (moveStoreSrcDaiNew I srcDaiNew).get? "rad" = some (moveRadValue I) := by
  rw [moveStoreSrcDaiNew, store_get_ne _ _ (by native_decide), moveStore_get_rad]

theorem moveStoreSrcDaiNew_get_srcDaiNew (I : ExecutionEnv) (srcDaiNew : UInt256) :
    (moveStoreSrcDaiNew I srcDaiNew).get? "srcDaiNew" =
      some (.int (Int.ofNat srcDaiNew.toNat)) := by
  simp [moveStoreSrcDaiNew]

theorem moveStoreSrcDaiNew_get_dst (I : ExecutionEnv) (srcDaiNew : UInt256) :
    (moveStoreSrcDaiNew I srcDaiNew).get? "dst" = some (moveDstValue I) := by
  rw [moveStoreSrcDaiNew, store_get_ne _ _ (by native_decide), moveStore_get_dst]

theorem moveStoreSrcDaiNew_get_src (I : ExecutionEnv) (srcDaiNew : UInt256) :
    (moveStoreSrcDaiNew I srcDaiNew).get? "src" = some (moveSrcValue I) := by
  rw [moveStoreSrcDaiNew, store_get_ne _ _ (by native_decide), moveStore_get_src]

theorem moveStoreDstDaiNew_get_dstDaiNew (I : ExecutionEnv)
    (srcDaiNew dstDaiNew : UInt256) :
    (moveStoreDstDaiNew I srcDaiNew dstDaiNew).get? "dstDaiNew" =
      some (.int (Int.ofNat dstDaiNew.toNat)) := by
  simp [moveStoreDstDaiNew]

theorem moveStoreDstDaiNew_get_dst (I : ExecutionEnv) (srcDaiNew dstDaiNew : UInt256) :
    (moveStoreDstDaiNew I srcDaiNew dstDaiNew).get? "dst" = some (moveDstValue I) := by
  rw [moveStoreDstDaiNew, store_get_ne _ _ (by native_decide),
    moveStoreSrcDaiNew_get_dst]

theorem moveStoreSrcDaiNew_dai (I : ExecutionEnv) (srcDaiNew : UInt256) :
    (moveStoreSrcDaiNew I srcDaiNew).get? "dai" = none := by
  rw [moveStoreSrcDaiNew, store_get_ne _ _ (by native_decide), moveStore_dai]

theorem moveStoreDstDaiNew_dai (I : ExecutionEnv) (srcDaiNew dstDaiNew : UInt256) :
    (moveStoreDstDaiNew I srcDaiNew dstDaiNew).get? "dai" = none := by
  rw [moveStoreDstDaiNew, store_get_ne _ _ (by native_decide),
    moveStoreSrcDaiNew_dai]

theorem moveSrcDaiSlot_eq (I : ExecutionEnv) :
    moveSrcDaiSlot I = solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I) := by
  unfold moveSrcDaiSlot daiSlot moveSrcKey moveSrcMaskedWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem moveDstDaiSlot_eq (I : ExecutionEnv) :
    moveDstDaiSlot I = solcMappingSlot ⟨5⟩ (moveDstMaskedWord I) := by
  unfold moveDstDaiSlot daiSlot moveDstKey moveDstMaskedWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem moveWishSlot_eq (I : ExecutionEnv) :
    moveWishSlot I =
      solcMappingSlot (solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I)) (hopeSourceWord I) := by
  unfold moveWishSlot canSlot canOwnerSlot moveSrcKey moveSourceKey moveSrcMaskedWord
    hopeSourceWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem moveSrcMaskedWord_canonical (I : ExecutionEnv) :
    (moveSrcMaskedWord I).toNat < EVM.addressModulus := by
  unfold moveSrcMaskedWord
  rw [u256_land_comm solcAddrMask (moveSrcWord I)]
  exact solcAddrMask_result_canonical (moveSrcWord I)

theorem moveDstMaskedWord_canonical (I : ExecutionEnv) :
    (moveDstMaskedWord I).toNat < EVM.addressModulus := by
  unfold moveDstMaskedWord
  rw [u256_land_comm solcAddrMask (moveDstWord I)]
  exact solcAddrMask_result_canonical (moveDstWord I)

theorem evalStorageRef_move_src_dai (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := moveStore I } evm
      (daiRef (.var "src")) = .ok (moveSrcDaiEvaledRef I) := by
  simp [moveSrcDaiEvaledRef, moveSrcValue, moveSrcKey, daiRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?, moveStore_get_src]

theorem evalStorageRef_move_dst_dai_after_src (evm : EVM.State) (I : ExecutionEnv)
    (srcDaiNew : UInt256) :
    evalStorageRef config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
      evm (daiRef (.var "dst")) = .ok (moveDstDaiEvaledRef I) := by
  simp [moveDstDaiEvaledRef, moveDstValue, moveDstKey, daiRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    moveStoreSrcDaiNew_get_dst]

theorem evalStorageRef_move_src_dai_after_src (evm : EVM.State) (I : ExecutionEnv)
    (srcDaiNew : UInt256) :
    evalStorageRef config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
      evm (daiRef (.var "src")) = .ok (moveSrcDaiEvaledRef I) := by
  simp [moveSrcDaiEvaledRef, moveSrcValue, moveSrcKey, daiRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    moveStoreSrcDaiNew_get_src]

theorem evalStorageRef_move_dst_dai_after_dst (evm : EVM.State) (I : ExecutionEnv)
    (srcDaiNew dstDaiNew : UInt256) :
    evalStorageRef config
      { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew } evm
      (daiRef (.var "dst")) = .ok (moveDstDaiEvaledRef I) := by
  simp [moveDstDaiEvaledRef, moveDstValue, moveDstKey, daiRef, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, bind, pure, ← Std.HashMap.get?_eq_getElem?,
    moveStoreDstDaiNew_get_dst]

theorem evalStorageRef_move_can (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := moveStore I } evm
      (canRef (.var "src") sender) = .ok (moveWishEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, canRef, sender,
    envValue, moveWishEvaledRef, hsrc, moveSrcValue, moveSourceKey, moveSrcKey,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    moveStore_index_src]

theorem moveStorageType_src_dai (I : ExecutionEnv) :
    storageTypeAt? contract.storage (moveSrcDaiEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  change storageTypeAt? storageDecls (moveSrcDaiEvaledRef I) =
    some (.elem (.int uint256Int))
  simp [moveSrcDaiEvaledRef, storageTypeAt?, storageTypeStep?, storageDecls, uint256St]

theorem moveStorageType_dst_dai (I : ExecutionEnv) :
    storageTypeAt? contract.storage (moveDstDaiEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  change storageTypeAt? storageDecls (moveDstDaiEvaledRef I) =
    some (.elem (.int uint256Int))
  simp [moveDstDaiEvaledRef, storageTypeAt?, storageTypeStep?, storageDecls, uint256St]

theorem moveStorageType_can (I : ExecutionEnv) :
    storageTypeAt? contract.storage (moveWishEvaledRef I) =
      some (.elem (.int uint256Int)) := by
  change storageTypeAt? storageDecls (moveWishEvaledRef I) = some (.elem (.int uint256Int))
  simp [moveWishEvaledRef, storageTypeAt?, storageTypeStep?, storageDecls, uint256St]

theorem moveStorageLayout_src_dai (I : ExecutionEnv) :
    config.storage.layout (moveSrcDaiEvaledRef I) =
      fun _ => some (wordLoc (moveSrcDaiSlot I)) := by
  funext evm
  change storageLayoutRaw (moveSrcDaiEvaledRef I) evm =
    some (wordLoc (moveSrcDaiSlot I))
  simp [storageLayoutRaw, moveSrcDaiEvaledRef, moveSrcDaiSlot]

theorem moveStorageLayout_dst_dai (I : ExecutionEnv) :
    config.storage.layout (moveDstDaiEvaledRef I) =
      fun _ => some (wordLoc (moveDstDaiSlot I)) := by
  funext evm
  change storageLayoutRaw (moveDstDaiEvaledRef I) evm =
    some (wordLoc (moveDstDaiSlot I))
  simp [storageLayoutRaw, moveDstDaiEvaledRef, moveDstDaiSlot]

theorem moveStorageLayout_can (I : ExecutionEnv) :
    config.storage.layout (moveWishEvaledRef I) =
      fun _ => some (wordLoc (moveWishSlot I)) := by
  funext evm
  change storageLayoutRaw (moveWishEvaledRef I) evm = some (wordLoc (moveWishSlot I))
  simp [storageLayoutRaw, moveWishEvaledRef, moveWishSlot]

theorem evalExpr_move_src_dai_old {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (.storage (daiRef (.var "src"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveSrcDaiSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := moveStore_dai I)
    (her := evalStorageRef_move_src_dai evm I)
    (hty := moveStorageType_src_dai I)
    (hloc := moveStorageLayout_src_dai I)
    (hload := vatStorageLocLoad_uint256 evm (moveSrcDaiSlot I))

theorem evalExpr_move_dst_dai_after_src {evm : EVM.State} {I : ExecutionEnv}
    (srcDaiNew : UInt256) :
    evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew } evm
      (.storage (daiRef (.var "dst"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveDstDaiSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := moveStoreSrcDaiNew_dai I srcDaiNew)
    (her := evalStorageRef_move_dst_dai_after_src evm I srcDaiNew)
    (hty := moveStorageType_dst_dai I)
    (hloc := moveStorageLayout_dst_dai I)
    (hload := vatStorageLocLoad_uint256 evm (moveDstDaiSlot I))

theorem evalExpr_move_src_dai_after_src {evm : EVM.State} {I : ExecutionEnv}
    (srcDaiNew : UInt256) :
    evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew } evm
      (.storage (daiRef (.var "src"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveSrcDaiSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := moveStoreSrcDaiNew_dai I srcDaiNew)
    (her := evalStorageRef_move_src_dai_after_src evm I srcDaiNew)
    (hty := moveStorageType_src_dai I)
    (hloc := moveStorageLayout_src_dai I)
    (hload := vatStorageLocLoad_uint256 evm (moveSrcDaiSlot I))

theorem evalExpr_move_dst_dai_after_dst {evm : EVM.State} {I : ExecutionEnv}
    (srcDaiNew dstDaiNew : UInt256) :
    evalExpr? config
      { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew } evm
      (.storage (daiRef (.var "dst"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveDstDaiSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := moveStoreDstDaiNew_dai I srcDaiNew dstDaiNew)
    (her := evalStorageRef_move_dst_dai_after_dst evm I srcDaiNew dstDaiNew)
    (hty := moveStorageType_dst_dai I)
    (hloc := moveStorageLayout_dst_dai I)
    (hload := vatStorageLocLoad_uint256 evm (moveDstDaiSlot I))

theorem evalExpr_move_can {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (.storage (canRef (.var "src") sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveWishSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (hbase := moveStore_can I)
    (her := evalStorageRef_move_can evm I hsrc)
    (hty := moveStorageType_can I)
    (hloc := moveStorageLayout_can I)
    (hload := vatStorageLocLoad_uint256 evm (moveWishSlot I))

theorem evalExpr_move_src_sender_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (heq : moveSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (.binary .eq (.var "src") sender) = .ok (.bool true) := by
  have hsrcValue :
      moveSrcValue I = .address evm.executionEnv.source := by
    rw [moveSrcValue, solcAddressValue_masked (moveSrcWord I)]
    change Value.address (AccountAddress.ofNat (moveSrcMaskedWord I).toNat) =
      Value.address evm.executionEnv.source
    rw [heq]
    rw [fluxHopeSource_ofNat I, ← hsrc]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [moveStore_get_src I, hsrcValue]
  simp [evalBinaryOp?]

theorem evalExpr_move_src_sender_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hne : moveSrcMaskedWord I ≠ hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (.binary .eq (.var "src") sender) = .ok (.bool false) := by
  have hneValue :
      moveSrcValue I ≠ .address evm.executionEnv.source := by
    intro hval
    have hmasked :
        Value.address (AccountAddress.ofNat (moveSrcMaskedWord I).toNat) =
        Value.address evm.executionEnv.source := by
      rw [← solcAddressValue_masked (moveSrcWord I), ← hval]
    have hword : moveSrcMaskedWord I = hopeSourceWord I := by
      apply u256_inj
      have haddrs :
          AccountAddress.ofNat (moveSrcMaskedWord I).toNat = evm.executionEnv.source := by
        injection hmasked with haddr
      have hnat := congrArg Fin.val haddrs
      unfold AccountAddress.ofNat at hnat
      change (moveSrcMaskedWord I).toNat % EVM.addressModulus =
        evm.executionEnv.source.val at hnat
      rw [Nat.mod_eq_of_lt (moveSrcMaskedWord_canonical I)] at hnat
      rw [hopeSourceWord_toNat, ← hsrc]
      exact hnat
    exact hne hword
  have hbeq : (moveSrcValue I == Value.address evm.executionEnv.source) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hneValue (beq_iff_eq.mp hb)
  simp only [evalExpr?, sender, envValue, EvalResult.bind, EvalResult.ofOption, bind, pure]
  rw [moveStore_get_src I]
  simp [evalBinaryOp?, hbeq]

theorem evalExpr_move_can_eq_true {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_move_can (evm := evm) (I := I) hsrc, hcan,
    show (⟨1⟩ : UInt256).toNat = 1 by decide]

theorem evalExpr_move_can_eq_false {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (.binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1)) =
      .ok (.bool false) := by
  have hneNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveWishSlot I)).toNat ≠ 1 := by
    intro hnat
    apply hcan
    apply u256_inj
    rw [hnat]
    decide
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
    evalExpr_move_can (evm := evm) (I := I) hsrc, hneNat]

theorem evalExpr_move_wish_true_src {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (heq : moveSrcMaskedWord I = hopeSourceWord I) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact fluxEvalExpr_or_true_left
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_move_src_sender_eq_true (evm := evm) (I := I) hsrc heq)

theorem evalExpr_move_wish_true_can {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hne : moveSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveWishSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (wishExpr (.var "src") sender) = .ok (.bool true) := by
  exact fluxEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_move_src_sender_eq_false (evm := evm) (I := I) hsrc hne)
    (evalExpr_move_can_eq_true (evm := evm) (I := I) hsrc hcan)

theorem evalExpr_move_wish_false {evm : EVM.State} {I : ExecutionEnv}
    (hsrc : evm.executionEnv.source = I.source)
    (hne : moveSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (moveWishSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := moveStore I } evm
      (wishExpr (.var "src") sender) = .ok (.bool false) := by
  exact fluxEvalExpr_or_false_right
    (lhs := .binary .eq (.var "src") sender)
    (rhs := .binary .eq (.storage (canRef (.var "src") sender)) (.intLit 1))
    (evalExpr_move_src_sender_eq_false (evm := evm) (I := I) hsrc hne)
    (evalExpr_move_can_eq_false (evm := evm) (I := I) hsrc hcan)

theorem moveWishWord_true_src {σ : AccountMap} {I : ExecutionEnv}
    (heq : moveSrcMaskedWord I = hopeSourceWord I) :
    moveWishWord σ I ≠ ⟨0⟩ := by
  by_cases hcan : vatSlotWord (moveWishSlot I) σ I = ⟨1⟩
  · unfold moveWishWord
    rw [heq, hcan, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold moveWishWord
    rw [heq, u256_eq_refl, u256_eq_of_ne hcan]
    rw [u256_lor_comm, u256_lor_zero]
    exact one_ne_zero_uint

theorem moveWishWord_true_can {σ : AccountMap} {I : ExecutionEnv}
    (hcan : vatSlotWord (moveWishSlot I) σ I = ⟨1⟩) :
    moveWishWord σ I ≠ ⟨0⟩ := by
  by_cases hsrc : moveSrcMaskedWord I = hopeSourceWord I
  · unfold moveWishWord
    rw [hcan, hsrc, u256_eq_refl, u256_eq_refl]
    native_decide
  · unfold moveWishWord
    rw [hcan, u256_eq_refl, u256_eq_of_ne hsrc]
    rw [u256_lor_zero]
    exact one_ne_zero_uint

theorem moveWishWord_false {σ : AccountMap} {I : ExecutionEnv}
    (hne : moveSrcMaskedWord I ≠ hopeSourceWord I)
    (hcan : vatSlotWord (moveWishSlot I) σ I ≠ ⟨1⟩) :
    moveWishWord σ I = ⟨0⟩ := by
  unfold moveWishWord
  rw [u256_eq_of_ne hcan, u256_eq_of_ne hne]
  rfl

theorem assignStorageRef_move_src_dai {evm evm' : EVM.State} {I : ExecutionEnv}
    {srcDaiNew : UInt256}
    (hevm' :
      evm' = Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (moveSrcDaiSlot I) srcDaiNew) :
    assignStorageRef? config
      { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew } evm .storage
      (daiRef (.var "src")) (.int (Int.ofNat srcDaiNew.toNat)) =
      .ok ({ contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }, evm') := by
  have hstore :
      storageLocStore evm (wordLoc (moveSrcDaiSlot I)) (.int (Int.ofNat srcDaiNew.toNat)) =
        some evm' := by
    rw [hevm']
    exact vatStorageLocStore_uint256 evm (moveSrcDaiSlot I) srcDaiNew
  exact assignStorageRef_storage_scalar
    (hbase := moveStoreSrcDaiNew_dai I srcDaiNew)
    (her := evalStorageRef_move_src_dai_after_src evm I srcDaiNew)
    (hty := moveStorageType_src_dai I)
    (hloc := moveStorageLayout_src_dai I)
    (hstore := hstore)

theorem assignStorageRef_move_dst_dai {evm evm' : EVM.State} {I : ExecutionEnv}
    {srcDaiNew dstDaiNew : UInt256}
    (hevm' :
      evm' = Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (moveDstDaiSlot I) dstDaiNew) :
    assignStorageRef? config
      { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew } evm .storage
      (daiRef (.var "dst")) (.int (Int.ofNat dstDaiNew.toNat)) =
      .ok ({ contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew },
        evm') := by
  have hstore :
      storageLocStore evm (wordLoc (moveDstDaiSlot I)) (.int (Int.ofNat dstDaiNew.toNat)) =
        some evm' := by
    rw [hevm']
    exact vatStorageLocStore_uint256 evm (moveDstDaiSlot I) dstDaiNew
  exact assignStorageRef_storage_scalar
    (hbase := moveStoreDstDaiNew_dai I srcDaiNew dstDaiNew)
    (her := evalStorageRef_move_dst_dai_after_dst evm I srcDaiNew dstDaiNew)
    (hty := moveStorageType_dst_dai I)
    (hloc := moveStorageLayout_dst_dai I)
    (hstore := hstore)

set_option maxHeartbeats 1000000 in
theorem vatMoveSourceOk
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let srcOld := vatSlotWord (moveSrcDaiSlot I) σ_solm I
    let srcDaiNew := UInt256.sub srcOld (moveRadWord I)
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (moveSrcDaiSlot I) srcDaiNew
    let dstOld := Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (moveDstDaiSlot I)
    let dstDaiNew := dstOld + moveRadWord I
    evalExpr? config { contract := contract, locals := moveStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool true) →
    (moveRadWord I).toNat ≤ srcOld.toNat →
    dstOld.toNat + (moveRadWord I).toNat < UInt256.size →
    ExecTransitionBody config contract evm0 (moveStore I) moveTransition.body
      (.returned { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew }
        (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
          (moveDstDaiSlot I) dstDaiNew) none) := by
  intro evm0 srcOld srcDaiNew evm1 dstOld dstDaiNew hwish hsrcEnough hdstFit
  have hsrcLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (moveSrcDaiSlot I) = srcOld := by
    simp [evm0, srcOld, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hdstLoad :
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (moveDstDaiSlot I) = dstOld := by
    simp [dstOld]
  have hrad :
      evalExpr? config { contract := contract, locals := moveStore I } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (moveRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := moveStore I) (name := "rad")
      (value := moveRadWord I) (moveStore_get_rad I)
  have hsrc :
      evalExpr? config { contract := contract, locals := moveStore I } evm0
          (.storage (daiRef (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using evalExpr_move_src_dai_old (evm := evm0) (I := I)
  have hsub :
      evalExpr? config { contract := contract, locals := moveStore I } evm0
          (sub256 (.storage (daiRef (.var "src"))) (.var "rad")) =
        .ok (.int (Int.ofNat srcDaiNew.toNat)) :=
    vatEvalExpr_sub256_ok hsrc hrad (by simp [srcDaiNew]) hsrcEnough
  have hsrcDaiNewEval :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm0 (.var "srcDaiNew") =
        .ok (.int (Int.ofNat srcDaiNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := moveStoreSrcDaiNew I srcDaiNew)
      (name := "srcDaiNew") (value := srcDaiNew)
      (moveStoreSrcDaiNew_get_srcDaiNew I srcDaiNew)
  have hsrcAgain :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm0 (.storage (daiRef (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using
      evalExpr_move_src_dai_after_src (evm := evm0) (I := I) srcDaiNew
  have hsrcDaiNewNat : srcDaiNew.toNat = srcOld.toNat - (moveRadWord I).toNat := by
    simp [srcDaiNew, usub_toNat hsrcEnough]
  have hreqSub :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm0 (.binary .le (.var "srcDaiNew")
            (.storage (daiRef (.var "src")))) =
        .ok (.bool true) :=
    vatEvalExpr_le_uint256_true hsrcDaiNewEval hsrcAgain
      (by rw [hsrcDaiNewNat]; omega)
  have hassignSrc :
      assignStorageRef? config
        { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew } evm0 .storage
        (daiRef (.var "src")) (.int (Int.ofNat srcDaiNew.toNat)) =
        .ok ({ contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }, evm1) :=
    assignStorageRef_move_src_dai (evm := evm0) (evm' := evm1) (I := I)
      (srcDaiNew := srcDaiNew) (by simp [evm1])
  have hradAfterSrc :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm1 (.var "rad") =
        .ok (.int (Int.ofNat (moveRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm1) (locals := moveStoreSrcDaiNew I srcDaiNew)
      (name := "rad") (value := moveRadWord I)
      (moveStoreSrcDaiNew_get_rad I srcDaiNew)
  have hdst :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm1 (.storage (daiRef (.var "dst"))) =
        .ok (.int (Int.ofNat dstOld.toNat)) := by
    simpa [hdstLoad] using
      evalExpr_move_dst_dai_after_src (evm := evm1) (I := I) srcDaiNew
  have hadd :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm1 (add256 (.storage (daiRef (.var "dst"))) (.var "rad")) =
        .ok (.int (Int.ofNat dstDaiNew.toNat)) :=
    fluxEvalExpr_add256_ok hdst hradAfterSrc (by simp [dstDaiNew]) hdstFit
  have hdstDaiNewEval :
      evalExpr? config { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew }
          evm1 (.var "dstDaiNew") =
        .ok (.int (Int.ofNat dstDaiNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm1)
      (locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew)
      (name := "dstDaiNew") (value := dstDaiNew)
      (moveStoreDstDaiNew_get_dstDaiNew I srcDaiNew dstDaiNew)
  have hdstAgain :
      evalExpr? config { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew }
          evm1 (.storage (daiRef (.var "dst"))) =
        .ok (.int (Int.ofNat dstOld.toNat)) := by
    simpa [hdstLoad] using
      evalExpr_move_dst_dai_after_dst (evm := evm1) (I := I) srcDaiNew dstDaiNew
  have hdstDaiNewNat : dstDaiNew.toNat = dstOld.toNat + (moveRadWord I).toNat := by
    rw [show dstDaiNew = dstOld + moveRadWord I by simp [dstDaiNew]]
    rw [uadd_toNat, Nat.mod_eq_of_lt hdstFit]
  have hreqAdd :
      evalExpr? config { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew }
          evm1 (.binary .ge (.var "dstDaiNew")
            (.storage (daiRef (.var "dst")))) =
        .ok (.bool true) :=
    fluxEvalExpr_ge_uint256_true hdstDaiNewEval hdstAgain
      (by rw [hdstDaiNewNat]; omega)
  have hassignDst :
      assignStorageRef? config
        { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew } evm1 .storage
        (daiRef (.var "dst")) (.int (Int.ofNat dstDaiNew.toNat)) =
        .ok ({ contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew },
          Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
            (moveDstDaiSlot I) dstDaiNew) :=
    assignStorageRef_move_dst_dai (evm := evm1)
      (evm' := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
        (moveDstDaiSlot I) dstDaiNew)
      (I := I) (srcDaiNew := srcDaiNew) (dstDaiNew := dstDaiNew) rfl
  have hblock :
      ExecBlock config { contract := contract, locals := moveStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcDaiNew" (.storage (daiRef (.var "src")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "src")) (.var "srcDaiNew") ] ++
          checkedAddUintInto "dstDaiNew" (.storage (daiRef (.var "dst")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ])
        (.ok { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew }
          (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
            (moveDstDaiSlot I) dstDaiNew)) := by
    change ExecBlock config { contract := contract, locals := moveStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcDaiNew" (some uint256)
          (sub256 (.storage (daiRef (.var "src"))) (.var "rad")),
        .require (.binary .le (.var "srcDaiNew")
          (.storage (daiRef (.var "src")))),
        .assign .storage (daiRef (.var "src")) (.var "srcDaiNew"),
        .letDecl "dstDaiNew" (some uint256)
          (add256 (.storage (daiRef (.var "dst"))) (.var "rad")),
        .require (.binary .ge (.var "dstDaiNew")
          (.storage (daiRef (.var "dst")))),
        .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ]
      (.ok { contract := contract, locals := moveStoreDstDaiNew I srcDaiNew dstDaiNew }
        (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
          (moveDstDaiSlot I) dstDaiNew))
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSub) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hsrcDaiNewEval hassignSrc) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hadd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAdd) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hdstDaiNewEval hassignDst) ExecBlock.nil
  simpa [ExecTransitionBody, moveTransition, evm0, evm1, nonpayable,
    checkedSubUintInto, checkedAddUintInto, List.append_assoc] using
    ExecFuncBody.execBlockOK hblock

theorem vatMoveSourceRevertWish
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    evalExpr? config { contract := contract, locals := moveStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool false) →
    ExecTransitionBody config contract evm0 (moveStore I) moveTransition.body .reverted := by
  intro evm0 hwish
  have hblock :
      ExecBlock config { contract := contract, locals := moveStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcDaiNew" (.storage (daiRef (.var "src")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "src")) (.var "srcDaiNew") ] ++
          checkedAddUintInto "dstDaiNew" (.storage (daiRef (.var "dst")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := moveStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcDaiNew" (some uint256)
          (sub256 (.storage (daiRef (.var "src"))) (.var "rad")),
        .require (.binary .le (.var "srcDaiNew")
          (.storage (daiRef (.var "src")))),
        .assign .storage (daiRef (.var "src")) (.var "srcDaiNew"),
        .letDecl "dstDaiNew" (some uint256)
          (add256 (.storage (daiRef (.var "dst"))) (.var "rad")),
        .require (.binary .ge (.var "dstDaiNew")
          (.storage (daiRef (.var "dst")))),
        .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hwish)
  simpa [ExecTransitionBody, moveTransition, evm0, nonpayable, checkedSubUintInto,
    checkedAddUintInto, List.append_assoc] using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem vatMoveSourceRevertSrcUnderflow
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let srcOld := vatSlotWord (moveSrcDaiSlot I) σ_solm I
    evalExpr? config { contract := contract, locals := moveStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool true) →
    srcOld.toNat < (moveRadWord I).toNat →
    ExecTransitionBody config contract evm0 (moveStore I) moveTransition.body .reverted := by
  intro evm0 srcOld hwish hunder
  have hsrcLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (moveSrcDaiSlot I) = srcOld := by
    simp [evm0, srcOld, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hrad :
      evalExpr? config { contract := contract, locals := moveStore I } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (moveRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := moveStore I) (name := "rad")
      (value := moveRadWord I) (moveStore_get_rad I)
  have hsrc :
      evalExpr? config { contract := contract, locals := moveStore I } evm0
          (.storage (daiRef (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using evalExpr_move_src_dai_old (evm := evm0) (I := I)
  have hsub :
      evalExpr? config { contract := contract, locals := moveStore I } evm0
          (sub256 (.storage (daiRef (.var "src"))) (.var "rad")) = .revert :=
    vatEvalExpr_sub256_revert hsrc hrad hunder
  have hblock :
      ExecBlock config { contract := contract, locals := moveStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcDaiNew" (.storage (daiRef (.var "src")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "src")) (.var "srcDaiNew") ] ++
          checkedAddUintInto "dstDaiNew" (.storage (daiRef (.var "dst")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := moveStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcDaiNew" (some uint256)
          (sub256 (.storage (daiRef (.var "src"))) (.var "rad")),
        .require (.binary .le (.var "srcDaiNew")
          (.storage (daiRef (.var "src")))),
        .assign .storage (daiRef (.var "src")) (.var "srcDaiNew"),
        .letDecl "dstDaiNew" (some uint256)
          (add256 (.storage (daiRef (.var "dst"))) (.var "rad")),
        .require (.binary .ge (.var "dstDaiNew")
          (.storage (daiRef (.var "dst")))),
        .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hsub)
  simpa [ExecTransitionBody, moveTransition, evm0, nonpayable, checkedSubUintInto,
    checkedAddUintInto, List.append_assoc] using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem vatMoveSourceRevertDstOverflow
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let srcOld := vatSlotWord (moveSrcDaiSlot I) σ_solm I
    let srcDaiNew := UInt256.sub srcOld (moveRadWord I)
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
      (moveSrcDaiSlot I) srcDaiNew
    let dstOld := Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (moveDstDaiSlot I)
    evalExpr? config { contract := contract, locals := moveStore I } evm0
        (wishExpr (.var "src") sender) = .ok (.bool true) →
    (moveRadWord I).toNat ≤ srcOld.toNat →
    UInt256.size ≤ dstOld.toNat + (moveRadWord I).toNat →
    ExecTransitionBody config contract evm0 (moveStore I) moveTransition.body .reverted := by
  intro evm0 srcOld srcDaiNew evm1 dstOld hwish hsrcEnough hover
  have hsrcLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (moveSrcDaiSlot I) = srcOld := by
    simp [evm0, srcOld, vatSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  have hdstLoad :
      Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner (moveDstDaiSlot I) = dstOld := by
    simp [dstOld]
  have hrad :
      evalExpr? config { contract := contract, locals := moveStore I } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (moveRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := moveStore I) (name := "rad")
      (value := moveRadWord I) (moveStore_get_rad I)
  have hsrc :
      evalExpr? config { contract := contract, locals := moveStore I } evm0
          (.storage (daiRef (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using evalExpr_move_src_dai_old (evm := evm0) (I := I)
  have hsub :
      evalExpr? config { contract := contract, locals := moveStore I } evm0
          (sub256 (.storage (daiRef (.var "src"))) (.var "rad")) =
        .ok (.int (Int.ofNat srcDaiNew.toNat)) :=
    vatEvalExpr_sub256_ok hsrc hrad (by simp [srcDaiNew]) hsrcEnough
  have hsrcDaiNewEval :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm0 (.var "srcDaiNew") =
        .ok (.int (Int.ofNat srcDaiNew.toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm0) (locals := moveStoreSrcDaiNew I srcDaiNew)
      (name := "srcDaiNew") (value := srcDaiNew)
      (moveStoreSrcDaiNew_get_srcDaiNew I srcDaiNew)
  have hsrcAgain :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm0 (.storage (daiRef (.var "src"))) =
        .ok (.int (Int.ofNat srcOld.toNat)) := by
    simpa [hsrcLoad] using
      evalExpr_move_src_dai_after_src (evm := evm0) (I := I) srcDaiNew
  have hsrcDaiNewNat : srcDaiNew.toNat = srcOld.toNat - (moveRadWord I).toNat := by
    simp [srcDaiNew, usub_toNat hsrcEnough]
  have hreqSub :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm0 (.binary .le (.var "srcDaiNew")
            (.storage (daiRef (.var "src")))) =
        .ok (.bool true) :=
    vatEvalExpr_le_uint256_true hsrcDaiNewEval hsrcAgain
      (by rw [hsrcDaiNewNat]; omega)
  have hassignSrc :
      assignStorageRef? config
        { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew } evm0 .storage
        (daiRef (.var "src")) (.int (Int.ofNat srcDaiNew.toNat)) =
        .ok ({ contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }, evm1) :=
    assignStorageRef_move_src_dai (evm := evm0) (evm' := evm1) (I := I)
      (srcDaiNew := srcDaiNew) (by simp [evm1])
  have hradAfterSrc :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm1 (.var "rad") =
        .ok (.int (Int.ofNat (moveRadWord I).toNat)) :=
    vatEvalExpr_varUInt256 (evm := evm1) (locals := moveStoreSrcDaiNew I srcDaiNew)
      (name := "rad") (value := moveRadWord I)
      (moveStoreSrcDaiNew_get_rad I srcDaiNew)
  have hdst :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm1 (.storage (daiRef (.var "dst"))) =
        .ok (.int (Int.ofNat dstOld.toNat)) := by
    simpa [hdstLoad] using
      evalExpr_move_dst_dai_after_src (evm := evm1) (I := I) srcDaiNew
  have hadd :
      evalExpr? config { contract := contract, locals := moveStoreSrcDaiNew I srcDaiNew }
          evm1 (add256 (.storage (daiRef (.var "dst"))) (.var "rad")) =
        .revert :=
    fluxEvalExpr_add256_revert hdst hradAfterSrc hover
  have hblock :
      ExecBlock config { contract := contract, locals := moveStore I } evm0
        (nonpayable ++
          [ .require (wishExpr (.var "src") sender) ] ++
          checkedSubUintInto "srcDaiNew" (.storage (daiRef (.var "src")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "src")) (.var "srcDaiNew") ] ++
          checkedAddUintInto "dstDaiNew" (.storage (daiRef (.var "dst")))
            (.var "rad") ++
          [ .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ])
        .reverted := by
    change ExecBlock config { contract := contract, locals := moveStore I } evm0
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (wishExpr (.var "src") sender),
        .letDecl "srcDaiNew" (some uint256)
          (sub256 (.storage (daiRef (.var "src"))) (.var "rad")),
        .require (.binary .le (.var "srcDaiNew")
          (.storage (daiRef (.var "src")))),
        .assign .storage (daiRef (.var "src")) (.var "srcDaiNew"),
        .letDecl "dstDaiNew" (some uint256)
          (add256 (.storage (daiRef (.var "dst"))) (.var "rad")),
        .require (.binary .ge (.var "dstDaiNew")
          (.storage (daiRef (.var "dst")))),
        .assign .storage (daiRef (.var "dst")) (.var "dstDaiNew") ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hwish) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hsub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSub) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hsrcDaiNewEval hassignSrc) ?_
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)
  simpa [ExecTransitionBody, moveTransition, evm0, nonpayable, checkedSubUintInto,
    checkedAddUintInto, List.append_assoc] using ExecFuncBody.execBlockRevert hblock

theorem vatDecode_move_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (moveTransition.params.map Param.name)
      (transitionSignature moveTransition).paramTypes I.calldata = some (moveStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "rad"]
    [addr, addr, uint256] I.calldata = _
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["src", "dst", "rad"]
      [abiAddress, abiAddress, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "src"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "dst"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "rad"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact
    decodeCalldata_legacyAddress_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "src") (y := "dst") (z := "rad") hsz100

theorem vatDecode_move_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (moveTransition.params.map Param.name)
      (transitionSignature moveTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "rad"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["src", "dst", "rad"]
    [abiAddress, abiAddress, abiUInt256] I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "src") (y := "dst") (z := "rad") hsz4 hshort

theorem vatDispatchMove {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 19)) :
    dispatchMsg contract I.calldata = some moveTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 19 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some moveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes, initSelectorBytes,
    liveSelectorBytes, moveSelectorBytes]
  native_decide

theorem vatReachMoveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 19)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1303⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xbb35783b⟩ :=
    vatSelWord_eq_of_beq I hsz 0xbb 0x35 0x78 0x3b ⟨0xbb35783b⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms114Body 0 (by omega) ⟨1303⟩ hcode hwv hsz hsize
    hroot hhigh hhighhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatMoveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1303⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5874⟩
      [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1303⟩) (ret := ⟨524⟩)
    (decoded := ⟨1325⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hmasked⟩ := RD.solcAddressAddressUint256ExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨1325⟩) (ret := ⟨524⟩) (routine := ⟨5874⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [moveRadWord, moveDstMaskedWord, moveSrcMaskedWord, moveDstWord, moveSrcWord,
      calldataWord] using hmasked⟩

theorem vatMoveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1303⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1303⟩) (ret := ⟨524⟩)
    (decoded := ⟨1325⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveWishLoaded
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5874⟩
      [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      [vatSlotWord (moveWishSlot I) σ I, ⟨1⟩, ⟨0⟩, moveSrcMaskedWord I,
        hopeSourceWord I, UInt256.ofNat I.source.val, moveSrcMaskedWord I, ⟨5884⟩,
        moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
      (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I))
        (twoWordHashMem (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6557 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨5884⟩ (by native_decide) (by evm_ov),
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
          (moveSrcMaskedWord I) =
        moveSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left (moveSrcMaskedWord_canonical I)
  have rd6568 := rd6568raw
  rw [hmask] at rd6568
  have rd6573pre := evm_run rd6568 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6573 := rd6573pre.mstore 0 (wordAt0Mem (moveSrcMaskedWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6580pre := evm_run rd6573 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6580 := rd6580pre.mstore 0
    (twoWordHashMem (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6585pre := evm_run rd6580 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)
            |>.readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I) :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I) solcFreePtrMem_size
  have rd6585 := rd6585pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I)) (UInt256.ofNat 3)
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
      (twoWordHashMem (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6595pre := evm_run rd6591 with [
    raw swap6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd6595 := rd6595pre.mstore 0
    (twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I))
      (twoWordHashMem (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6597pre := evm_run rd6595 with [
    raw dup3 (by native_decide) (by evm_ov)]
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (hopeSourceWord I)
            (solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I))
            (twoWordHashMem (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)).readWithPadding 0 64))) =
        moveWishSlot I := by
    rw [moveWishSlot_eq I]
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I))
      (hopeSourceWord I)
      (twoWordHashMem_size_96 (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem_size)
  have rd6597 := rd6597pre.keccak256 0 (moveWishSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6599raw⟩ := rd6597.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [vatSlotWord, solcSlotWord] using rd6599raw⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveWishBranchOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      [vatSlotWord (moveWishSlot I) σ I, ⟨1⟩, ⟨0⟩, moveSrcMaskedWord I,
        hopeSourceWord I, UInt256.ofNat I.source.val, moveSrcMaskedWord I, ⟨5884⟩,
        moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwish : moveWishWord σ I ≠ ⟨0⟩) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5951⟩
      [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
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
  have rd6793 := rd6792.or (by native_decide) (by evm_ov)
  have rd6612raw := evm_run rd6793 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd5884raw := evm_run rd6612raw with [
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
    raw push2 ⟨5951⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd5884raw.jumpiT (by native_decide) hwish (by jump_dest) (by simp)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveWishBranchRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6599⟩
      [vatSlotWord (moveWishSlot I) σ I, ⟨1⟩, ⟨0⟩, moveSrcMaskedWord I,
        hopeSourceWord I, UInt256.ofNat I.source.val, moveSrcMaskedWord I, ⟨5884⟩,
        moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hwish : moveWishWord σ I = ⟨0⟩) :
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
  have rd6793 := rd6792.or (by native_decide) (by evm_ov)
  have rd6612raw := evm_run rd6793 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd5884raw := evm_run rd6612raw with [
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
    raw push2 ⟨5951⟩ (by native_decide) (by evm_ov)]
  have rd5889 := rd5884raw.jumpiNT (by native_decide) hwish (by simp)
  exact RD.solcErrorStringRevertTail
    (code := vatBytecode) (pc := ⟨5889⟩) (len := ⟨15⟩)
    (rawWord := ⟨112128532177926167570164739106265433⟩) (shift := ⟨138⟩)
    (word := UInt256.shiftLeft ⟨112128532177926167570164739106265433⟩ ⟨138⟩)
    (op := .PUSH15) (width := 15)
    rd5889
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by native_decide) rfl hmem hread64 (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveSourceSubSuccess
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5951⟩
      [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hle :
      (moveRadWord I).toNat ≤
        (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I))).toNat) :
    ∃ k' C', RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5986⟩
      (UInt256.sub (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I)))
          (moveRadWord I) ::
        moveRadWord I :: moveDstMaskedWord I :: moveSrcMaskedWord I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let slot := solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I)
  let old := solcSlotWord σ I slot
  have rd5961raw := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (moveSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        moveSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    exact solcAddrMask_clean_left (moveSrcMaskedWord_canonical I)
  have rd5961 := rd5961raw
  rw [hmask] at rd5961
  have rd5966pre := evm_run rd5961 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd5966 := rd5966pre.mstore 0 (wordAt0Mem (moveSrcMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd5971pre := evm_run rd5966 with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd5971 := rd5971pre.mstore 0
    (twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd5975pre := evm_run rd5971 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩ mem).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I) hmem
  have rd5975 := rd5975pre.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5977raw⟩ := rd5975.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd5977 := rd5977raw
  rw [hold] at rd5977
  have rd6621pre := evm_run rd5977 with [
    raw push2 ⟨5986⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubSuccess
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := old) (b := moveRadWord I) (ret := ⟨5986⟩)
    (R := [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel])
    (by simpa [old, slot] using rd6621)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot] using hle) (by jump_dest) (by jump_dest) (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveSourceSubRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} {sel : UInt256} {mem : ByteArray}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5951⟩
      [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hmem : mem.size = 96)
    (hlt :
      (solcSlotWord σ I (solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I))).toNat <
        (moveRadWord I).toNat) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let slot := solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I)
  let old := solcSlotWord σ I slot
  have rd5961raw := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (moveSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        moveSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm]
    exact solcAddrMask_clean_left (moveSrcMaskedWord_canonical I)
  have rd5961 := rd5961raw
  rw [hmask] at rd5961
  have rd5966pre := evm_run rd5961 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd5966 := rd5966pre.mstore 0 (wordAt0Mem (moveSrcMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd5971pre := evm_run rd5966 with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd5971 := rd5971pre.mstore 0
    (twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd5975pre := evm_run rd5971 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩ mem).readWithPadding 0 64))) =
        slot := by
    simpa [slot] using twoWordHashMem_solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I) hmem
  have rd5975 := rd5975pre.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5977raw⟩ := rd5975.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd5977 := rd5977raw
  rw [hold] at rd5977
  have rd6621pre := evm_run rd5977 with [
    raw push2 ⟨5986⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have hroutine := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := old)
    (b := moveRadWord I) (ret := ⟨5986⟩)
    (R := [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩, sel])
    (by simpa [old, slot] using hroutine)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot] using hlt) (by simp)

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveSourceStoreValue
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {srcDaiNew rad dst src ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨5986⟩
      (srcDaiNew :: rad :: dst :: src :: ret :: R)
      (twoWordHashMem src ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hsrcCanon : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨6017⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: rad :: dst :: src :: ret :: R)
      (twoWordHashMem src ⟨5⟩ (twoWordHashMem src ⟨5⟩ mem))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨5⟩ src) srcDaiNew) k' C' := by
  simpa [solcSingleMappingStoreDebitOutPc] using
    RD.solcSingleMappingStoreDebitMem
      (code := vatBytecode) (pc := ⟨5986⟩) (baseSlot := ⟨5⟩)
      (newValue := srcDaiNew) (value := rad) (aux := dst) (key := src)
      (ret := ret) (R := R) h
      (by
        unfold solcSingleMappingStoreDebitMemWf
        repeat' first | apply And.intro | native_decide)
      hmem hperm hsrcCanon hov

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveDestAddSuccess
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {rad dst src ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6017⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: rad :: dst :: src :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem dst mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ dst)
    (hdstCanon : dst.toNat < EVM.addressModulus)
    (hfit : (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ dst)).toNat + rad.toNat < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ⟨6033⟩
      ((solcSlotWord σ ee (solcMappingSlot ⟨5⟩ dst) + rad) ::
        rad :: dst :: src :: ret :: R)
      (wordAt0Mem dst mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  let slot := solcMappingSlot ⟨5⟩ dst
  let old := solcSlotWord σ ee slot
  have rd6019raw := evm_run h with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask : UInt256.land dst solcAddrMask = dst :=
    solcAddrMask_clean hdstCanon
  have rd6019 := rd6019raw
  rw [hmask] at rd6019
  have rd6021pre := evm_run rd6019 with [
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6021 := rd6021pre.mstore 0 (wordAt0Mem dst mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6022 := rd6021.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost (by simpa [slot] using hslot) (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6024raw⟩ := rd6022.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd6024 := rd6024raw
  rw [hold] at rd6024
  have rd6637pre := evm_run rd6024 with [
    raw push2 ⟨6033⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6637⟩ (by native_decide) (by evm_ov)]
  have rd6637 := rd6637pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedAddSuccess
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := old) (b := rad) (ret := ⟨6033⟩)
    (R := [rad, dst, src, ret] ++ R)
    (by simpa [old, slot] using rd6637)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot] using hfit) (by jump_dest) (by jump_dest)
    (by simp [List.length_cons, List.length_append] at hov ⊢; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveDestAddRevert
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {rad dst src ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6017⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: rad :: dst :: src :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem dst mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ dst)
    (hdstCanon : dst.toNat < EVM.addressModulus)
    (hover : UInt256.size ≤
      (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ dst)).toNat + rad.toNat)
    (hov : R.length + 16 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  let slot := solcMappingSlot ⟨5⟩ dst
  let old := solcSlotWord σ ee slot
  have rd6019raw := evm_run h with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask : UInt256.land dst solcAddrMask = dst :=
    solcAddrMask_clean hdstCanon
  have rd6019 := rd6019raw
  rw [hmask] at rd6019
  have rd6021pre := evm_run rd6019 with [
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6021 := rd6021pre.mstore 0 (wordAt0Mem dst mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6022 := rd6021.keccak256 0 slot (UInt256.ofNat 3)
    (by native_decide) mem_cost (by simpa [slot] using hslot) (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6024raw⟩ := rd6022.sload (by native_decide) (by evm_ov)
  have hold :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = old := by
    simp [old, solcSlotWord]
  have rd6024 := rd6024raw
  rw [hold] at rd6024
  have rd6637pre := evm_run rd6024 with [
    raw push2 ⟨6033⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨6637⟩ (by native_decide) (by evm_ov)]
  have hroutine := rd6637pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6637⟩) (okPc := ⟨6615⟩)
    (a := old) (b := rad) (ret := ⟨6033⟩)
    (R := [rad, dst, src, ret] ++ R)
    (by simpa [old, slot] using hroutine)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [old, slot] using hover)
    (by simp [List.length_cons, List.length_append] at hov ⊢; omega)

set_option maxHeartbeats 1000000 in
theorem RD.vatMoveDestStoreReturn
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {dstDaiNew rad dst src ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨6033⟩
      (dstDaiNew :: rad :: dst :: src :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hdstCanon : dst.toNat < EVM.addressModulus)
    (hperm : ee.perm = true)
    (hret : (D_J vatBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD vatBytecode ee g s0 ret R
      (twoWordHashMem dst ⟨5⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨5⟩ dst) dstDaiNew) k' C' := by
  have rd6034 := h.jumpdest (by native_decide) (by evm_ov)
  have rd6044raw := evm_run rd6034 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land dst
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        dst := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean hdstCanon
  have rd6044 := rd6044raw
  rw [hmask] at rd6044
  have rd6049pre := evm_run rd6044 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6049 := rd6049pre.mstore 0 (wordAt0Mem dst mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6054pre := evm_run rd6049 with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd6054 := rd6054pre.mstore 0 (twoWordHashMem dst ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6058pre := evm_run rd6054 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem dst ⟨5⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ dst := by
    exact twoWordHashMem_solcMappingSlot ⟨5⟩ dst hmem
  have rd6058 := rd6058pre.keccak256 0 (solcMappingSlot ⟨5⟩ dst)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd6062pre := evm_run rd6058 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6063raw⟩ := rd6062pre.sstore hperm (by native_decide)
    (by simp [List.length_cons] at hov ⊢; omega)
  have rd6064 := rd6063raw.pop (by native_decide) (by evm_ov)
  have rd6065 := rd6064.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa using rd6065.jump (by native_decide) hret (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem vatMoveAuthorizedPath
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {k C : ℕ} {memWish : ByteArray}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some moveTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (moveTransition.params.map Param.name)
        (transitionSignature moveTransition).paramTypes I.calldata = some (moveStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmemWish : memWish.size = 96)
    (hwishSolm :
      evalExpr? config
        { contract := contract, locals := moveStore I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (wishExpr (.var "src") sender) = .ok (.bool true))
    (h5951 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5951⟩
      [moveRadWord I, moveDstMaskedWord I, moveSrcMaskedWord I, ⟨524⟩,
        vatSelWord I]
      memWish (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hsrcWord :
      vatSlotWord (moveSrcDaiSlot I) σ_evm I =
        vatSlotWord (moveSrcDaiSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (moveSrcDaiSlot I) ⟨0⟩
  let srcOldE := vatSlotWord (moveSrcDaiSlot I) σ_evm I
  let srcDaiNew := UInt256.sub srcOldE (moveRadWord I)
  by_cases hsrcUnder : srcOldE.toNat < (moveRadWord I).toNat
  · have hbody :
        ExecTransitionBody config contract evm0 (moveStore I) moveTransition.body .reverted := by
      exact vatMoveSourceRevertSrcUnderflow
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hwv
        (by simpa [evm0] using hwishSolm)
        (by simpa [evm0, srcOldE, hsrcWord] using hsrcUnder)
    have hsrcUnderSolc :
        (solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I))).toNat <
          (moveRadWord I).toNat := by
      simpa [srcOldE, vatSlotWord, moveSrcDaiSlot_eq I] using hsrcUnder
    have hrev := RD.vatMoveSourceSubRevert
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
      h5951 hmemWish hsrcUnderSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hsrcEnough : (moveRadWord I).toNat ≤ srcOldE.toNat := le_of_not_gt hsrcUnder
    have hsrcEnoughSolc :
        (moveRadWord I).toNat ≤
          (solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I))).toNat := by
      simpa [srcOldE, vatSlotWord, moveSrcDaiSlot_eq I] using hsrcEnough
    obtain ⟨_, _, h5986⟩ := RD.vatMoveSourceSubSuccess
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := vatSelWord I)
      h5951 hmemWish hsrcEnoughSolc
    let memSrcSub := twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩ memWish
    have hmemSrcSub : memSrcSub.size = 96 := by
      dsimp [memSrcSub]
      apply twoWordHashMem_size_96
      exact hmemWish
    obtain ⟨_, _, h6017⟩ := RD.vatMoveSourceStoreValue
      (h := h5986) hmemWish hperm (moveSrcMaskedWord_canonical I) (by simp)
    let σSrcE := sstoreAccountMap I.codeOwner σ_evm (moveSrcDaiSlot I) srcDaiNew
    let σSrcS := sstoreAccountMap I.codeOwner σ_solm (moveSrcDaiSlot I) srcDaiNew
    have hsrcSlotEq :
        solcMappingSlot ⟨5⟩ (moveSrcMaskedWord I) = moveSrcDaiSlot I := by
      exact (moveSrcDaiSlot_eq I).symm
    have h6017Move := h6017
    rw [hsrcSlotEq] at h6017Move
    have hsrcValEqMove :
        UInt256.sub (solcSlotWord σ_evm I (moveSrcDaiSlot I)) (moveRadWord I) =
          srcDaiNew := by
      simp [srcDaiNew, srcOldE, vatSlotWord]
    rw [hsrcValEqMove] at h6017Move
    have hAccountsSrc : accountMapEquiv σSrcE σSrcS := by
      simpa [σSrcE, σSrcS] using
        accountMapEquiv_sstoreAccountMap I.codeOwner (moveSrcDaiSlot I) srcDaiNew hAccounts
    have hdstWord :
        vatSlotWord (moveDstDaiSlot I) σSrcE I =
          vatSlotWord (moveDstDaiSlot I) σSrcS I :=
      accountMapEquiv_storage_findD hAccountsSrc I.codeOwner (moveDstDaiSlot I) ⟨0⟩
    let dstOldE := vatSlotWord (moveDstDaiSlot I) σSrcE I
    let dstDaiNew := dstOldE + moveRadWord I
    have hdstSlotEq :
        solcMappingSlot ⟨5⟩ (moveDstMaskedWord I) = moveDstDaiSlot I := by
      exact (moveDstDaiSlot_eq I).symm
    have hsrcDaiNewSolm :
        UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I) (moveRadWord I) =
          srcDaiNew := by
      simp [srcDaiNew, srcOldE, hsrcWord]
    have hloadDstSolm :
        Solm.EVM.storageLoad
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
              (moveSrcDaiSlot I)
              (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                (moveRadWord I)))
            (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
              (moveSrcDaiSlot I)
              (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                (moveRadWord I))).executionEnv.codeOwner
            (moveDstDaiSlot I) =
          vatSlotWord (moveDstDaiSlot I) σSrcS I := by
      rw [hsrcDaiNewSolm]
      simp [evm0, σSrcS, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
        storageStore_accountMap, vatSlotWord, solcSlotWord]
    let memDestIn :=
      twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩
        (twoWordHashMem (moveSrcMaskedWord I) ⟨5⟩ memWish)
    have hdstHashSlot :
        UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem (moveDstMaskedWord I) memDestIn).readWithPadding 0 64))) =
          solcMappingSlot ⟨5⟩ (moveDstMaskedWord I) := by
      dsimp [memDestIn]
      apply wordAt0Mem_twoWordHashMem_solcMappingSlot
      apply twoWordHashMem_size_96
      exact hmemWish
    by_cases hdstOverflow : UInt256.size ≤ dstOldE.toNat + (moveRadWord I).toNat
    · have hdstOverflowSolm :
          UInt256.size ≤
            (Solm.EVM.storageLoad
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (moveSrcDaiSlot I)
                  (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                    (moveRadWord I)))
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (moveSrcDaiSlot I)
                  (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                    (moveRadWord I))).executionEnv.codeOwner
                (moveDstDaiSlot I)).toNat + (moveRadWord I).toNat := by
        rw [hloadDstSolm]
        have htmp :
            UInt256.size ≤ (vatSlotWord (moveDstDaiSlot I) σSrcE I).toNat +
                (moveRadWord I).toNat := by
          simpa [dstOldE] using hdstOverflow
        rw [hdstWord] at htmp
        exact htmp
      have hbody :
          ExecTransitionBody config contract evm0 (moveStore I) moveTransition.body
            .reverted := by
        exact vatMoveSourceRevertDstOverflow
          (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hwv
          (by simpa [evm0] using hwishSolm)
          (by simpa [srcOldE, hsrcWord] using hsrcEnough)
          hdstOverflowSolm
      have hdstOverflowSolc :
          UInt256.size ≤
            (solcSlotWord σSrcE I
              (solcMappingSlot ⟨5⟩ (moveDstMaskedWord I))).toNat +
              (moveRadWord I).toNat := by
        simpa [dstOldE, vatSlotWord, σSrcE, moveDstDaiSlot_eq I] using hdstOverflow
      have hrev := RD.vatMoveDestAddRevert
        (h := h6017Move)
        hdstHashSlot (moveDstMaskedWord_canonical I) hdstOverflowSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdstFit : dstOldE.toNat + (moveRadWord I).toNat < UInt256.size :=
        Nat.lt_of_not_ge hdstOverflow
      have hdstFitSolc :
          (solcSlotWord σSrcE I
                (solcMappingSlot ⟨5⟩ (moveDstMaskedWord I))).toNat +
              (moveRadWord I).toNat < UInt256.size := by
        simpa [dstOldE, vatSlotWord, σSrcE, moveDstDaiSlot_eq I] using hdstFit
      obtain ⟨_, _, h6033⟩ := RD.vatMoveDestAddSuccess
        (h := h6017Move)
        hdstHashSlot (moveDstMaskedWord_canonical I) hdstFitSolc (by simp)
      have hdstValEq :
          solcSlotWord σSrcE I (solcMappingSlot ⟨5⟩ (moveDstMaskedWord I)) +
              moveRadWord I =
            dstDaiNew := by
        simp [dstDaiNew, dstOldE, vatSlotWord, moveDstDaiSlot_eq I]
      have h6033Move := h6033
      rw [hdstValEq] at h6033Move
      let memDestAdd := wordAt0Mem (moveDstMaskedWord I) memDestIn
      have hmemDestAdd : memDestAdd.size = 96 := by
        dsimp [memDestAdd, memDestIn]
        apply wordAt0Mem_size_96
        apply twoWordHashMem_size_96
        apply twoWordHashMem_size_96
        exact hmemWish
      obtain ⟨_, _, hretPcRaw⟩ := RD.vatMoveDestStoreReturn
        (h := h6033Move)
        hmemDestAdd (moveDstMaskedWord_canonical I) hperm (by jump_dest) (by simp)
      have hretPc := hretPcRaw
      rw [hdstSlotEq] at hretPc
      have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
      have hret :
          RDret vatBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (cA, sstoreAccountMap I.codeOwner σSrcE (moveDstDaiSlot I) dstDaiNew)
            ByteArray.empty := by
        exact RD.stop hretPc' (by native_decide) (by simp)
      have hdstFitSolm :
          (Solm.EVM.storageLoad
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                (moveSrcDaiSlot I)
                (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                  (moveRadWord I)))
              (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                (moveSrcDaiSlot I)
                (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                  (moveRadWord I))).executionEnv.codeOwner
              (moveDstDaiSlot I)).toNat + (moveRadWord I).toNat < UInt256.size := by
        rw [hloadDstSolm]
        have htmp :
            (vatSlotWord (moveDstDaiSlot I) σSrcE I).toNat +
                (moveRadWord I).toNat < UInt256.size := by
          simpa [dstOldE] using hdstFit
        rw [hdstWord] at htmp
        exact htmp
      have hbody := vatMoveSourceOk
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hwv
        (by simpa [evm0] using hwishSolm)
        (by simpa [srcOldE, hsrcWord] using hsrcEnough)
        hdstFitSolm
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σSrcE (moveDstDaiSlot I) dstDaiNew).1 =
            (Solm.EVM.storageStore
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (moveSrcDaiSlot I)
                  (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                    (moveRadWord I)))
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (moveSrcDaiSlot I)
                  (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                    (moveRadWord I))).executionEnv.codeOwner
                (moveDstDaiSlot I)
                ((Solm.EVM.storageLoad
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (moveSrcDaiSlot I)
                      (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                        (moveRadWord I)))
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (moveSrcDaiSlot I)
                      (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                        (moveRadWord I))).executionEnv.codeOwner
                    (moveDstDaiSlot I)) + moveRadWord I)).createdAccounts := by
        simp [evm0, initState, storageStore_createdAccounts]
      have haccountsFinal :
          accountMapEquiv
            (cA, sstoreAccountMap I.codeOwner σSrcE (moveDstDaiSlot I) dstDaiNew).2
            (Solm.EVM.storageStore
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (moveSrcDaiSlot I)
                  (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                    (moveRadWord I)))
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (moveSrcDaiSlot I)
                  (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                    (moveRadWord I))).executionEnv.codeOwner
                (moveDstDaiSlot I)
                ((Solm.EVM.storageLoad
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (moveSrcDaiSlot I)
                      (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                        (moveRadWord I)))
                    (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                      (moveSrcDaiSlot I)
                      (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                        (moveRadWord I))).executionEnv.codeOwner
                    (moveDstDaiSlot I)) + moveRadWord I)).accountMap := by
        have hAccountsDst :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner σSrcE (moveDstDaiSlot I) dstDaiNew)
              (sstoreAccountMap I.codeOwner σSrcS (moveDstDaiSlot I) dstDaiNew) :=
          accountMapEquiv_sstoreAccountMap I.codeOwner (moveDstDaiSlot I) dstDaiNew
            hAccountsSrc
        have hloadDstSolmOwner :
            Solm.EVM.storageLoad
                (Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner
                  (moveSrcDaiSlot I)
                  (UInt256.sub (vatSlotWord (moveSrcDaiSlot I) σ_solm I)
                    (moveRadWord I)))
                evm0.executionEnv.codeOwner
                (moveDstDaiSlot I) =
              vatSlotWord (moveDstDaiSlot I) σSrcS I := by
          simpa [storageStore_executionEnv] using hloadDstSolm
        have hdstDaiNewSolmOwner :
            vatSlotWord (moveDstDaiSlot I) σSrcS I + moveRadWord I = dstDaiNew := by
          simp [dstDaiNew, dstOldE, hdstWord]
        rw [storageStore_accountMap, storageStore_executionEnv]
        rw [hloadDstSolmOwner, hdstDaiNewSolmOwner]
        rw [storageStore_accountMap]
        rw [hsrcDaiNewSolm]
        change accountMapEquiv
          (sstoreAccountMap I.codeOwner σSrcE (moveDstDaiSlot I) dstDaiNew)
          (sstoreAccountMap evm0.executionEnv.codeOwner σSrcS (moveDstDaiSlot I) dstDaiNew)
        rw [show evm0.executionEnv.codeOwner = I.codeOwner by simp [evm0, initState]]
        exact hAccountsDst
      have henc : returnEquiv ByteArray.empty none moveTransition.returnType := by
        rw [show moveTransition.returnType = [] by rfl]
        exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccountsFinal henc

theorem vatMoveBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsel : selIs I (vatSelBytes 19))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1303⟩ [vatSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatMoveX_shortarg (g := Sat256.ofUInt256 g) hsz4 hshort hsize hreach)
    |>.reEquivDecodingFailed hcode (vatDispatchMove hsel)
      (vatDecode_move_none_short hsz4 hshort)

theorem vatMoveBodyCore : VatBodyTheorem 19 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 19) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some moveTransition :=
    vatDispatchMove hsel
  have hreach := vatReachMoveBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := vatDecode_move_ok (I := I) hsz100
    obtain ⟨_, _, hdecoded⟩ := vatMoveX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    obtain ⟨_, _, hloaded⟩ := RD.vatMoveWishLoaded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecoded
    let memWish :=
      twoWordHashMem (hopeSourceWord I) (solcMappingSlot ⟨1⟩ (moveSrcMaskedWord I))
        (twoWordHashMem (moveSrcMaskedWord I) ⟨1⟩ solcFreePtrMem)
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
    by_cases hsrcEq : moveSrcMaskedWord I = hopeSourceWord I
    · have hwishSolm :
          evalExpr? config { contract := contract, locals := moveStore I } evm0
            (wishExpr (.var "src") sender) = .ok (.bool true) :=
        evalExpr_move_wish_true_src (evm := evm0) (I := I)
          (by simp [evm0, initState]) hsrcEq
      have hwishEvm : moveWishWord σ_evm I ≠ ⟨0⟩ :=
        moveWishWord_true_src (σ := σ_evm) (I := I) hsrcEq
      obtain ⟨_, _, h5951⟩ := RD.vatMoveWishBranchOk hloaded hwishEvm
      exact vatMoveAuthorizedPath
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hperm hwv
        hdispatch hdecode hAccounts hmemWish
        (by simpa [evm0] using hwishSolm) h5951
    · by_cases hcanEvm : vatSlotWord (moveWishSlot I) σ_evm I = ⟨1⟩
      · have hcanSolm :
            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (moveWishSlot I) = ⟨1⟩ := by
          have hcanWord :
              vatSlotWord (moveWishSlot I) σ_evm I =
                vatSlotWord (moveWishSlot I) σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (moveWishSlot I) ⟨0⟩
          rw [hcanWord] at hcanEvm
          simpa [evm0, initState, vatSlotWord, solcSlotWord, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage] using hcanEvm
        have hwishSolm :
            evalExpr? config { contract := contract, locals := moveStore I } evm0
              (wishExpr (.var "src") sender) = .ok (.bool true) :=
          evalExpr_move_wish_true_can (evm := evm0) (I := I)
            (by simp [evm0, initState]) hsrcEq hcanSolm
        have hwishEvm : moveWishWord σ_evm I ≠ ⟨0⟩ :=
          moveWishWord_true_can (σ := σ_evm) (I := I) hcanEvm
        obtain ⟨_, _, h5951⟩ := RD.vatMoveWishBranchOk hloaded hwishEvm
        exact vatMoveAuthorizedPath
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hperm hwv
          hdispatch hdecode hAccounts hmemWish
          (by simpa [evm0] using hwishSolm) h5951
      · have hcanSolm :
            Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (moveWishSlot I) ≠ ⟨1⟩ := by
          intro hbad
          apply hcanEvm
          have hcanWord :
              vatSlotWord (moveWishSlot I) σ_evm I =
                vatSlotWord (moveWishSlot I) σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (moveWishSlot I) ⟨0⟩
          rw [hcanWord]
          simpa [evm0, initState, vatSlotWord, solcSlotWord, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage] using hbad
        have hwishSolm :
            evalExpr? config { contract := contract, locals := moveStore I } evm0
              (wishExpr (.var "src") sender) = .ok (.bool false) :=
          evalExpr_move_wish_false (evm := evm0) (I := I)
            (by simp [evm0, initState]) hsrcEq hcanSolm
        have hbody :
            ExecTransitionBody config contract evm0 (moveStore I) moveTransition.body
              .reverted :=
          vatMoveSourceRevertWish
            (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hwishSolm
        have hrev := RD.vatMoveWishBranchRevert hloaded hmemWish hread64Wish
          (moveWishWord_false (σ := σ_evm) (I := I) hsrcEq hcanEvm)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact vatMoveBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hsel hreach

end Benchmarks.Dss.Vat
