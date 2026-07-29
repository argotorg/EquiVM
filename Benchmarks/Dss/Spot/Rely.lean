import Benchmarks.Dss.Spot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

/-! ## `rely(address)` -/

abbrev relyGuyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev relyGuyMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (relyGuyWord I)

abbrev relySourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev relyGuyValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (relyGuyWord I).toNat)

abbrev relyGuyKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (relyGuyWord I).toNat)

abbrev relyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev relyStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "guy" (relyGuyValue I)

def relyGuyStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyGuyKey I)

def relyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyAuthKey I)

def relyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  spotSlotWord (relyAuthStorageSlot I) σ I

def relyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (relyGuyStorageSlot I) ⟨1⟩

abbrev relyGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyGuyKey I)] }

abbrev relyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyAuthKey I)] }

theorem relyStore_wards (I : ExecutionEnv) :
    (relyStore I).get? "wards" = none := by
  unfold relyStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem relySourceWord_toNat (I : ExecutionEnv) :
    (relySourceWord I).toNat = I.source.val := by
  unfold relySourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem relyGuyStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    relyGuyStorageSlot I = mapSlot (relyGuyMaskedWord I) ⟨0⟩ := by
  unfold relyGuyStorageSlot wardsSlot relyGuyKey relyGuyMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem relyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    relyAuthStorageSlot I = mapSlot (relySourceWord I) ⟨0⟩ := by
  unfold relyAuthStorageSlot wardsSlot relyAuthKey relySourceWord
  rw [keyValueToWord_address]

theorem spotDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy"] [addr] I.calldata = _
  simpa [relyStore, relyGuyValue, relyGuyWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "guy") hsz36

theorem spotDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "guy")
    hsz4 hshort

theorem evalStorageRef_rely_guy (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef (.var "guy")) = .ok (relyGuyEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, relyStore, relyGuyValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_rely_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem uint256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem evalExpr_rely_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := relyStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [relyStore, wardsRef])
      (her := evalStorageRef_rely_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using spotStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_rely_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := relyStore I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simp [relyStore, wardsRef])
      (her := evalStorageRef_rely_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact spotStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalStorageRef_auth_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (_hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_auth_true_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simpa [wardsRef] using hwards)
      (her := evalStorageRef_auth_of_wards_none evm I locals hwards hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using spotStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_auth_false_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simpa [wardsRef] using hwards)
      (her := evalStorageRef_auth_of_wards_none evm I locals hwards hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact spotStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem relyAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := relyStore I } evm
      .storage (wardsRef (.var "guy")) (.int 1) =
        .ok ({ contract := contract, locals := relyStore I }, relyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (relyGuyStorageSlot I))
      (hbase := relyStore_wards I)
      (her := evalStorageRef_rely_guy evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [relyPostState, wordLoc, uint256Loc] using
    storageLocStore_uint256 evm (relyGuyStorageSlot I) ⟨1⟩

theorem spotRelyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) relyTransition.body
      (.returned { contract := contract, locals := relyStore I } (relyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (evm' := relyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 1)
      (ref := wardsRef (.var "guy"))
      (value := .int 1)
      hwv
      (evalExpr_rely_auth_true evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (relyAssign evm I)

theorem spotRelyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) relyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "guy")) (.intLit 1)])
      hwv
      (evalExpr_rely_auth_false evm I hsrc hauth)

noncomputable abbrev relyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relySourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev relyStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relyGuyMaskedWord I) ⟨0⟩ (relyAuthHashMem I)

theorem relyGuyMaskedWord_canonical (I : ExecutionEnv) :
    (relyGuyMaskedWord I).toNat < EVM.addressModulus := by
  unfold relyGuyMaskedWord
  rw [u256_land_comm solcAddrMask (relyGuyWord I)]
  exact solcAddrMask_result_canonical (relyGuyWord I)

theorem relyAuthHashMem_size (I : ExecutionEnv) :
    (relyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem relyAuthHashMem_read64 (I : ExecutionEnv) :
    (relyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem relyStoreHashMem_size (I : ExecutionEnv) :
    (relyStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relyGuyMaskedWord I) ⟨0⟩ (relyAuthHashMem_size I)

/-! ### Spotter CODECOPY-backed `Error(string)` auth tail -/

theorem spotErrorStringMem2_read64 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem2 len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem write32_read_above_from (src base : ByteArray) (srcAddr destAddr readAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) (hlo : destAddr ≤ base.size)
    (habove : destAddr + 32 ≤ readAddr) (hin : readAddr + 32 ≤ base.size) :
    (src.write srcAddr base destAddr 32).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcsz : (src.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hcsz : (base.extract (destAddr + 32) base.size).size =
      base.size - (destAddr + 32) := by
    rw [ByteArray.size_extract]
    omega
  have habsz :
      (base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + 32)).size =
        destAddr + 32 := by
    rw [ByteArray.size_append, hbsz, hsrcsz]
  rw [write_eq_gen_from src base srcAddr destAddr 32 (by decide) hsrc (by omega),
      readWithPadding_eq_extract _ readAddr
        (by rw [ByteArray.size_append, habsz, hcsz]; omega),
      readWithPadding_eq_extract _ readAddr (by omega),
      extract_append_right_window _ _ _ _ (by rw [habsz]; omega), habsz,
      extract_extract_BA,
      show destAddr + 32 + (readAddr - (destAddr + 32)) = readAddr from by omega,
      show min (destAddr + 32 + (readAddr + 32 - (destAddr + 32))) base.size =
          readAddr + 32 from by omega]

noncomputable def spotCodecopyErrorScratchMem (offset len : UInt256)
    (mem : ByteArray) : ByteArray :=
  spotBytecode.write offset.toNat (solcErrorStringMem2 len mem) 0 32

noncomputable def spotCodecopyErrorRestoreMem (offset len scratchWord : UInt256)
    (mem : ByteArray) : ByteArray :=
  scratchWord.toByteArray.write 0 (spotCodecopyErrorScratchMem offset len mem) 0 32

noncomputable def spotCodecopyErrorFinalMem
    (offset len scratchWord copiedWord : UInt256) (mem : ByteArray) : ByteArray :=
  copiedWord.toByteArray.write 0
    (spotCodecopyErrorRestoreMem offset len scratchWord mem) 196 32

theorem spotCodecopyErrorScratchMem_size {mem : ByteArray} (offset len : UInt256)
    (hmem : mem.size = 96) (hsrc : offset.toNat + 32 ≤ spotBytecode.size) :
    (spotCodecopyErrorScratchMem offset len mem).size = 196 := by
  unfold spotCodecopyErrorScratchMem
  have hbase : (solcErrorStringMem2 len mem).size = 196 := solcErrorStringMem2_size len hmem
  rw [write_eq_gen_from spotBytecode (solcErrorStringMem2 len mem) offset.toNat 0 32
      (by decide) hsrc (by rw [hbase]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hbase]
  omega

theorem spotCodecopyErrorRestoreMem_size {mem : ByteArray} (offset len scratchWord : UInt256)
    (hmem : mem.size = 96) (hsrc : offset.toNat + 32 ≤ spotBytecode.size) :
    (spotCodecopyErrorRestoreMem offset len scratchWord mem).size = 196 := by
  unfold spotCodecopyErrorRestoreMem
  exact toByteArray_write32_size_of_le
    (spotCodecopyErrorScratchMem offset len mem) scratchWord 0 196 196
    (spotCodecopyErrorScratchMem_size offset len hmem hsrc)
    (by omega)
    (by omega)

theorem spotCodecopyErrorFinalMem_size {mem : ByteArray}
    (offset len scratchWord copiedWord : UInt256) (hmem : mem.size = 96)
    (hsrc : offset.toNat + 32 ≤ spotBytecode.size) :
    (spotCodecopyErrorFinalMem offset len scratchWord copiedWord mem).size = 228 := by
  unfold spotCodecopyErrorFinalMem
  exact toByteArray_write32_size_of_le
    (spotCodecopyErrorRestoreMem offset len scratchWord mem) copiedWord 196 196 228
    (spotCodecopyErrorRestoreMem_size offset len scratchWord hmem hsrc)
    (by
      rw [spotCodecopyErrorRestoreMem_size offset len scratchWord hmem hsrc])
    (by omega)

theorem spotCodecopyErrorRestoreMem_read64 {mem : ByteArray}
    (offset len scratchWord : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrc : offset.toNat + 32 ≤ spotBytecode.size) :
    (spotCodecopyErrorRestoreMem offset len scratchWord mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold spotCodecopyErrorRestoreMem spotCodecopyErrorScratchMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by
        have hbase : (spotBytecode.write offset.toNat (solcErrorStringMem2 len mem) 0 32).size =
            196 := by
          simpa [spotCodecopyErrorScratchMem] using
            spotCodecopyErrorScratchMem_size offset len hmem hsrc
        rw [hbase]
        omega)]
  rw [write32_read_above_from spotBytecode (solcErrorStringMem2 len mem) offset.toNat 0 64
      hsrc (by omega) (by omega)
      (by
        rw [solcErrorStringMem2_size len hmem]
        omega)]
  exact spotErrorStringMem2_read64 len hmem hread64

theorem spotCodecopyErrorFinalMem_read64 {mem : ByteArray}
    (offset len scratchWord copiedWord : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrc : offset.toNat + 32 ≤ spotBytecode.size) :
    (spotCodecopyErrorFinalMem offset len scratchWord copiedWord mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold spotCodecopyErrorFinalMem
  rw [toByteArray_write_read_below_of_gap copiedWord _ 196 64
      (by
        have hbase := spotCodecopyErrorRestoreMem_size offset len scratchWord hmem hsrc
        rw [hbase]
        omega)
      (by omega)
      (by
        have hbase := spotCodecopyErrorRestoreMem_size offset len scratchWord hmem hsrc
        rw [hbase]
        exact lt_usize _ (by norm_num))]
  exact spotCodecopyErrorRestoreMem_read64 offset len scratchWord hmem hread64 hsrc

theorem spotCodecopyErrorFinalMem_mload64 {mem : ByteArray}
    (offset len scratchWord copiedWord : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrc : offset.toNat + 32 ≤ spotBytecode.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (spotCodecopyErrorFinalMem offset len scratchWord copiedWord mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((spotCodecopyErrorFinalMem offset len scratchWord copiedWord mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [spotCodecopyErrorFinalMem_size offset len scratchWord copiedWord hmem hsrc]
      omega)
    (by decide)
    (spotCodecopyErrorFinalMem_read64 offset len scratchWord copiedWord hmem hread64 hsrc)

@[reducible] def spotCodecopyAuthRevertTailWf (pc offset len : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p29 := p27 + UInt256.ofNat 2
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p33 := p31 + UInt256.ofNat 2
  let p36 := p33 + UInt256.ofNat 3
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p44 := p42 + UInt256.ofNat 2
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
  let p48 := p47 + ⟨1⟩
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p53 := p52 + ⟨1⟩
  let p55 := p53 + UInt256.ofNat 2
  let p56 := p55 + ⟨1⟩
  let p57 := p56 + ⟨1⟩
  decode spotBytecode pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode spotBytecode p2 = some (.DUP1, .none)
  ∧ decode spotBytecode p3 = some (.MLOAD, .none)
  ∧ decode spotBytecode p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode spotBytecode p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode spotBytecode p10 = some (.SHL, .none)
  ∧ decode spotBytecode p11 = some (.DUP2, .none)
  ∧ decode spotBytecode p12 = some (.MSTORE, .none)
  ∧ decode spotBytecode p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode spotBytecode p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode spotBytecode p17 = some (.DUP3, .none)
  ∧ decode spotBytecode p18 = some (.ADD, .none)
  ∧ decode spotBytecode p19 = some (.MSTORE, .none)
  ∧ decode spotBytecode p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode spotBytecode p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode spotBytecode p24 = some (.DUP3, .none)
  ∧ decode spotBytecode p25 = some (.ADD, .none)
  ∧ decode spotBytecode p26 = some (.MSTORE, .none)
  ∧ decode spotBytecode p27 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode spotBytecode p29 = some (.DUP1, .none)
  ∧ decode spotBytecode p30 = some (.MLOAD, .none)
  ∧ decode spotBytecode p31 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode spotBytecode p33 = some (.Push .PUSH2, some (offset, 2))
  ∧ decode spotBytecode p36 = some (.DUP4, .none)
  ∧ decode spotBytecode p37 = some (.CODECOPY, .none)
  ∧ decode spotBytecode p38 = some (.DUP2, .none)
  ∧ decode spotBytecode p39 = some (.MLOAD, .none)
  ∧ decode spotBytecode p40 = some (.SWAP2, .none)
  ∧ decode spotBytecode p41 = some (.MSTORE, .none)
  ∧ decode spotBytecode p42 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode spotBytecode p44 = some (.DUP3, .none)
  ∧ decode spotBytecode p45 = some (.ADD, .none)
  ∧ decode spotBytecode p46 = some (.MSTORE, .none)
  ∧ decode spotBytecode p47 = some (.SWAP1, .none)
  ∧ decode spotBytecode p48 = some (.MLOAD, .none)
  ∧ decode spotBytecode p49 = some (.SWAP1, .none)
  ∧ decode spotBytecode p50 = some (.DUP2, .none)
  ∧ decode spotBytecode p51 = some (.SWAP1, .none)
  ∧ decode spotBytecode p52 = some (.SUB, .none)
  ∧ decode spotBytecode p53 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode spotBytecode p55 = some (.ADD, .none)
  ∧ decode spotBytecode p56 = some (.SWAP1, .none)
  ∧ decode spotBytecode p57 = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.spotCodecopyAuthRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (offset len : UInt256)
    (h : RD spotBytecode ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : spotCodecopyAuthRevertTailWf pc offset len)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrc : offset.toNat + 32 ≤ spotBytecode.size)
    (hov : stk.length + 7 ≤ 1024) :
    RDrev spotBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd29, hd30, hd31, hd33,
      hd36, hd37, hd38, hd39, hd40, hd41, hd42, hd44, hd45, hd46, hd47,
      hd48, hd49, hd50, hd51, hd52, hd53, hd55, hd56, hd57⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨0⟩ hd27 (by evm_ov),
    raw dup1 hd29 (by evm_ov)]
  let scratchWord : UInt256 :=
    UInt256.ofNat (fromByteArrayBigEndian ((solcErrorStringMem2 len mem).readWithPadding 0 32))
  have rdScratch := rdPrefix.mload 0 scratchWord (UInt256.ofNat 7) hd30 mem_cost
    (by
      dsimp [scratchWord]
      exact mloadValue_eq_readWithPadding_of_lt_size
        (solcErrorStringMem2 len mem) (UInt256.ofNat 7) (⟨0⟩ : UInt256) 196
        (solcErrorStringMem2_size len hmem) (by decide) (by decide))
    (by decide) (by evm_ov)
  have rdCopyPre := evm_run rdScratch with [
    raw push1 ⟨32⟩ hd31 (by evm_ov),
    raw push2 offset hd33
      (by simp only [List.length_cons]; omega),
    raw dup4 hd36
      (by simp only [List.length_cons]; omega)]
  have hcopy :
      spotBytecode.write offset.toNat (solcErrorStringMem2 len mem) 0 32 =
        spotCodecopyErrorScratchMem offset len mem := by
    rfl
  have rdCopy := rdCopyPre.codecopy 0 (spotCodecopyErrorScratchMem offset len mem)
    (UInt256.ofNat 7) hd37
    (fun s haws hstk => by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    hcopy
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  let copiedWord : UInt256 :=
    UInt256.ofNat
      (fromByteArrayBigEndian
        ((spotCodecopyErrorScratchMem offset len mem).readWithPadding 0 32))
  have rdCopiedWord := rdCopy.dup2 hd38 (by evm_ov)
    |>.mload 0 copiedWord (UInt256.ofNat 7) hd39 mem_cost
      (by
        dsimp [copiedWord]
        exact mloadValue_eq_readWithPadding_of_lt_size
          (spotCodecopyErrorScratchMem offset len mem) (UInt256.ofNat 7)
          (⟨0⟩ : UInt256) 196
          (spotCodecopyErrorScratchMem_size offset len hmem hsrc)
          (by decide)
          (by decide))
      (by decide) (by evm_ov)
    |>.swap2 hd40 (by evm_ov)
    |>.mstore 0 (spotCodecopyErrorRestoreMem offset len scratchWord mem)
      (UInt256.ofNat 7) hd41 mem_cost (by rfl) (by native_decide) (by evm_ov)
  exact evm_run rdCopiedWord with [
    raw push1 ⟨68⟩ hd42 (by evm_ov),
    raw dup3 hd44 (by evm_ov),
    raw add hd45 (by evm_ov),
    raw mstore 3 (spotCodecopyErrorFinalMem offset len scratchWord copiedWord mem)
      (UInt256.ofNat 8) hd46 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 hd47 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd48 mem_cost
      (spotCodecopyErrorFinalMem_mload64 offset len scratchWord copiedWord hmem hread64 hsrc)
      (by decide) (by evm_ov),
    raw swap1 hd49 (by evm_ov),
    raw dup2 hd50 (by evm_ov),
    raw swap1 hd51 (by evm_ov),
    raw sub hd52 (by evm_ov),
    raw push1 ⟨100⟩ hd53 (by evm_ov),
    raw add hd55 (by evm_ov),
    raw swap1 hd56 (by evm_ov),
    raw rev 0 hd57 mem_cost (by evm_ov)]

theorem spotReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 9)) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨354⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : spotSelWord I = ⟨0x65fae35e⟩ :=
    spotSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc 5))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachLowBody 5 (by omega) ⟨354⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem spotRelyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨354⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1468⟩
        [relyGuyMaskedWord I, ⟨214⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := spotBytecode) (sel := sel) (entry := ⟨354⟩) (ret := ⟨214⟩)
    (decoded := ⟨376⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := spotBytecode) (decoded := ⟨376⟩) (ret := ⟨214⟩) (routine := ⟨1468⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [relyGuyMaskedWord, relyGuyWord, calldataWord] using hroutine⟩

theorem spotRelyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨354⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := spotBytecode) (sel := sel) (entry := ⟨354⟩) (ret := ⟨214⟩)
    (decoded := ⟨376⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem spotRelyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1468⟩
      [relyGuyMaskedWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1550⟩
      [relyGuyMaskedWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1474pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1475 := rd1474pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1479pre := evm_run rd1475 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1480 := rd1479pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1483pre := evm_run rd1480 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1484 := rd1483pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1485, C1485, rd1485raw⟩ := rd1484.sload (by native_decide) (by evm_ov)
  have rd1485 : RD spotBytecode I g s0 ⟨1485⟩
      (relyAuthWord σ I :: relyGuyMaskedWord I :: ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1485 C1485 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1485raw
  have rd1488pre := evm_run rd1485 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1488pre
  have rd1491 := rd1488pre.pushConst (⟨1550⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1491.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem spotRelyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1468⟩
      [relyGuyMaskedWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1474pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1475 := rd1474pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1479pre := evm_run rd1475 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1480 := rd1479pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1483pre := evm_run rd1480 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1484 := rd1483pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1485, C1485, rd1485raw⟩ := rd1484.sload (by native_decide) (by evm_ov)
  have rd1485 : RD spotBytecode I g s0 ⟨1485⟩
      (relyAuthWord σ I :: relyGuyMaskedWord I :: ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1485 C1485 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1485raw
  have rd1488pre := evm_run rd1485 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1488pre
  have rd1491 := rd1488pre.pushConst (⟨1550⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1492 := rd1491.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.spotCodecopyAuthRevertTail ⟨2134⟩ ⟨22⟩ rd1492
    (by
      unfold spotCodecopyAuthRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem spotRelyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD spotBytecode I g s0 ⟨1550⟩
      [relyGuyMaskedWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret spotBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (relyGuyStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (relyGuyMaskedWord I) ⟨0⟩ := by
    simpa [relyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relyGuyMaskedWord I)
        (relyAuthHashMem_size I)
  have rd1559pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (relyGuyMaskedWord I)
        = relyGuyMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (relyGuyMaskedWord_canonical I)
  rw [hmask] at rd1559pre
  have rd1564pre := evm_run rd1559pre with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1565 := rd1564pre.mstore 0
    (wordAt0Mem (relyGuyMaskedWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1569pre := evm_run rd1565 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1570 := rd1569pre.mstore 0 (relyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1573pre := evm_run rd1570 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1574 := rd1573pre.keccak256 0 (mapSlot (relyGuyMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rd1577pre := evm_run rd1574 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1578raw⟩ := rd1577pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd214 := rd1578raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd215 := rd214.jumpdest (by native_decide) (by evm_ov)
  simpa [relyGuyStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd215 (by native_decide) (by evm_ov)

theorem spotX_rely_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨354⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret spotBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (relyGuyStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd1468⟩ := spotRelyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd1550⟩ := spotRelyX_authorized (I := I) hauth rd1468
  exact spotRelyX_storeAuthorized hperm rd1550

theorem spotX_rely_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨354⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1468⟩ := spotRelyX_decoded (g := g) hsz36 hsize hreach
  exact spotRelyX_unauthorized (I := I) hauth rd1468

theorem spotRelyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨354⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body
        (.returned { contract := contract, locals := relyStore I }
          (relyPostState evmSolm I) none) := by
    simpa [evmSolm, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      spotRelyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (spotX_rely_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [relyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [relyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (relyGuyStorageSlot I) ⟨1⟩
            hAccounts)
      (by
        simpa [relyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem spotRelyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨354⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      spotRelyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (spotX_rely_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotRelyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨354⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (spotRelyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (spotDecode_rely_none_short hsz4 hshort)

theorem spotRelyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 9) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    spotDispatchRely hsel
  have hreach := spotReachRelyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · exact spotRelyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (spotDecode_rely_ok hsz36) hreach hAccounts
    · exact spotRelyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (spotDecode_rely_ok hsz36) hreach hAccounts
  · exact spotRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Spot
