import Benchmarks.Dss.Cure.Common
import Benchmarks.Dss.Cure.Cage
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

set_option maxRecDepth 2000000

/-! ## `load(address)` -/

abbrev loadSrc (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev loadLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "src" (.address (loadSrc I))

abbrev loadKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev loadPosEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "pos", steps := [.mindex (.address (loadSrc I))] }

abbrev loadPosSlotFor (I : ExecutionEnv) : UInt256 :=
  posSlot (.address (loadSrc I))

abbrev loadAmtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "amt", steps := [.mindex (.address (loadSrc I))] }

abbrev loadAmtSlotFor (I : ExecutionEnv) : UInt256 :=
  amtSlot (.address (loadSrc I))

abbrev loadSayEvaledRef : EvaledStorageRef :=
  { base := "say", steps := [] }

abbrev loadLoadedEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "loaded", steps := [.mindex (.address (loadSrc I))] }

abbrev loadLoadedSlotFor (I : ExecutionEnv) : UInt256 :=
  loadedSlot (.address (loadSrc I))

abbrev loadLCountEvaledRef : EvaledStorageRef :=
  { base := "lCount", steps := [] }

theorem loadPosSlotFor_eq (I : ExecutionEnv) :
    loadPosSlotFor I = solcMappingSlot ⟨5⟩ (loadKey I) := by
  unfold loadPosSlotFor loadSrc loadKey posSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem loadAmtSlotFor_eq (I : ExecutionEnv) :
    loadAmtSlotFor I = solcMappingSlot ⟨6⟩ (loadKey I) := by
  unfold loadAmtSlotFor loadSrc loadKey amtSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem loadLoadedSlotFor_eq (I : ExecutionEnv) :
    loadLoadedSlotFor I = solcMappingSlot ⟨7⟩ (loadKey I) := by
  unfold loadLoadedSlotFor loadSrc loadKey loadedSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem loadKey_address_eq (I : ExecutionEnv) :
    AccountAddress.ofUInt256 (loadKey I) = loadSrc I := by
  unfold loadKey loadSrc
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  let w := calldataWord I.calldata 4
  change (UInt256.land solcAddrMask w).toNat % AccountAddress.size =
    w.toNat % AccountAddress.size
  rw [uland_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [show 2 ^ 160 - 1 &&& w.toNat = Nat.land w.toNat (2 ^ 160 - 1) from
    Nat.land_comm _ _]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  rw [Nat.mod_mod]

theorem evalExpr_loadLiveEqZero_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := loadLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [evalExpr_storage_scalar
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := wordLoc ⟨1⟩)]
    · rw [cureStorageLocLoad_uint256]
      rw [hlive]
      simp only [evalExpr?, pure]
      decide +native
    · simp [loadLocals, liveRef]
    · simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    · simp [storageTypeAt?, contract, storageDecls, uint256St]
    · funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]
  · decide +native
  · decide +native

theorem evalExpr_loadLiveEqZero_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := loadLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [evalExpr_storage_scalar
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := wordLoc ⟨1⟩)]
    · rw [cureStorageLocLoad_uint256]
      simp only [evalExpr?, pure]
      change EvalResult.ok (Value.bool
          ((Value.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) ==
            (Value.int 0))) = EvalResult.ok (Value.bool false)
      congr
      rw [Bool.eq_false_iff]
      intro hbeq
      simp at hbeq
      apply hlive
      apply u256_inj
      simpa using hbeq
    · simp [loadLocals, liveRef]
    · simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
    · simp [storageTypeAt?, contract, storageDecls, uint256St]
    · funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]
  · decide +native
  · decide +native

theorem evalExpr_loadPosStorage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := loadLocals I } evm
      (.storage (posRef (.var "src"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadPosSlotFor I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := loadPosEvaledRef I) (t := .int uint256Int) (loc := wordLoc (loadPosSlotFor I))]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm (loadPosSlotFor I))
  · simp [loadLocals, posRef]
  · simp [loadPosEvaledRef, loadSrc, posRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, loadLocals]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      loadPosEvaledRef, loadPosSlotFor]

theorem evalExpr_loadAmtStorage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := loadLocals I } evm
      (.storage (amtRef (.var "src"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadAmtSlotFor I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := loadAmtEvaledRef I) (t := .int uint256Int) (loc := wordLoc (loadAmtSlotFor I))]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm (loadAmtSlotFor I))
  · simp [loadLocals, amtRef]
  · simp [loadAmtEvaledRef, loadSrc, amtRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, loadLocals]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      loadAmtEvaledRef, loadAmtSlotFor]

theorem evalExpr_loadSayStorage {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "say" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage sayRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := loadSayEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨9⟩)]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm ⟨9⟩)
  · exact hbase
  · simp [loadSayEvaledRef, sayRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, loadSayEvaledRef]

theorem evalExpr_loadLoadedStorage {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hbase : locals.get? "loaded" = none)
    (hsrc : locals.get? "src" = some (.address (loadSrc I))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (loadedRef (.var "src"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (loadLoadedSlotFor I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := loadLoadedEvaledRef I) (t := .int uint256Int)
    (loc := wordLoc (loadLoadedSlotFor I))]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm (loadLoadedSlotFor I))
  · exact hbase
  · have hvar :
        evalExpr? config { contract := contract, locals := locals } evm (.var "src") =
          .ok (.address (loadSrc I)) := by
      rw [evalExpr?]
      change EvalResult.ofOption EvalError.unboundVariable (locals.get? "src") =
        .ok (.address (loadSrc I))
      rw [hsrc]
      rfl
    simp [loadLoadedEvaledRef, loadedRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, hvar, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, loadSrc]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      loadLoadedEvaledRef, loadLoadedSlotFor]

theorem evalExpr_loadLoadedEqZero_true {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hbase : locals.get? "loaded" = none)
    (hsrc : locals.get? "src" = some (.address (loadSrc I)))
    (hloaded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadLoadedSlotFor I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0)) = .ok (.bool true) := by
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [evalExpr_loadLoadedStorage (evm := evm) (locals := locals) I hbase hsrc]
    rw [hloaded]
    simp [evalExpr?, pure]
    decide +native
  · decide +native
  · decide +native

theorem evalExpr_loadLoadedEqZero_false {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hbase : locals.get? "loaded" = none)
    (hsrc : locals.get? "src" = some (.address (loadSrc I)))
    (hloaded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadLoadedSlotFor I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0)) = .ok (.bool false) := by
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [evalExpr_loadLoadedStorage (evm := evm) (locals := locals) I hbase hsrc]
    simp only [evalExpr?, pure]
    change EvalResult.ok (Value.bool
        ((Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadLoadedSlotFor I)).toNat)) ==
          (Value.int 0))) = EvalResult.ok (Value.bool false)
    congr
    rw [Bool.eq_false_iff]
    intro hbeq
    simp at hbeq
    apply hloaded
    apply u256_inj
    simpa using hbeq
  · decide +native
  · decide +native

theorem evalExpr_loadLCountStorage {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "lCount" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage lCountRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := loadLCountEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨8⟩)]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm ⟨8⟩)
  · exact hbase
  · simp [loadLCountEvaledRef, lCountRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, loadLCountEvaledRef]

theorem evalExpr_incUncheckedLCount {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "lCount" = none) :
    let count := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩
    evalExpr? config { contract := contract, locals := locals } evm
      (incUnchecked (.storage lCountRef)) =
        .ok (.int (Int.ofNat (count + ⟨1⟩).toNat)) := by
  intro count
  have hcount := evalExpr_loadLCountStorage (evm := evm) (locals := locals) hbase
  have hmodNat : (count.toNat + 1) % UInt256.size = (count + ⟨1⟩).toNat := by
    rw [uadd_toNat]
    rfl
  have hmodInt :
      (Int.ofNat count.toNat + 1) % wordModulus =
        Int.ofNat (count + ⟨1⟩).toNat := by
    have haddCast : Int.ofNat count.toNat + 1 = Int.ofNat (count.toNat + 1) := by
      norm_num
    rw [haddCast]
    rw [wordModulus, show (2 : Int) ^ 256 = Int.ofNat UInt256.size by
      norm_num [UInt256.size]]
    rw [show Int.ofNat (count.toNat + 1) % Int.ofNat UInt256.size =
        Int.ofNat ((count.toNat + 1) % UInt256.size) by
      simpa using (Int.natCast_mod (count.toNat + 1) UInt256.size).symm]
    rw [hmodNat]
  simp [incUnchecked, wrap256, evalExpr?, EvalResult.bind, bind, hcount, evalBinaryOp?,
    wordModulus]
  change (Int.ofNat count.toNat + 1) % wordModulus =
    Int.ofNat (count + ⟨1⟩).toNat
  exact hmodInt

theorem assign_loadAmtStorage {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (newAmt : UInt256)
    (hbase : locals.get? "amt" = none)
    (hsrc : locals.get? "src" = some (.address (loadSrc I))) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (loadAmtSlotFor I) newAmt
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (amtRef (.var "src")) (.int (Int.ofNat newAmt.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (loadAmtSlotFor I))
    (er := loadAmtEvaledRef I)
    (hbase := hbase)
    (her := by
      have hvar :
          evalExpr? config { contract := contract, locals := locals } evm (.var "src") =
            .ok (.address (loadSrc I)) := by
        rw [evalExpr?]
        change EvalResult.ofOption EvalError.unboundVariable (locals.get? "src") =
          .ok (.address (loadSrc I))
        rw [hsrc]
        rfl
      unfold loadAmtEvaledRef amtRef evalStorageRef evalStorageRefSteps evalStorageRefStep
      simp [hvar, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind, loadSrc])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        loadAmtEvaledRef, loadAmtSlotFor])
    (hstore := by simpa [evm'] using storageLocStore_uint256 evm (loadAmtSlotFor I) newAmt)

theorem assign_loadSayStorage {evm : EVM.State} {locals : Store} (sayNew : UInt256)
    (hbase : locals.get? "say" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩ sayNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage sayRef (.int (Int.ofNat sayNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨9⟩)
    (er := loadSayEvaledRef)
    (hbase := hbase)
    (her := by simp [loadSayEvaledRef, sayRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, loadSayEvaledRef])
    (hstore := by simpa [evm'] using storageLocStore_uint256 evm ⟨9⟩ sayNew)

theorem assign_loadLoadedStorage {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (value : UInt256)
    (hbase : locals.get? "loaded" = none)
    (hsrc : locals.get? "src" = some (.address (loadSrc I))) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (loadLoadedSlotFor I) value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (loadedRef (.var "src")) (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (loadLoadedSlotFor I))
    (er := loadLoadedEvaledRef I)
    (hbase := hbase)
    (her := by
      have hvar :
          evalExpr? config { contract := contract, locals := locals } evm (.var "src") =
            .ok (.address (loadSrc I)) := by
        rw [evalExpr?]
        change EvalResult.ofOption EvalError.unboundVariable (locals.get? "src") =
          .ok (.address (loadSrc I))
        rw [hsrc]
        rfl
      simp [loadLoadedEvaledRef, loadedRef, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, hvar, valueToKey?, EvalResult.ofOption, EvalResult.bind,
        pure, bind, loadSrc])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        loadLoadedEvaledRef, loadLoadedSlotFor])
    (hstore := by simpa [evm'] using storageLocStore_uint256 evm (loadLoadedSlotFor I) value)

theorem assign_loadLCountStorage {evm : EVM.State} {locals : Store} (value : UInt256)
    (hbase : locals.get? "lCount" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage lCountRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨8⟩)
    (er := loadLCountEvaledRef)
    (hbase := hbase)
    (her := by simp [loadLCountEvaledRef, lCountRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, loadLCountEvaledRef])
    (hstore := by simpa [evm'] using storageLocStore_uint256 evm ⟨8⟩ value)

theorem execLoadLoadedZeroTail {evm : EVM.State} {locals : Store} (I : ExecutionEnv)
    (hbaseLoaded : locals.get? "loaded" = none)
    (hbaseLCount : locals.get? "lCount" = none)
    (hsrc : locals.get? "src" = some (.address (loadSrc I)))
    (hloaded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadLoadedSlotFor I) = ⟨0⟩) :
    let evmLoaded := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (loadLoadedSlotFor I) ⟨1⟩
    let count := Solm.EVM.storageLoad evmLoaded evmLoaded.executionEnv.codeOwner ⟨8⟩
    let evmCount := Solm.EVM.storageStore evmLoaded evmLoaded.executionEnv.codeOwner
      ⟨8⟩ (count + ⟨1⟩)
    ExecStmt config { contract := contract, locals := locals } evm
      (.ite
        (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
        [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
          .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
        [])
      (.ok { contract := contract, locals := locals } evmCount) := by
  intro evmLoaded count evmCount
  have hcond :=
    evalExpr_loadLoadedEqZero_true (evm := evm) (locals := locals) I
      hbaseLoaded hsrc hloaded
  have hassignLoaded :
      assignStorageRef? config { contract := contract, locals := locals } evm
        .storage (loadedRef (.var "src")) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evmLoaded) := by
    simpa [evmLoaded] using assign_loadLoadedStorage (evm := evm) (locals := locals)
      I ⟨1⟩ hbaseLoaded hsrc
  have hinc :
      evalExpr? config { contract := contract, locals := locals } evmLoaded
        (incUnchecked (.storage lCountRef)) =
          .ok (.int (Int.ofNat (count + ⟨1⟩).toNat)) := by
    simpa [count] using evalExpr_incUncheckedLCount (evm := evmLoaded)
      (locals := locals) hbaseLCount
  have hassignCount :
      assignStorageRef? config { contract := contract, locals := locals } evmLoaded
        .storage lCountRef (.int (Int.ofNat (count + ⟨1⟩).toNat)) =
          .ok ({ contract := contract, locals := locals }, evmCount) := by
    simpa [evmCount] using assign_loadLCountStorage (evm := evmLoaded)
      (locals := locals) (count + ⟨1⟩) hbaseLCount
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
          .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
        (.ok { contract := contract, locals := locals } evmCount) := by
    refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignLoaded) ?_
    · simp [evalExpr?, pure]
    exact ExecBlock.consNormal (ExecStmt.assign hinc hassignCount) ExecBlock.nil
  exact ExecStmt.iteTrue hcond hthen

theorem evalExpr_loadPosGtZero_false (evm : EVM.State) (I : ExecutionEnv)
    (hpos : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadPosSlotFor I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := loadLocals I } evm
      (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) = .ok (.bool false) := by
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [evalExpr_loadPosStorage evm I]
    rw [hpos]
    simp only [evalExpr?, pure]
    decide +native
  · decide +native
  · decide +native

theorem evalExpr_loadPosGtZero_true (evm : EVM.State) (I : ExecutionEnv)
    (hpos : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := loadLocals I } evm
      (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) = .ok (.bool true) := by
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [evalExpr_loadPosStorage evm I]
    simp only [evalExpr?, pure]
    simp only [evalBinaryOp?]
    have hposNat :
        0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadPosSlotFor I)).toNat :=
      Nat.pos_of_ne_zero (by
        intro hzero
        apply hpos
        apply u256_inj
        simpa using hzero)
    have hposInt :
        (0 : Int) < Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadPosSlotFor I)).toNat := by
      exact Int.natCast_pos.mpr hposNat
    rw [show decide (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadPosSlotFor I)).toNat > 0) =
        true from by
          exact decide_eq_true (show Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (loadPosSlotFor I)).toNat >
              0 from hposInt)]
  · decide +native
  · decide +native

theorem evalExpr_loadExtCodeSizeGtZero_false_of_src {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store}
    (hsrc : locals.get? "src" = some (.address (loadSrc I)))
    (hnoCode : extCodeSizeWord σ (loadKey I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool false) := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.var "src") = .ok (.address (loadSrc I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption .unboundVariable (locals.get? "src") =
      .ok (.address (loadSrc I))
    rw [hsrc]
    rfl
  have hcodeWord :
      EVM.Word.ofNat ((evm0.lookupAccount (loadSrc I)).option 0 (fun acc => acc.code.size)) =
        ⟨0⟩ := by
    change EVM.Word.ofNat
      ((σ.find? (loadSrc I)).option 0 (fun acc => acc.code.size)) = ⟨0⟩
    cases hacc : σ.find? (loadSrc I) with
    | none =>
        rfl
    | some acc =>
        have hnoAcc : UInt256.ofNat acc.code.size = ⟨0⟩ := by
          simpa [extCodeSizeWord, loadKey_address_eq I, hacc] using hnoCode
        simpa [hacc] using hnoAcc
  have hext :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.extCodeSize (.var "src")) = .ok (.int 0) := by
    rw [evalExpr?]
    simp only [EvalResult.bind, bind]
    rw [hvar]
    simp only [pure]
    rw [hcodeWord]
    rfl
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [hext]
    simp only [evalExpr?, pure]
    decide +native
  · decide +native
  · decide +native

theorem evalExpr_loadExtCodeSizeGtZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnoCode : extCodeSizeWord σ (loadKey I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := loadLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool false) := by
  exact evalExpr_loadExtCodeSizeGtZero_false_of_src
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (locals := loadLocals I) (by simp [loadLocals]) hnoCode

theorem evalExpr_loadExtCodeSizeGtZero_true_of_src {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store}
    (hsrc : locals.get? "src" = some (.address (loadSrc I)))
    (hcode : extCodeSizeWord σ (loadKey I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool true) := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.var "src") = .ok (.address (loadSrc I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption .unboundVariable (locals.get? "src") =
      .ok (.address (loadSrc I))
    rw [hsrc]
    rfl
  have hcodeWordNe :
      EVM.Word.ofNat ((evm0.lookupAccount (loadSrc I)).option 0 (fun acc => acc.code.size)) ≠
        ⟨0⟩ := by
    change UInt256.ofNat
      ((σ.find? (loadSrc I)).option 0 (fun acc => acc.code.size)) ≠ ⟨0⟩
    cases hacc : σ.find? (loadSrc I) with
    | none =>
        exact False.elim (hcode (by simp [extCodeSizeWord, loadKey_address_eq I, hacc, Option.option]))
    | some acc =>
        simpa [extCodeSizeWord, loadKey_address_eq I, hacc] using hcode
  have hcodePos :
      0 < (EVM.Word.ofNat
        ((evm0.lookupAccount (loadSrc I)).option 0 (fun acc => acc.code.size))).toNat :=
    Nat.pos_of_ne_zero (by
      intro hzero
      apply hcodeWordNe
      apply u256_inj
      simpa using hzero)
  have hext :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.extCodeSize (.var "src")) =
          .ok (.int (Int.ofNat
            (EVM.Word.ofNat
              ((evm0.lookupAccount (loadSrc I)).option 0 (fun acc => acc.code.size))).toNat)) := by
    rw [evalExpr?]
    simp only [EvalResult.bind, bind]
    rw [hvar]
    rfl
  rw [evalExpr?]
  · simp only [EvalResult.bind, bind]
    rw [hext]
    simp only [evalExpr?, pure]
    simp [evalBinaryOp?, hcodePos]
  · decide +native
  · decide +native

abbrev sourceCureSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨2215084781⟩ ⟨224⟩

noncomputable def loadCureSelectorMem (mem : ByteArray) : ByteArray :=
  sourceCureSelectorShifted.toByteArray.write 0 mem 128 32

theorem loadCureSelectorMem_size_of_size96 {mem : ByteArray} (hmem : mem.size = 96) :
    (loadCureSelectorMem mem).size = 160 := by
  unfold loadCureSelectorMem
  exact toByteArray_write32_size_of_ge mem sourceCureSelectorShifted 128 96 160 hmem
    (by omega) (by decide +native) (by omega)

theorem loadCureSelectorMem_read64_of_size96 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (loadCureSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold loadCureSelectorMem
  have hreadBound : 64 + 32 ≤ mem.size := by
    rw [hmem]
  have hpreserve :
      ((UInt256.toByteArray sourceCureSelectorShifted).write 0 mem 128 32).readWithPadding
          64 32 =
        mem.readWithPadding 64 32 :=
    toByteArray_write_read_below_of_gap sourceCureSelectorShifted mem 128 64
      (hread := hreadBound)
      (hbelow := by decide +native)
      (hgap := by rw [hmem]; decide +native)
  rw [hpreserve, hread64]

theorem loadCureSelectorMem_read128_4 {mem : ByteArray} (hmem : mem.size = 96) :
    (loadCureSelectorMem mem).readWithPadding 128 4 = sourceCureSelector := by
  unfold loadCureSelectorMem sourceCureSelector
  rw [toByteArray_write_read_window_of_gap sourceCureSelectorShifted mem 128 0 4
    (by decide) (by decide) (by decide) (by rw [hmem]; decide +native)]
  decide +native

theorem loadCureEncode_eq {mem : ByteArray} (hmem : mem.size = 96) :
    config.externalABI.encode? "cure" [] =
      some ((loadCureSelectorMem mem).readWithPadding 128 4) := by
  rw [loadCureSelectorMem_read128_4 hmem]
  rfl

theorem loadCureDecode_ok {o : ByteArray} (ho32 : 32 ≤ o.size) :
    config.externalABI.decode? "cure" o =
      some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)] := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_ok (returndata := o) ho32
  have hlt := fromByteArrayBigEndian_extract0_32_lt (returndata := o) ho32
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o =
        some (.int (Int.ofNat (fromByteArrayBigEndian (o.extract 0 32)))) := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o =
    some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)]
  unfold decodeReturn?
  rw [hdec']
  simp [UInt256.toNat_ofNat_of_lt hlt, Int.ofNat_eq_natCast]

theorem loadCureDecode_none_short {o : ByteArray} (hshort : o.size < 32) :
    config.externalABI.decode? "cure" o = none := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o) hshort
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o = none
  unfold decodeReturn?
  rw [hdec']
  rfl

theorem loadCureMin32_toNat_of_lt {n : ℕ} (h : n < 32) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = n := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = n
  have hnsize : n < UInt256.size := by
    have h32 : 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  rw [if_neg, ulit_toNat' n hnsize]
  · show ¬ (32 : ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ulit_toNat' n hnsize]
    omega

theorem loadCureMin32_toNat_of_ge {n : ℕ}
    (h32 : 32 ≤ n) (hsize : n < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = 32 := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = 32
  rw [if_pos]
  · rfl
  · show (32 : ℕ) ≤ (UInt256.ofNat n).toNat
    rw [ulit_toNat' n hsize]
    exact h32

theorem loadCureReturnWrite_size {base o : ByteArray} {L : ℕ}
    (hbase : base.size = 160) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).size = 160 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen o base 128 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem loadCureReturnWrite_read64 {base o : ByteArray} {L : ℕ}
    (hbase : base.size = 160)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen o base 128 L 64 (by omega) hLo
      (by rw [hbase]; omega) (by omega), hread64]

theorem loadCureReturnWrite_read128_32 {base o : ByteArray}
    (hbase : base.size = 160) (ho32 : 32 ≤ o.size) :
    (o.write 0 base 128 32).readWithPadding 128 32 = o.extract 0 32 :=
  write32_read_back o base 128 ho32 (by rw [hbase]; omega)

theorem wordAt0Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt0Mem word mem).size = 160 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt32Mem word mem).size = 160 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem twoWordHashMem_size_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).size = 160 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_160 slot (wordAt0Mem_size_160 key hmem)

theorem twoWordHashMem_read0_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_160 key hmem]; norm_num)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; norm_num)]
  exact hread64

theorem twoWordHashMem_read0_64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_160 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_160 key slot hmem]; omega),
      twoWordHashMem_read0_160 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_160 key slot hmem]; omega),
      twoWordHashMem_read32_160 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem twoWordHashMem_solcMappingSlot_160 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_160 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem solcErrorStringMem0_size_of_size160 {mem : ByteArray} (hmem : mem.size = 160) :
    (solcErrorStringMem0 mem).size = 160 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem, toByteArray_size]

theorem solcErrorStringMem1_size_of_size160 {mem : ByteArray} (hmem : mem.size = 160) :
    (solcErrorStringMem1 mem).size = 164 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem0_size_of_size160 hmem,
    toByteArray_size]

theorem solcErrorStringMem2_size_of_size160 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size160 hmem])]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem1_size_of_size160 hmem,
    toByteArray_size]

theorem solcErrorStringMem3_size_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size160 len hmem])]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem2_size_of_size160 len hmem,
    toByteArray_size]

theorem solcErrorStringMem3_read64_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size160 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size160 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size160 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size160 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size160 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size160 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size160 len word hmem]; decide)
    (by decide) (solcErrorStringMem3_read64_of_size160 len word hmem hread64)


end Benchmarks.Dss.Cure
