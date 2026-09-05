import Benchmarks.Dss.Clipper.KickEventEVM
import Benchmarks.Dss.Clipper.Guards
import Benchmarks.Dss.Clipper.Count
import Benchmarks.Dss.Clipper.RedoDoneSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! Source-side state names for the storage-initialization prefix of `kick`. -/

def clipperKickLockedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩

abbrev clipperKickSourceIdWord (evm : EVM.State) : UInt256 :=
  ⟨1⟩ + Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩

def clipperKickSourceIdState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩
    (clipperKickSourceIdWord evm)

abbrev clipperKickSourceActiveLengthWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad (clipperKickSourceIdState evm)
    evm.executionEnv.codeOwner ⟨11⟩

def clipperKickSourceActiveLengthState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (clipperKickSourceIdState evm)
    (clipperKickSourceIdState evm).executionEnv.codeOwner ⟨11⟩
    (clipperKickSourceActiveLengthWord evm + ⟨1⟩)

abbrev clipperKickSourceActiveElemSlot (evm : EVM.State) : UInt256 :=
  activeDataSlot + clipperKickSourceActiveLengthWord evm

def clipperKickSourceActiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (clipperKickSourceActiveLengthState evm)
    (clipperKickSourceActiveLengthState evm).executionEnv.codeOwner
    (clipperKickSourceActiveElemSlot evm) (clipperKickSourceIdWord evm)

abbrev clipperKickSourcePostPushLengthWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad (clipperKickSourceActiveState evm)
    (clipperKickSourceActiveState evm).executionEnv.codeOwner ⟨11⟩

abbrev clipperKickSourceActivePosWord (evm : EVM.State) : UInt256 :=
  UInt256.sub (clipperKickSourcePostPushLengthWord evm) ⟨1⟩

abbrev clipperKickSourceIdKey (evm : EVM.State) : KeyValue :=
  .int (Int.ofNat (clipperKickSourceIdWord evm).toNat)

abbrev clipperKickSourceSalesBaseSlot (evm : EVM.State) : UInt256 :=
  salesBase (clipperKickSourceIdKey evm)

def clipperKickSourceSalesPosState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (clipperKickSourceActiveState evm)
    (clipperKickSourceActiveState evm).executionEnv.codeOwner
    (clipperKickSourceSalesBaseSlot evm) (clipperKickSourceActivePosWord evm)

def clipperKickSourceSalesTabState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (clipperKickSourceSalesPosState evm)
    (clipperKickSourceSalesPosState evm).executionEnv.codeOwner
    (clipperKickSourceSalesBaseSlot evm + ⟨1⟩) (clipperKickTabWord I)

def clipperKickSourceSalesLotState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (clipperKickSourceSalesTabState evm I)
    (clipperKickSourceSalesTabState evm I).executionEnv.codeOwner
    (clipperKickSourceSalesBaseSlot evm + ⟨2⟩) (clipperKickLotWord I)

def clipperKickSourceSalesUsrState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (clipperKickSourceSalesLotState evm I)
    (clipperKickSourceSalesLotState evm I).executionEnv.codeOwner
    (clipperKickSourceSalesBaseSlot evm + ⟨3⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad (clipperKickSourceSalesLotState evm I)
        (clipperKickSourceSalesLotState evm I).executionEnv.codeOwner
        (clipperKickSourceSalesBaseSlot evm + ⟨3⟩))
      (clipperKickUsrMaskedWord I))

def clipperKickSourceInitializedState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  let evmUsr := clipperKickSourceSalesUsrState evm I
  let ticWord := UInt256.land (UInt256.ofNat evmUsr.executionEnv.header.timestamp)
    clipperSalesUint96Mask
  Solm.EVM.storageStore evmUsr evmUsr.executionEnv.codeOwner
    (clipperKickSourceSalesBaseSlot evm + ⟨3⟩)
    (UInt256.lor
      (UInt256.mul
        (UInt256.land ticWord clipperSalesUint96Mask)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
      (UInt256.land
        (Solm.EVM.storageLoad evmUsr evmUsr.executionEnv.codeOwner
          (clipperKickSourceSalesBaseSlot evm + ⟨3⟩)) solcAddrMask))

abbrev clipperKickLocalsId (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperKickStore I).insert "id"
    (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat))

abbrev clipperKickLocalsActivePos (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (clipperKickLocalsId evm I).insert "activePos"
    (.int (Int.ofNat (clipperKickSourceActivePosWord evm).toNat))

theorem clipperKickStore_get_wards (I : ExecutionEnv) :
    (clipperKickStore I).get? "wards" = none := by
  simp [clipperKickStore]

theorem clipperKickStore_get_locked (I : ExecutionEnv) :
    (clipperKickStore I).get? "locked" = none := by
  simp [clipperKickStore]

theorem clipperKickStore_get_stopped (I : ExecutionEnv) :
    (clipperKickStore I).get? "stopped" = none := by
  simp [clipperKickStore]

theorem clipperKickStore_get_kicks (I : ExecutionEnv) :
    (clipperKickStore I).get? "kicks" = none := by
  simp [clipperKickStore]

theorem clipperKickLocalsId_get_active (evm : EVM.State) (I : ExecutionEnv) :
    (clipperKickLocalsId evm I).get? "active" = none := by
  simp [clipperKickLocalsId, clipperKickStore]

theorem clipperKickLocalsActivePos_get_sales (evm : EVM.State) (I : ExecutionEnv) :
    (clipperKickLocalsActivePos evm I).get? "sales" = none := by
  unfold clipperKickLocalsActivePos clipperKickLocalsId
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp [clipperKickStore]

theorem evalExpr_clipperStopped_lt_one (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "stopped" = none)
    (hload : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat < 1) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .lt (.storage stoppedRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage stoppedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := stoppedRef)
      (er := { base := "stopped", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨14⟩)
      (hbase := hbase)
      (her := by
        simp only [stoppedRef, evalStorageRef, evalStorageRefSteps]
        rfl)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa using clipperStorageLocLoad_uint256 evm ⟨14⟩)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.lt
      (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat))
      (.int 1) = .ok (.bool true)
  simp [evalBinaryOp?]
  omega

theorem clipperEvalKickTabPositive (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : 0 < (clipperKickTabWord I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
      (.binary .gt (.var "tab") (.intLit 0)) = .ok (.bool true) := by
  have htab :
      evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
        (.var "tab") = .ok (clipperKickTabValue I) := by
    simp only [evalExpr?, clipperKickStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
    rfl
  simpa [evalExpr?, htab, clipperKickTabValue, EvalResult.bind, bind,
    evalBinaryOp?] using h

theorem clipperEvalKickLotPositive (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : 0 < (clipperKickLotWord I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
      (.binary .gt (.var "lot") (.intLit 0)) = .ok (.bool true) := by
  have hlot :
      evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
        (.var "lot") = .ok (clipperKickLotValue I) := by
    simp only [evalExpr?, clipperKickStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    rfl
  simpa [evalExpr?, hlot, clipperKickLotValue, EvalResult.bind, bind,
    evalBinaryOp?] using h

theorem clipperEvalKickUsrNonzero (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : clipperKickUsrMaskedWord I ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
      (.binary .ne (.var "usr") zeroAddr) = .ok (.bool true) := by
  have haddr : AccountAddress.ofNat (clipperKickUsrWord I).toNat ≠
      AccountAddress.ofNat 0 := by
    intro heq
    apply h
    calc
      clipperKickUsrMaskedWord I =
          keyValueToWord (.address
            (AccountAddress.ofNat (clipperKickUsrWord I).toNat)) :=
        (keyValueToWord_address_ofNat_mask (clipperKickUsrWord I)).symm
      _ = keyValueToWord (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) :=
        congrArg (fun a : AccountAddress => keyValueToWord (.address a)) heq
      _ = UInt256.land solcAddrMask ⟨0⟩ := keyValueToWord_address_ofNat_mask ⟨0⟩
      _ = ⟨0⟩ := by native_decide
  have husr :
      evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
        (.var "usr") = .ok (clipperKickUsrValue I) := by
    simp only [evalExpr?, clipperKickStore]
    rw [store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
        zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure]
    change EvalResult.ofOption .typeError (castValue? (.int 0) addrSt) =
      .ok (.address (AccountAddress.ofNat 0))
    rfl
  simp only [evalExpr?, husr, hzero, EvalResult.bind, bind]
  change evalBinaryOp? .ne (clipperKickUsrValue I)
    (.address (AccountAddress.ofNat 0)) = .ok (.bool true)
  simp [evalBinaryOp?, clipperKickUsrValue, haddr]

theorem clipperEvalKickIdExpr (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
      (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))) =
      .ok (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) := by
  have hkicks :
      evalExpr? (config v) { contract := contract v, locals := clipperKickStore I } evm
        (.storage kicksRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v) (solm := { contract := contract v, locals := clipperKickStore I })
      (slot := kicksRef) (er := { base := "kicks", steps := [] })
      (t := .int uint256Int) (loc := wordLoc ⟨10⟩)
      (hbase := clipperKickStore_get_kicks I)
      (her := by
        simp only [kicksRef, evalStorageRef, evalStorageRefSteps]
        rfl)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa using clipperStorageLocLoad_uint256 evm ⟨10⟩)
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩
  rw [wrap256]
  simp only [evalExpr?, hkicks, EvalResult.bind, bind, pure]
  change (if wordModulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat old.toNat + 1) % wordModulus))) =
    .ok (Value.int (Int.ofNat (⟨1⟩ + old).toNat))
  rw [if_neg (by norm_num [wordModulus])]
  have hmod :
      (Int.ofNat old.toNat + 1) % wordModulus = Int.ofNat (⟨1⟩ + old).toNat := by
    rw [show Int.ofNat old.toNat + 1 = Int.ofNat (old.toNat + 1) by simp]
    rw [wordModulus]
    rw [show (Int.ofNat (old.toNat + 1)) % (2 : Int) ^ 256 =
        Int.ofNat ((old.toNat + 1) % UInt256.size) by
      exact (Int.natCast_mod (old.toNat + 1) UInt256.size).symm]
    rw [uadd_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by native_decide, Nat.add_comm]
  rw [hmod]

theorem clipperKickAssignId (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    assignStorageRef? (config v)
      { contract := contract v, locals := clipperKickLocalsId evm I }
      evm .storage kicksRef (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) =
      .ok ({ contract := contract v, locals := clipperKickLocalsId evm I },
        clipperKickSourceIdState evm) := by
  apply assignStorageRef_storage_scalar
    (er := { base := "kicks", steps := [] }) (ty := uint256St)
    (loc := wordLoc ⟨10⟩)
  · simp [kicksRef, clipperKickLocalsId, clipperKickStore]
  · simp only [kicksRef, evalStorageRef, evalStorageRefSteps]
    rfl
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · rfl
  · simpa [clipperKickSourceIdState, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm ⟨10⟩ (clipperKickSourceIdWord evm)

theorem clipperEvalKickIdPositive (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : clipperKickSourceIdWord evm ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsId evm I }
      (clipperKickSourceIdState evm)
      (.binary .gt (.var "id") (.intLit 0)) = .ok (.bool true) := by
  have hpos : 0 < (clipperKickSourceIdWord evm).toNat := by
    exact Nat.pos_of_ne_zero (fun hz => h (uint256_toNat_eq_zero hz))
  have hid :
      evalExpr? (config v)
        { contract := contract v, locals := clipperKickLocalsId evm I }
        (clipperKickSourceIdState evm) (.var "id") =
        .ok (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsId, store_get_self, EvalResult.ofOption]
  simpa [evalExpr?, hid, EvalResult.bind, bind, evalBinaryOp?] using hpos

theorem clipperKickPushActive (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hlen : (clipperKickSourceActiveLengthWord evm).toNat + 1 < UInt256.size) :
    pushArray? (config v)
      { contract := contract v, locals := clipperKickLocalsId evm I }
      (clipperKickSourceIdState evm) activeRef
      (some (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat))) =
      .ok (clipperKickSourceActiveState evm) := by
  let evmId := clipperKickSourceIdState evm
  let len := clipperKickSourceActiveLengthWord evm
  let evmLen := clipperKickSourceActiveLengthState evm
  have hresolve :
      resolveStorageRef? (config v)
        { contract := contract v, locals := clipperKickLocalsId evm I }
        evmId activeRef =
      .ok (({ base := "active", steps := [] } : EvaledStorageRef),
        .dynamicArray uint256St) := by
    have hactiveElem : (clipperKickLocalsId evm I)["active"]? = none := by
      simpa [Std.HashMap.get?_eq_getElem?] using clipperKickLocalsId_get_active evm I
    simp [resolveStorageRef?, evalStorageRef, activeRef, hactiveElem, config,
      storageTypeAt?, contract, storageDecls, EvalResult.bind, bind, pure]
    rfl
  have hlenLoc :
      (config v).storage.layout
        ({ base := "active", steps := [.length] } : EvaledStorageRef) evmId =
      some (wordLoc ⟨11⟩) := by
    rfl
  have hlenLoad : storageLocLoad evmId (wordLoc ⟨11⟩) =
      .int (Int.ofNat len.toNat) := by
    simpa [len, evmId, clipperKickSourceIdState, storageStore_executionEnv] using
      clipperStorageLocLoad_uint256 evmId ⟨11⟩
  have hinc : (len + ⟨1⟩).toNat = len.toNat + 1 := by
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by native_decide,
      Nat.mod_eq_of_lt hlen]
  have hstoreLen :
      storageLocStore evmId (wordLoc ⟨11⟩) (.int (Int.ofNat len.toNat + 1)) =
      some evmLen := by
    rw [show Int.ofNat len.toNat + 1 = Int.ofNat (len.toNat + 1) by simp, ← hinc]
    dsimp [evmLen, clipperKickSourceActiveLengthState]
    simpa [evmId, len, wordLoc, uint256Loc]
      using storageLocStore_uint256 evmId ⟨11⟩ (len + ⟨1⟩)
  have hwrite :
      writeStorage? (config v) evmLen
        ({ base := "active", steps := [.aindex (.int (Int.ofNat len.toNat))] } :
          EvaledStorageRef)
        uint256St (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) =
      .ok (clipperKickSourceActiveState evm) := by
    have hstore :
        storageLocStore evmLen
          (wordLoc (activeSlot (.int (Int.ofNat len.toNat))))
          (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) =
        some (clipperKickSourceActiveState evm) := by
      unfold activeSlot
      rw [keyValueToWord_uint256]
      dsimp [clipperKickSourceActiveState]
      simpa [evmLen,
        clipperKickSourceActiveLengthState, clipperKickSourceActiveElemSlot,
        len, wordLoc, uint256Loc]
        using storageLocStore_uint256 evmLen
          (activeDataSlot + len) (clipperKickSourceIdWord evm)
    unfold writeStorage?
    change (match some (wordLoc (activeSlot (.int (Int.ofNat len.toNat)))) with
      | some loc => EvalResult.ofOption .storageError (storageLocStore evmLen loc
          (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)))
      | none => .error .storageError) = _
    simp only [hstore, EvalResult.ofOption]
  unfold pushArray?
  rw [hresolve]
  simp only [EvalResult.bind, bind]
  simp only [List.nil_append]
  rw [hlenLoc]
  simp only [EvalResult.ofOption]
  rw [hlenLoad]
  simp only
  rw [hstoreLen]
  exact hwrite

theorem clipperEvalKickActiveLengthAfterPush (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsId evm I }
      (clipperKickSourceActiveState evm) (.arrayLength .storage activeRef) =
      .ok (.int (Int.ofNat (clipperKickSourcePostPushLengthWord evm).toNat)) := by
  simpa [clipperKickSourcePostPushLengthWord, clipperKickSourceActiveState,
    storageStore_executionEnv] using
    clipperEvalActiveLength v (clipperKickSourceActiveState evm)
      (clipperKickLocalsId evm I) (clipperKickLocalsId_get_active evm I)

theorem clipperEvalKickActivePosExpr (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsId evm I }
      (clipperKickSourceActiveState evm)
      (wrap256 (.binary .sub (.arrayLength .storage activeRef) (.intLit 1))) =
      .ok (.int (Int.ofNat (clipperKickSourceActivePosWord evm).toNat)) := by
  let n := clipperKickSourcePostPushLengthWord evm
  have hlen := clipperEvalKickActiveLengthAfterPush v evm I
  rw [wrap256]
  simp only [evalExpr?, hlen, EvalResult.bind, bind, pure]
  change (if wordModulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat n.toNat - 1) % wordModulus))) =
    .ok (Value.int (Int.ofNat (UInt256.sub n ⟨1⟩).toNat))
  rw [if_neg (by norm_num [wordModulus])]
  simpa using clipperIntModWord_sub_toNat n ⟨1⟩

abbrev clipperKickSourceSalesRef (evm : EVM.State) (field : Ident) :
    EvaledStorageRef :=
  { base := "sales", steps := [.mindex (clipperKickSourceIdKey evm), .field field] }

theorem clipperEvalKickVarId (v : ClipperImmutables) (evm evmRead : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      evmRead (.var "id") =
      .ok (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) := by
  simp only [evalExpr?, clipperKickLocalsActivePos]
  rw [store_get_ne _ _ (by decide), clipperKickLocalsId, store_get_self]
  rfl

theorem clipperEvalKickVarActivePos (v : ClipperImmutables)
    (evm evmRead : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      evmRead (.var "activePos") =
      .ok (.int (Int.ofNat (clipperKickSourceActivePosWord evm).toNat)) := by
  simp only [evalExpr?, clipperKickLocalsActivePos, store_get_self, EvalResult.ofOption]

theorem clipperEvalKickVarTab (v : ClipperImmutables) (evm evmRead : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      evmRead (.var "tab") = .ok (clipperKickTabValue I) := by
  simp only [evalExpr?, clipperKickLocalsActivePos]
  rw [store_get_ne _ _ (by decide), clipperKickLocalsId,
    store_get_ne _ _ (by decide), clipperKickStore,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalKickVarLot (v : ClipperImmutables) (evm evmRead : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      evmRead (.var "lot") = .ok (clipperKickLotValue I) := by
  simp only [evalExpr?, clipperKickLocalsActivePos]
  rw [store_get_ne _ _ (by decide), clipperKickLocalsId,
    store_get_ne _ _ (by decide), clipperKickStore,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalKickVarUsr (v : ClipperImmutables) (evm evmRead : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      evmRead (.var "usr") = .ok (clipperKickUsrValue I) := by
  simp only [evalExpr?, clipperKickLocalsActivePos]
  rw [store_get_ne _ _ (by decide), clipperKickLocalsId,
    store_get_ne _ _ (by decide), clipperKickStore,
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperKickAssignSalesPos (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      (clipperKickSourceActiveState evm)
      (.assign .storage (salesF (.var "id") "pos") (.var "activePos"))
      (.ok { contract := contract v, locals := clipperKickLocalsActivePos evm I }
        (clipperKickSourceSalesPosState evm)) := by
  apply ExecStmt.assign
    (clipperEvalKickVarActivePos v evm (clipperKickSourceActiveState evm) I)
  apply assignStorageRef_storage_scalar
    (er := clipperKickSourceSalesRef evm "pos") (ty := uint256St)
    (loc := wordLoc (clipperKickSourceSalesBaseSlot evm))
  · exact clipperKickLocalsActivePos_get_sales evm I
  · simp [salesF, clipperKickSourceSalesRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep,
      clipperEvalKickVarId v evm (clipperKickSourceActiveState evm) I,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, SaleStructTy,
      uint256St]
  · rfl
  · simpa [clipperKickSourceSalesPosState, wordLoc, uint256Loc] using
      storageLocStore_uint256 (clipperKickSourceActiveState evm)
        (clipperKickSourceSalesBaseSlot evm) (clipperKickSourceActivePosWord evm)

theorem clipperKickAssignSalesTab (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      (clipperKickSourceSalesPosState evm)
      (.assign .storage (salesF (.var "id") "tab") (.var "tab"))
      (.ok { contract := contract v, locals := clipperKickLocalsActivePos evm I }
        (clipperKickSourceSalesTabState evm I)) := by
  apply ExecStmt.assign (by
    simpa [clipperKickTabValue] using
      clipperEvalKickVarTab v evm (clipperKickSourceSalesPosState evm) I)
  apply assignStorageRef_storage_scalar
    (er := clipperKickSourceSalesRef evm "tab") (ty := uint256St)
    (loc := wordLoc (clipperKickSourceSalesBaseSlot evm + ⟨1⟩))
  · exact clipperKickLocalsActivePos_get_sales evm I
  · simp [salesF, clipperKickSourceSalesRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep,
      clipperEvalKickVarId v evm (clipperKickSourceSalesPosState evm) I,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [clipperKickSourceSalesRef, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperKickSourceSalesTabState, wordLoc, uint256Loc] using
      storageLocStore_uint256 (clipperKickSourceSalesPosState evm)
        (clipperKickSourceSalesBaseSlot evm + ⟨1⟩) (clipperKickTabWord I)

theorem clipperKickAssignSalesLot (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      (clipperKickSourceSalesTabState evm I)
      (.assign .storage (salesF (.var "id") "lot") (.var "lot"))
      (.ok { contract := contract v, locals := clipperKickLocalsActivePos evm I }
        (clipperKickSourceSalesLotState evm I)) := by
  apply ExecStmt.assign (by
    simpa [clipperKickLotValue] using
      clipperEvalKickVarLot v evm (clipperKickSourceSalesTabState evm I) I)
  apply assignStorageRef_storage_scalar
    (er := clipperKickSourceSalesRef evm "lot") (ty := uint256St)
    (loc := wordLoc (clipperKickSourceSalesBaseSlot evm + ⟨2⟩))
  · exact clipperKickLocalsActivePos_get_sales evm I
  · simp [salesF, clipperKickSourceSalesRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep,
      clipperEvalKickVarId v evm (clipperKickSourceSalesTabState evm I) I,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [clipperKickSourceSalesRef, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperKickSourceSalesLotState, wordLoc, uint256Loc] using
      storageLocStore_uint256 (clipperKickSourceSalesTabState evm I)
        (clipperKickSourceSalesBaseSlot evm + ⟨2⟩) (clipperKickLotWord I)

theorem clipperKickUsrMaskedWord_canonical (I : ExecutionEnv) :
    (clipperKickUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold clipperKickUsrMaskedWord
  rw [u256_land_comm]
  exact solcAddrMask_result_canonical (clipperKickUsrWord I)

theorem clipperKickUsrValue_masked (I : ExecutionEnv) :
    clipperKickUsrValue I =
      .address (AccountAddress.ofNat (clipperKickUsrMaskedWord I).toNat) := by
  simpa [clipperKickUsrValue, clipperKickUsrMaskedWord] using
    (solcAddressValue_masked (clipperKickUsrWord I))

theorem clipperKickAssignSalesUsr (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      (clipperKickSourceSalesLotState evm I)
      (.assign .storage (salesF (.var "id") "usr") (.var "usr"))
      (.ok { contract := contract v, locals := clipperKickLocalsActivePos evm I }
        (clipperKickSourceSalesUsrState evm I)) := by
  have husr := clipperEvalKickVarUsr v evm (clipperKickSourceSalesLotState evm I) I
  rw [clipperKickUsrValue_masked I] at husr
  apply ExecStmt.assign husr
  apply assignStorageRef_storage_scalar_value
    (er := clipperKickSourceSalesRef evm "usr") (ty := addrSt)
    (loc := addrLoc (clipperKickSourceSalesBaseSlot evm + ⟨3⟩))
  · exact clipperKickLocalsActivePos_get_sales evm I
  · simp [salesF, clipperKickSourceSalesRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep,
      clipperEvalKickVarId v evm (clipperKickSourceSalesLotState evm I) I,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [clipperKickSourceSalesRef, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, addrSt]
  · rfl
  · trivial
  · simpa [clipperKickSourceSalesUsrState, addrLoc] using
      storageLocStore_address_offset0 (clipperKickSourceSalesLotState evm I)
        (clipperKickSourceSalesBaseSlot evm + ⟨3⟩) (clipperKickUsrMaskedWord I)
        (clipperKickUsrMaskedWord_canonical I)

abbrev clipperKickSourceTicWord (evm : EVM.State) : UInt256 :=
  UInt256.land (UInt256.ofNat evm.executionEnv.header.timestamp)
    clipperSalesUint96Mask

theorem clipperKickSourceTicWord_toNat (evm : EVM.State) :
    (clipperKickSourceTicWord evm).toNat =
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat % 2 ^ 96 := by
  unfold clipperKickSourceTicWord
  rw [u256_land_toNat]
  have hmask : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by native_decide
  rw [hmask, nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size]))

theorem clipperKickAssignSalesTic (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evm I }
      (clipperKickSourceSalesUsrState evm I)
      (.assign .storage (salesF (.var "id") "tic") (wrap96 (.env .timestamp)))
      (.ok { contract := contract v, locals := clipperKickLocalsActivePos evm I }
        (clipperKickSourceInitializedState evm I)) := by
  let evmUsr := clipperKickSourceSalesUsrState evm I
  let ticWord := clipperKickSourceTicWord evmUsr
  have hrhs :
      evalExpr? (config v)
        { contract := contract v, locals := clipperKickLocalsActivePos evm I }
        evmUsr (wrap96 (.env .timestamp)) =
      .ok (.int (Int.ofNat ticWord.toNat)) := by
    rw [clipperKickSourceTicWord_toNat]
    simpa [evmUsr] using
      clipperEvalRedoTimestamp96 v evmUsr (clipperKickLocalsActivePos evm I)
  apply ExecStmt.assign hrhs
  apply assignStorageRef_storage_scalar
    (er := clipperKickSourceSalesRef evm "tic") (ty := uint96St)
    (loc := uint96Loc (clipperKickSourceSalesBaseSlot evm + ⟨3⟩)
      ⟨20, by decide⟩ (by decide))
  · exact clipperKickLocalsActivePos_get_sales evm I
  · simp [salesF, clipperKickSourceSalesRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, clipperEvalKickVarId v evm evmUsr I, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, SaleStructTy,
      uint96St]
  · rfl
  · have hstore := clipperStorageLocStore_uint96_offset20 evmUsr
        (clipperKickSourceSalesBaseSlot evm + ⟨3⟩) ticWord
    simpa only [clipperKickSourceInitializedState, clipperKickSourceTicWord]
      using hstore

end Benchmarks.Dss.Clipper
