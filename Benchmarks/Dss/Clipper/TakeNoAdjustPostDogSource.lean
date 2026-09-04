import Benchmarks.Dss.Clipper.TakeNoAdjustVatMoveSource
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperEvalTakeNoAdjustDogDigsTargetAtMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.var "dog_") =
        .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_self]
  rfl

theorem clipperEvalTakeNoAdjustLotEqZero_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
  have htoNat : lotNew.toNat ≠ 0 := by
    intro hzero
    apply hlot
    cases lotNew with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hzero
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int (Int.ofNat lotNew.toNat)) (.int 0) =
    .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat lotNew.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat lotNew.toNat) == Value.int 0) = false by
    simp [htoNat]]

theorem clipperEvalTakeNoAdjustDogCodeGuard_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalTakeNoAdjustDogDigsTargetAtMoveRet,
    evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem clipperEvalTakeNoAdjustDogDigsOweArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove [ilkExpr v, .var "owe"] =
        .ok [v.ilk, .int (Int.ofNat owe.toNat)] := by
  have hilk :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmMove (ilkExpr v) = .ok v.ilk := by
    rcases v.ilk_wf with ⟨_bs, hbs, _hlen⟩
    simp [ilkExpr, hbs, evalExpr?, pure]
  have howe :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmMove (.var "owe") = .ok (.int (Int.ofNat owe.toNat)) := by
    simpa using
      clipperEvalTakeOweAtNoAdjustMoveRet v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe tabNew lotNew
  simp only [evalExprs?, hilk, howe, EvalResult.bind, bind, pure]

theorem clipperTakeNoAdjustDogDigsOweCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlotNew : lotNew ≠ ⟨0⟩)
    (hdogCode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0 [v.ilk, .int (Int.ofNat owe.toNat)]
        (true, evmDog, outDog) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmDog) := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let digsFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
    simpa [moveFrame] using
      clipperEvalTakeNoAdjustLotEqZero_false v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe tabNew lotNew hlotNew
  have hdogOk :
      ExecBlock (config v) moveFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "owe"] "_digsRet")
        (.ok digsFrame evmDog) := by
    have htarget :
        evalExpr? (config v) moveFrame evmMove (.var "dog_") =
          .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simpa [moveFrame] using
        clipperEvalTakeNoAdjustDogDigsTargetAtMoveRet v evmLoc evmRead evmVat evmMove
          I price slice owe0 owe tabNew lotNew
    have hguard :
        evalExpr? (config v) moveFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [moveFrame] using
        clipperEvalTakeNoAdjustDogCodeGuard_true v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe tabNew lotNew hdogCode
    have hargs :
        evalExprs? (config v) moveFrame evmMove [ilkExpr v, .var "owe"] =
          .ok [v.ilk, .int (Int.ofNat owe.toNat)] := by
      simpa [moveFrame] using
        clipperEvalTakeNoAdjustDogDigsOweArgs v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe tabNew lotNew
    simpa [checkedExternalCallStmts, moveFrame, digsFrame,
      clipperTakeLocalsNoAdjustDigsRet, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consNormal
          (ExecStmt.externalCallSuccess htarget (by simp [evalExpr?, pure]) hargs hcallDog
            (clipperTakeDecodeDigsVoid v outDog))
          ExecBlock.nil))
  simpa [moveFrame, digsFrame] using
    ExecBlock.consNormal (ExecStmt.iteFalse hlotCond hdogOk) ExecBlock.nil

theorem clipperTakeLocalsNoAdjustDigsRet_locked
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
      tabNew lotNew).get? "locked" = none := by
  simp [clipperTakeLocalsNoAdjustDigsRet, clipperTakeLocalsNoAdjustMoveRet,
    clipperTakeLocalsNoAdjustDogLoaded, clipperTakeLocalsNoAdjustFluxBuyerRet,
    clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
    clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
    clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
    clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
    clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
    clipperTakeLocalsUsr, clipperTakeStore]

theorem clipperEvalTakeNoAdjustVarIdAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmDog (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsNoAdjustDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_ne _ _ (by decide),
    clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeNoAdjustVarTabAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmDog (.var "tab") = .ok (.int (Int.ofNat tabNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsNoAdjustDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustTabAssigned, store_get_self]
  rfl

theorem clipperEvalTakeNoAdjustVarLotAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmDog (.var "lot") = .ok (.int (Int.ofNat lotNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsNoAdjustDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_self]
  rfl

theorem clipperEvalTakeNoAdjustLotEqZeroAtDigsRet_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmDog (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
  have htoNat : lotNew.toNat ≠ 0 := by
    intro hzero
    apply hlot
    cases lotNew with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hzero
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsNoAdjustDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int (Int.ofNat lotNew.toNat)) (.int 0) =
    .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat lotNew.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat lotNew.toNat) == Value.int 0) = false by
    simp [htoNat]]

theorem clipperEvalTakeNoAdjustTabEqZeroAtDigsRet_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (htab : tabNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmDog (.binary .eq (.var "tab") (.intLit 0)) = .ok (.bool false) := by
  have htoNat : tabNew.toNat ≠ 0 := by
    intro hzero
    apply htab
    cases tabNew with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hzero
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsNoAdjustDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustTabAssigned, store_get_self]
  change evalBinaryOp? .eq (.int (Int.ofNat tabNew.toNat)) (.int 0) =
    .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat tabNew.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat tabNew.toNat) == Value.int 0) = false by
    simp [htoNat]]

theorem clipperTakeNoAdjustAssignSalesTabAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evm : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) :
    assignStorageRef? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evm .storage (salesF (.var "id") "tab") (.int (Int.ofNat tabNew.toNat)) =
      .ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperTakeSalesTabSlot I)
            tabNew) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesTabRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesTabSlot I))
  · simp [salesF, clipperTakeLocalsNoAdjustDigsRet, clipperTakeLocalsNoAdjustMoveRet,
      clipperTakeLocalsNoAdjustDogLoaded, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore]
  · simp [clipperTakeSalesTabRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeNoAdjustVarIdAtDigsRet v evmLoc evmRead evmVat evm I price slice
        owe0 owe tabNew lotNew,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesTabSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesTabSlot I) tabNew

theorem clipperTakeNoAdjustAssignSalesLotAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evm : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) :
    assignStorageRef? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evm .storage (salesF (.var "id") "lot") (.int (Int.ofNat lotNew.toNat)) =
      .ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperTakeSalesLotSlot I)
            lotNew) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesLotRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesLotSlot I))
  · simp [salesF, clipperTakeLocalsNoAdjustDigsRet, clipperTakeLocalsNoAdjustMoveRet,
      clipperTakeLocalsNoAdjustDogLoaded, clipperTakeLocalsNoAdjustFluxBuyerRet,
      clipperTakeLocalsNoAdjustLotAssigned, clipperTakeLocalsNoAdjustTabAssigned,
      clipperTakeLocalsNoAdjustLotNew, clipperTakeLocalsNoAdjustTabNew,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore]
  · simp [clipperTakeSalesLotRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeNoAdjustVarIdAtDigsRet v evmLoc evmRead evmVat evm I price slice
        owe0 owe tabNew lotNew,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesLotSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesLotSlot I) lotNew

theorem clipperTakeNoAdjustDogDigsOweNonzeroStoreSourceOk (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew ≠ ⟨0⟩)
    (hdogCode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v) evmMove
        (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        "digs" 0 [v.ilk, .int (Int.ofNat owe.toNat)]
        (true, evmDog, outDog) true) :
    let evmTab :=
      Solm.EVM.storageStore evmDog evmDog.executionEnv.codeOwner
        (clipperTakeSalesTabSlot I) tabNew
    let evmLot :=
      Solm.EVM.storageStore evmTab evmTab.executionEnv.codeOwner
        (clipperTakeSalesLotSlot I) lotNew
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet"),
        .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ]
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro evmTab evmLot
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hdog :
      ExecBlock (config v) moveFrame evmMove
        [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
        (.ok digsRetFrame evmDog) := by
    simpa [moveFrame, digsRetFrame] using
      clipperTakeNoAdjustDogDigsOweCallSuccessBlock v evmLoc evmRead evmVat
        evmMove evmDog I price slice owe0 owe tabNew lotNew hlotNew hdogCode hcallDog
  have hlotCond :
      evalExpr? (config v) digsRetFrame evmDog
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
    simpa [digsRetFrame] using
      clipperEvalTakeNoAdjustLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat evmDog
        I price slice owe0 owe tabNew lotNew hlotNew
  have htabCond :
      evalExpr? (config v) digsRetFrame evmDog
        (.binary .eq (.var "tab") (.intLit 0)) = .ok (.bool false) := by
    simpa [digsRetFrame] using
      clipperEvalTakeNoAdjustTabEqZeroAtDigsRet_false v evmLoc evmRead evmVat evmDog
        I price slice owe0 owe tabNew lotNew htabNew
  have htabEval :
      evalExpr? (config v) digsRetFrame evmDog (.var "tab") =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [digsRetFrame] using
      clipperEvalTakeNoAdjustVarTabAtDigsRet v evmLoc evmRead evmVat evmDog I price
        slice owe0 owe tabNew lotNew
  have htabAssign :
      assignStorageRef? (config v) digsRetFrame evmDog
        .storage (salesF (.var "id") "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok (digsRetFrame, evmTab) := by
    simpa [digsRetFrame, evmTab] using
      clipperTakeNoAdjustAssignSalesTabAtDigsRet v evmLoc evmRead evmVat evmDog I
        price slice owe0 owe tabNew lotNew
  have htabStmt :
      ExecStmt (config v) digsRetFrame evmDog
        (.assign .storage (salesF (.var "id") "tab") (.var "tab"))
        (.ok digsRetFrame evmTab) := by
    exact ExecStmt.assign htabEval htabAssign
  have hlotEval :
      evalExpr? (config v) digsRetFrame evmTab (.var "lot") =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [digsRetFrame] using
      clipperEvalTakeNoAdjustVarLotAtDigsRet v evmLoc evmRead evmVat evmTab I price
        slice owe0 owe tabNew lotNew
  have hlotAssign :
      assignStorageRef? (config v) digsRetFrame evmTab
        .storage (salesF (.var "id") "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok (digsRetFrame, evmLot) := by
    simpa [digsRetFrame, evmLot] using
      clipperTakeNoAdjustAssignSalesLotAtDigsRet v evmLoc evmRead evmVat evmTab I
        price slice owe0 owe tabNew lotNew
  have hlotStmt :
      ExecStmt (config v) digsRetFrame evmTab
        (.assign .storage (salesF (.var "id") "lot") (.var "lot"))
        (.ok digsRetFrame evmLot) := by
    exact ExecStmt.assign hlotEval hlotAssign
  have hstoreBlock :
      ExecBlock (config v) digsRetFrame evmDog
        [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
          .assign .storage (salesF (.var "id") "lot") (.var "lot") ]
        (.ok digsRetFrame evmLot) := by
    exact ExecBlock.consNormal htabStmt (ExecBlock.consNormal hlotStmt ExecBlock.nil)
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite
          (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        (.ok digsRetFrame evmLot) := by
    exact ExecStmt.iteFalse htabCond hstoreBlock
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        (.ok digsRetFrame evmLot) := by
    exact ExecStmt.iteFalse hlotCond (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hzero :
      evalExpr? (config v) digsRetFrame evmLot (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, digsRetFrame]
  have hassign :
      assignStorageRef? (config v) digsRetFrame evmLot
        .storage lockedRef (.int 0) =
        .ok (digsRetFrame,
          Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [digsRetFrame] using
      assign_clipperLocked v evmLot
        (clipperTakeLocalsNoAdjustDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew)
        (clipperTakeLocalsNoAdjustDigsRet_locked evmLoc evmRead evmVat I price slice
          owe0 owe tabNew lotNew)
        ⟨0⟩
  have hunlock :
      ExecStmt (config v) digsRetFrame evmLot
        (.assign .storage lockedRef (.intLit 0))
        (.ok digsRetFrame
          (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecStmt.assign hzero hassign
  have htail :
      ExecBlock (config v) digsRetFrame evmDog
        [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
          .assign .storage lockedRef (.intLit 0) ]
        (.ok digsRetFrame
          (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)
  simpa [moveFrame, digsRetFrame, evmTab, evmLot] using execBlockAppendOk hdog htail

end Benchmarks.Dss.Clipper
