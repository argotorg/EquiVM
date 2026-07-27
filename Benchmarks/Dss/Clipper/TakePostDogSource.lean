import Benchmarks.Dss.Clipper.TakeDogDigs
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeLocalsDigsRet_locked
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew).get? "locked" = none := by
  simp [clipperTakeLocalsDigsRet, clipperTakeLocalsMoveRet,
    clipperTakeLocalsDogLoaded, clipperTakeLocalsFluxBuyerRet,
    clipperTakeLocalsLotAssigned, clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
    clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab,
    clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
    clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
    clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
    clipperTakeLocalsUsr, clipperTakeStore]

theorem clipperEvalTakeVarIdAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
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

theorem clipperEvalTakeVarTabAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.var "tab") = .ok (.int (Int.ofNat tabNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_self]
  rfl

theorem clipperEvalTakeVarLotAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.var "lot") = .ok (.int (Int.ofNat lotNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  rfl

theorem clipperTakeAssignSalesTabAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evm : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    assignStorageRef? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evm .storage (salesF (.var "id") "tab") (.int (Int.ofNat tabNew.toNat)) =
      .ok
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperTakeSalesTabSlot I)
            tabNew) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesTabRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesTabSlot I))
  · simp [salesF, clipperTakeLocalsDigsRet, clipperTakeLocalsMoveRet,
      clipperTakeLocalsDogLoaded, clipperTakeLocalsFluxBuyerRet,
      clipperTakeLocalsLotAssigned, clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
      clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore]
  · simp [clipperTakeSalesTabRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeVarIdAtDigsRet v evmLoc evmRead evmVat evm I price slice owe0 owe
        slice' tabNew lotNew,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesTabSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesTabSlot I) tabNew

theorem clipperTakeAssignSalesLotAtDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evm : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    assignStorageRef? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evm .storage (salesF (.var "id") "lot") (.int (Int.ofNat lotNew.toNat)) =
      .ok
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperTakeSalesLotSlot I)
            lotNew) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesLotRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesLotSlot I))
  · simp [salesF, clipperTakeLocalsDigsRet, clipperTakeLocalsMoveRet,
      clipperTakeLocalsDogLoaded, clipperTakeLocalsFluxBuyerRet,
      clipperTakeLocalsLotAssigned, clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
      clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab,
      clipperTakeLocalsOwe, clipperTakeLocalsOwe0, clipperTakeLocalsSlice,
      clipperTakeLocalsTab, clipperTakeLocalsLot, clipperTakeLocalsPrice,
      clipperTakeLocalsDone, clipperTakeLocalsSt, clipperTakeLocalsTic,
      clipperTakeLocalsUsr, clipperTakeStore]
  · simp [clipperTakeSalesLotRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeVarIdAtDigsRet v evmLoc evmRead evmVat evm I price slice owe0 owe
        slice' tabNew lotNew,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesLotSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesLotSlot I) lotNew

theorem clipperTakeDogDigsOweNonzeroStoreSourceOk (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
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
        "digs" 0
        [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (true, evmDog, outDog) true) :
    let evmTab :=
      Solm.EVM.storageStore evmDog evmDog.executionEnv.codeOwner
        (clipperTakeSalesTabSlot I) tabNew
    let evmLot :=
      Solm.EVM.storageStore evmTab evmTab.executionEnv.codeOwner
        (clipperTakeSalesLotSlot I) lotNew
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
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
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro evmTab evmLot
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe slice'
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
      clipperTakeDogDigsOweCallSuccessBlock v evmLoc evmRead evmVat evmMove evmDog I
        price slice owe0 owe slice' tabNew lotNew hlotNew hdogCode hcallDog
  have hlotCond :
      evalExpr? (config v) digsRetFrame evmDog
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
    simpa [digsRetFrame] using
      clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat evmDog I
        price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond :
      evalExpr? (config v) digsRetFrame evmDog
        (.binary .eq (.var "tab") (.intLit 0)) = .ok (.bool false) := by
    simpa [digsRetFrame] using
      clipperEvalTakeTabEqZeroAtDigsRet_false v evmLoc evmRead evmVat evmDog I
        price slice owe0 owe slice' tabNew lotNew htabNew
  have htabEval :
      evalExpr? (config v) digsRetFrame evmDog (.var "tab") =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [digsRetFrame] using
      clipperEvalTakeVarTabAtDigsRet v evmLoc evmRead evmVat evmDog I price slice
        owe0 owe slice' tabNew lotNew
  have htabAssign :
      assignStorageRef? (config v) digsRetFrame evmDog
        .storage (salesF (.var "id") "tab") (.int (Int.ofNat tabNew.toNat)) =
        .ok (digsRetFrame, evmTab) := by
    simpa [digsRetFrame, evmTab] using
      clipperTakeAssignSalesTabAtDigsRet v evmLoc evmRead evmVat evmDog I price
        slice owe0 owe slice' tabNew lotNew
  have htabStmt :
      ExecStmt (config v) digsRetFrame evmDog
        (.assign .storage (salesF (.var "id") "tab") (.var "tab"))
        (.ok digsRetFrame evmTab) := by
    exact ExecStmt.assign htabEval htabAssign
  have hlotEval :
      evalExpr? (config v) digsRetFrame evmTab (.var "lot") =
        .ok (.int (Int.ofNat lotNew.toNat)) := by
    simpa [digsRetFrame] using
      clipperEvalTakeVarLotAtDigsRet v evmLoc evmRead evmVat evmTab I price slice
        owe0 owe slice' tabNew lotNew
  have hlotAssign :
      assignStorageRef? (config v) digsRetFrame evmTab
        .storage (salesF (.var "id") "lot") (.int (Int.ofNat lotNew.toNat)) =
        .ok (digsRetFrame, evmLot) := by
    simpa [digsRetFrame, evmLot] using
      clipperTakeAssignSalesLotAtDigsRet v evmLoc evmRead evmVat evmTab I price
        slice owe0 owe slice' tabNew lotNew
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
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew)
        (clipperTakeLocalsDigsRet_locked evmLoc evmRead evmVat I price slice owe0
          owe slice' tabNew lotNew)
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
