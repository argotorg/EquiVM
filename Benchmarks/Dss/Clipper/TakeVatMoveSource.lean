import Benchmarks.Dss.Clipper.Dog
import Benchmarks.Dss.Clipper.TakeVatFluxSource
import Benchmarks.Dss.Clipper.TakeVatMove
import Benchmarks.Dss.Clipper.Vow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeDogEVMWord (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) solcAddrMask

abbrev clipperTakeVowEVMWord (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) solcAddrMask

abbrev clipperTakeLocalsDogLoaded (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice' tabNew
    lotNew).insert "dog_"
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))

abbrev clipperTakeLocalsMoveRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "_moveRet" .unit

abbrev clipperTakeLocalsDigsRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "_digsRet" .unit

theorem clipperTakeDecodeMoveVoid (v : ClipperImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "move" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem clipperTakeDecodeDigsVoid (v : ClipperImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "digs" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem clipperTakeDecodeClipperCallVoid (v : ClipperImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "clipperCall" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem clipperEvalTakeDataLengthZero (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat (bytesLength "data") = .ok (.int 0) := by
  simp only [bytesLength, localRef, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
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
    clipperTakeStore, store_get_self]
  simp [clipperTakeDataBytes, hdataLen]

theorem clipperEvalTakeCallbackGuardDataEmpty (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) =
        .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperEvalTakeDataLengthZero v evmLoc evmRead evmVat I price slice owe0 owe
    slice' tabNew lotNew hdataLen]
  simp [evalBinaryOp?]

theorem clipperEvalTakeVatMoveArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmVat.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
  have hsender :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat sender = .ok (.address evmVat.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  have hvow :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat (.storage vowRef) =
          .ok (.address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat)) := by
    simpa [clipperTakeVowEVMWord] using
      clipperEvalVow v evmVat
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)
        (by
          simp [clipperTakeLocalsDogLoaded, clipperTakeLocalsFluxBuyerRet,
            clipperTakeLocalsLotAssigned, clipperTakeLocalsTabAssigned,
            clipperTakeLocalsLotNew, clipperTakeLocalsTabNew,
            clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab, clipperTakeLocalsOwe,
            clipperTakeLocalsOwe0, clipperTakeLocalsSlice, clipperTakeLocalsTab,
            clipperTakeLocalsLot, clipperTakeLocalsPrice, clipperTakeLocalsDone,
            clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
            clipperTakeStore])
  have howe :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat (.var "owe") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_self]
    rfl
  simp only [evalExprs?, hsender, hvow, howe, EvalResult.bind, bind, pure]

theorem clipperEvalTakeCallbackArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat [sender, .var "owe", .var "slice", .var "data"] =
        .ok
          [.address evmVat.executionEnv.source,
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat),
            .int (Int.ofNat slice'.toNat), clipperTakeDataValue I] := by
  have hsender :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat sender = .ok (.address evmVat.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  have howe :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat (.var "owe") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_self]
    rfl
  have hslice :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat (.var "slice") = .ok (.int (Int.ofNat slice'.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_self]
    rfl
  have hdata :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat (.var "data") = .ok (clipperTakeDataValue I) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
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
      clipperTakeStore, store_get_self]
    rfl
  simp only [evalExprs?, hsender, howe, hslice, hdata, EvalResult.bind, bind, pure]

theorem clipperEvalTakeDogDigsTarget (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove (.var "dog_") =
        .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_self]
  rfl

theorem clipperEvalTakeDogDigsOweArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove [ilkExpr v, .var "owe"] =
        .ok
          [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
  have hilk :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmMove (ilkExpr v) = .ok v.ilk := by
    rcases v.ilk_wf with ⟨bs, hbs, _hlen⟩
    simp [ilkExpr, hbs, evalExpr?, pure]
  have howe :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmMove (.var "owe") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_self]
    rfl
  simp only [evalExprs?, hilk, howe, EvalResult.bind, bind, pure]

theorem clipperEvalTakeDogCodeGuard_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalTakeDogDigsTarget, evalBinaryOp?,
    EVM.Word.ofNat, hnoCode]

theorem clipperEvalTakeDogCodeGuard_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalTakeDogDigsTarget, evalBinaryOp?,
    EVM.Word.ofNat, hcode]

theorem clipperEvalTakeLotEqZero_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool true) := by
  subst lotNew
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int 0) (.int 0) = .ok (.bool true)
  unfold evalBinaryOp?
  rfl

theorem clipperEvalTakeLotEqZero_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmMove
      (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool false) := by
  have htoNat : lotNew.toNat ≠ 0 := by
    intro hzero
    apply hlot
    cases lotNew with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hzero
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int (Int.ofNat lotNew.toNat)) (.int 0) =
    .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat lotNew.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat lotNew.toNat) == Value.int 0) = false by
    simp [htoNat]]

theorem clipperTakeDogDigsOweNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩)
    (hnoDogCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
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
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
    simpa [moveFrame] using
      clipperEvalTakeLotEqZero_false v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew hlot
  have hdogRevert :
      ExecBlock (config v) moveFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "owe"] "_digsRet")
        .reverted := by
    have hguard :
        evalExpr? (config v) moveFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool false) := by
      simpa [moveFrame] using
        clipperEvalTakeDogCodeGuard_false v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew hnoDogCode
    simpa [checkedExternalCallStmts, moveFrame] using
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
  simpa [moveFrame] using
    ExecBlock.consRevert (ExecStmt.iteFalse hlotCond hdogRevert)

theorem clipperTakeDogDigsOweCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlot : lotNew ≠ ⟨0⟩)
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
        (false, evmDog, outDog) true) :
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
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
    simpa [moveFrame] using
      clipperEvalTakeLotEqZero_false v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew hlot
  have hdogRevert :
      ExecBlock (config v) moveFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "owe"] "_digsRet")
        .reverted := by
    have htarget :
        evalExpr? (config v) moveFrame evmMove (.var "dog_") =
          .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simpa [moveFrame] using
        clipperEvalTakeDogDigsTarget v evmLoc evmRead evmVat evmMove I price slice
          owe0 owe slice' tabNew lotNew
    have hguard :
        evalExpr? (config v) moveFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [moveFrame] using
        clipperEvalTakeDogCodeGuard_true v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew hdogCode
    have hargs :
        evalExprs? (config v) moveFrame evmMove [ilkExpr v, .var "owe"] =
          .ok
            [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
      simpa [moveFrame] using
        clipperEvalTakeDogDigsOweArgs v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew
    simpa [checkedExternalCallStmts, moveFrame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure htarget (by simp [evalExpr?, pure]) hargs hcallDog)))
  simpa [moveFrame] using
    ExecBlock.consRevert (ExecStmt.iteFalse hlotCond hdogRevert)

theorem clipperTakeDogDigsOweCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlot : lotNew ≠ ⟨0⟩)
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
            [ilkExpr v, .var "owe"] "_digsRet") ]
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmDog) := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let digsFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
    simpa [moveFrame] using
      clipperEvalTakeLotEqZero_false v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe slice' tabNew lotNew hlot
  have hdogOk :
      ExecBlock (config v) moveFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "owe"] "_digsRet")
        (.ok digsFrame evmDog) := by
    have htarget :
        evalExpr? (config v) moveFrame evmMove (.var "dog_") =
          .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simpa [moveFrame] using
        clipperEvalTakeDogDigsTarget v evmLoc evmRead evmVat evmMove I price slice
          owe0 owe slice' tabNew lotNew
    have hguard :
        evalExpr? (config v) moveFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [moveFrame] using
        clipperEvalTakeDogCodeGuard_true v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew hdogCode
    have hargs :
        evalExprs? (config v) moveFrame evmMove [ilkExpr v, .var "owe"] =
          .ok
            [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
      simpa [moveFrame] using
        clipperEvalTakeDogDigsOweArgs v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe slice' tabNew lotNew
    simpa [checkedExternalCallStmts, moveFrame, digsFrame, clipperTakeLocalsDigsRet,
      collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consNormal
          (ExecStmt.externalCallSuccess htarget (by simp [evalExpr?, pure]) hargs hcallDog
            (clipperTakeDecodeDigsVoid v outDog))
          ExecBlock.nil))
  simpa [moveFrame, digsFrame] using
    ExecBlock.consNormal (ExecStmt.iteFalse hlotCond hdogOk) ExecBlock.nil

theorem clipperEvalTakeLotEqZeroAtDigsRet_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool false) := by
  have htoNat : lotNew.toNat ≠ 0 := by
    intro hzero
    apply hlot
    cases lotNew with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hzero
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int (Int.ofNat lotNew.toNat)) (.int 0) =
    .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat lotNew.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat lotNew.toNat) == Value.int 0) = false by
    simp [htoNat]]

theorem clipperEvalTakeTabEqZeroAtDigsRet_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (htab : tabNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "tab") (.intLit 0)) =
        .ok (.bool true) := by
  subst tabNew
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_self]
  change evalBinaryOp? .eq (.int 0) (.int 0) = .ok (.bool true)
  unfold evalBinaryOp?
  rfl

theorem clipperEvalTakeTabEqZeroAtDigsRet_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (htab : tabNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "tab") (.intLit 0)) =
        .ok (.bool false) := by
  have htoNat : tabNew.toNat ≠ 0 := by
    intro hzero
    apply htab
    cases tabNew with
    | mk val =>
        cases val using Fin.cases
        · rfl
        · simp [UInt256.toNat] at hzero
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_self]
  change evalBinaryOp? .eq (.int (Int.ofNat tabNew.toNat)) (.int 0) =
    .ok (.bool false)
  unfold evalBinaryOp?
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat tabNew.toNat) == Value.int 0)) =
    EvalResult.ok (Value.bool false)
  rw [show (Value.int (Int.ofNat tabNew.toNat) == Value.int 0) = false by
    simp [htoNat]]

theorem clipperTakeVatMoveNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hnoVatCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      ([ .letDecl "dog_" (some addr) (.storage dogRef),
        .ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [] ] ++
        checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  let startFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice' tabNew
        lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                slice' tabNew lotNew)
              (by
                simp [clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
                  clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
                  clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
                  clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
                  clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
                  clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
                  clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])))
  have hcallback :
      ExecStmt (config v) dogFrame evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        (.ok dogFrame evmVat) := by
    simpa [dogFrame] using
      ExecStmt.iteFalse
        (clipperEvalTakeCallbackGuardDataEmpty v evmLoc evmRead evmVat I price slice
          owe0 owe slice' tabNew lotNew hdataLen)
        ExecBlock.nil
  have hmoveRevert :
      ExecBlock (config v) dogFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    have hguard :
        evalExpr? (config v) dogFrame evmVat
          (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
            .ok (.bool false) := by
      exact clipperEvalTakeVatCodeGuard_false v evmVat
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew) hnoVatCode
    simpa [checkedExternalCallStmts, dogFrame] using
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
  simpa [startFrame, dogFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal hcallback hmoveRevert))

theorem clipperTakeVatMoveCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (false, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      ([ .letDecl "dog_" (some addr) (.storage dogRef),
        .ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [] ] ++
        checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  let startFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice' tabNew
        lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                slice' tabNew lotNew)
              (by
                simp [clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
                  clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
                  clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
                  clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
                  clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
                  clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
                  clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])))
  have hcallback :
      ExecStmt (config v) dogFrame evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        (.ok dogFrame evmVat) := by
    simpa [dogFrame] using
      ExecStmt.iteFalse
        (clipperEvalTakeCallbackGuardDataEmpty v evmLoc evmRead evmVat I price slice
          owe0 owe slice' tabNew lotNew hdataLen)
        ExecBlock.nil
  have hargs :
      evalExprs? (config v) dogFrame evmVat [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmVat.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
    simpa [dogFrame] using
      clipperEvalTakeVatMoveArgs v evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew
  have hmoveRevert :
      ExecBlock (config v) dogFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    have hguard :
        evalExpr? (config v) dogFrame evmVat
          (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
            .ok (.bool true) := by
      exact clipperEvalTakeVatCodeGuard_true v evmVat
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew) hvatCode
    simpa [checkedExternalCallStmts, dogFrame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalVat v evmVat
              (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
                slice' tabNew lotNew))
            (by simp [evalExpr?, pure]) hargs hcallMove)))
  simpa [startFrame, dogFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal hcallback hmoveRevert))

theorem clipperTakeVatMoveNoCodeBlockOfCallbackFalse (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hcallback :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
              slice' tabNew lotNew))
          evmVat))
    (hnoVatCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      ([ .letDecl "dog_" (some addr) (.storage dogRef),
        .ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [] ] ++
        checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  let startFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice' tabNew
        lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                slice' tabNew lotNew)
              (by
                simp [clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
                  clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
                  clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
                  clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
                  clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
                  clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
                  clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])))
  have hmoveRevert :
      ExecBlock (config v) dogFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    have hguard :
        evalExpr? (config v) dogFrame evmVat
          (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
            .ok (.bool false) := by
      exact clipperEvalTakeVatCodeGuard_false v evmVat
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew) hnoVatCode
    simpa [checkedExternalCallStmts, dogFrame] using
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
  simpa [startFrame, dogFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal (by simpa [dogFrame] using hcallback) hmoveRevert))

theorem clipperTakeVatMoveCallFailureBlockOfCallbackFalse (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hcallback :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
              slice' tabNew lotNew))
          evmVat))
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (false, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      ([ .letDecl "dog_" (some addr) (.storage dogRef),
        .ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [] ] ++
        checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  let startFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice' tabNew
        lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                slice' tabNew lotNew)
              (by
                simp [clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
                  clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
                  clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
                  clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
                  clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
                  clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
                  clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])))
  have hargs :
      evalExprs? (config v) dogFrame evmVat [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmVat.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
    simpa [dogFrame] using
      clipperEvalTakeVatMoveArgs v evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew
  have hmoveRevert :
      ExecBlock (config v) dogFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
        .reverted := by
    have hguard :
        evalExpr? (config v) dogFrame evmVat
          (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
            .ok (.bool true) := by
      exact clipperEvalTakeVatCodeGuard_true v evmVat
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew) hvatCode
    simpa [checkedExternalCallStmts, dogFrame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalVat v evmVat
              (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
                slice' tabNew lotNew))
            (by simp [evalExpr?, pure]) hargs hcallMove)))
  simpa [startFrame, dogFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal (by simpa [dogFrame] using hcallback) hmoveRevert))

theorem clipperTakeVatMoveCallSuccessBlockOfCallbackFalse (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hcallback :
      ExecStmt (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        (.ok
          (Frame.mk (contract v)
            (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
              slice' tabNew lotNew))
          evmVat))
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (true, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      ([ .letDecl "dog_" (some addr) (.storage dogRef),
        .ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [] ] ++
        checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmMove) := by
  let startFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice' tabNew
        lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                slice' tabNew lotNew)
              (by
                simp [clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
                  clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
                  clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
                  clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
                  clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
                  clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
                  clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])))
  have hargs :
      evalExprs? (config v) dogFrame evmVat [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmVat.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
    simpa [dogFrame] using
      clipperEvalTakeVatMoveArgs v evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew
  have hmove :
      ExecBlock (config v) dogFrame evmVat
        (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
        (.ok moveFrame evmMove) := by
    have hguard :
        evalExpr? (config v) dogFrame evmVat
          (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
            .ok (.bool true) := by
      exact clipperEvalTakeVatCodeGuard_true v evmVat
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew) hvatCode
    simpa [checkedExternalCallStmts, dogFrame, moveFrame, clipperTakeLocalsMoveRet,
      collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consNormal
          (ExecStmt.externalCallSuccess
            (clipperEvalVat v evmVat
              (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
                slice' tabNew lotNew))
            (by simp [evalExpr?, pure]) hargs hcallMove
            (clipperTakeDecodeMoveVoid v outMove))
          ExecBlock.nil))
  simpa [startFrame, dogFrame, moveFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal (by simpa [dogFrame] using hcallback) hmove))

theorem clipperTakeVatMoveCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
        (true, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      ([ .letDecl "dog_" (some addr) (.storage dogRef),
        .ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [] ] ++
        checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
          [sender, .storage vowRef, .var "owe"] "_moveRet")
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmMove) := by
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
        tabNew lotNew)
  have hcallback :
      ExecStmt (config v) dogFrame evmVat
        (.ite
          (.binary .and
            (.binary .gt (bytesLength "data") (.intLit 0))
            (.binary .and
              (.binary .ne (.var "who") (vatExpr v))
              (.binary .ne (.var "who") (.var "dog_"))))
          (checkedExternalCallStmts (.var "who") "clipperCall" (.intLit 0)
            [sender, .var "owe", .var "slice", .var "data"] "_clipperCallRet")
          [])
        (.ok dogFrame evmVat) := by
    simpa [dogFrame] using
      ExecStmt.iteFalse
        (clipperEvalTakeCallbackGuardDataEmpty v evmLoc evmRead evmVat I price slice
          owe0 owe slice' tabNew lotNew hdataLen)
        ExecBlock.nil
  simpa [dogFrame] using
    clipperTakeVatMoveCallSuccessBlockOfCallbackFalse v evmLoc evmRead evmVat evmMove I
      price slice owe0 owe slice' tabNew lotNew hcallback hvatCode hcallMove

end Benchmarks.Dss.Clipper
