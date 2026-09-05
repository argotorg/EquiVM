import Benchmarks.Dss.Clipper.TakeCallbackSource
import Benchmarks.Dss.Clipper.TakePostDogRemoveSource
import Benchmarks.Dss.Clipper.TakePostDogSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeLocalsCallbackMoveRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "_moveRet" .unit

abbrev clipperTakeLocalsCallbackDigsRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "_digsRet" .unit

abbrev clipperTakeLocalsCallbackDigsAmt (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "digsAmt"
      (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat))

abbrev clipperTakeLocalsCallbackDigsAmtRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe slice'
    tabNew lotNew).insert "_digsRet" .unit

theorem clipperEvalTakeVatMoveArgsAtCallbackRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmCb [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmCb.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
            .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
  have hsender :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmCb sender = .ok (.address evmCb.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  have hvow :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmCb (.storage vowRef) =
          .ok (.address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat)) := by
    simpa [clipperTakeVowEVMWord] using
      clipperEvalVow v evmCb
        (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew)
        (by
          simp [clipperTakeLocalsCallbackRet, clipperTakeLocalsDogLoaded,
            clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
            clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
            clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
            clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
            clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
            clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
            clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])
  have howe :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
            tabNew lotNew))
        evmCb (.var "owe") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_self]
    rfl
  simp only [evalExprs?, hsender, hvow, howe, EvalResult.bind, bind, pure]

theorem clipperEvalTakeVatCodeGuardFalseAtCallbackRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmCb (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool false) := by
  exact clipperEvalTakeVatCodeGuard_false v evmCb _ hnoCode

theorem clipperEvalTakeVatCodeGuardTrueAtCallbackRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmCb (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool true) := by
  exact clipperEvalTakeVatCodeGuard_true v evmCb _ hcode

theorem clipperTakeVatMoveNoCodeBlockAtCallbackRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmCb
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (clipperEvalTakeVatCodeGuardFalseAtCallbackRet v evmLoc evmRead evmVat evmCb I
          price slice owe0 owe slice' tabNew lotNew hnoCode))

theorem clipperTakeVatMoveCallFailureBlockAtCallbackRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmCb (EVM.address v.vat) "move" 0
      [.address evmCb.executionEnv.source,
        .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
        .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (false, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmCb
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (clipperEvalTakeVatCodeGuardTrueAtCallbackRet v evmLoc evmRead evmVat evmCb I
          price slice owe0 owe slice' tabNew lotNew hcode))
      (ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (clipperEvalVat v evmCb
            (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe
              slice' tabNew lotNew))
          (by simp [evalExpr?, pure])
          (clipperEvalTakeVatMoveArgsAtCallbackRet v evmLoc evmRead evmVat evmCb I price
            slice owe0 owe slice' tabNew lotNew)
          hcall))

theorem clipperTakeVatMoveCallSuccessBlockAtCallbackRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmCb evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outMove : ByteArray}
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmCb.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmCb (EVM.address v.vat) "move" 0
      [.address evmCb.executionEnv.source,
        .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmCb).toNat),
        .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (true, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmCb
      (checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
        [sender, .storage vowRef, .var "owe"] "_moveRet")
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove) := by
  simpa [checkedExternalCallStmts, clipperTakeLocalsCallbackMoveRet,
    collapseReturns] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (clipperEvalTakeVatCodeGuardTrueAtCallbackRet v evmLoc evmRead evmVat evmCb I
          price slice owe0 owe slice' tabNew lotNew hcode))
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalVat v evmCb
            (clipperTakeLocalsCallbackRet evmLoc evmRead evmVat I price slice owe0 owe
              slice' tabNew lotNew))
          (by simp [evalExpr?, pure])
          (clipperEvalTakeVatMoveArgsAtCallbackRet v evmLoc evmRead evmVat evmCb I price
            slice owe0 owe slice' tabNew lotNew)
          hcall (clipperTakeDecodeMoveVoid v outMove))
        ExecBlock.nil)

theorem clipperEvalTakeDogDigsTargetAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (.var "dog_") =
        .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_self]
  rfl

theorem clipperEvalTakeDogDigsOweArgsAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove [ilkExpr v, .var "owe"] =
        .ok
          [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
  have hilk :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove (ilkExpr v) = .ok v.ilk := by
    rcases v.ilk_wf with ⟨bs, hbs, _hlen⟩
    simp [ilkExpr, hbs, evalExpr?, pure]
  have howe :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove (.var "owe") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
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

theorem clipperEvalTakeLotEqZeroTrueAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool true) := by
  subst lotNew
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  rfl

theorem clipperEvalTakeLotEqZeroFalseAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool false) := by
  have htoNat : lotNew.toNat ≠ 0 := by
    intro hzero
    apply hlot
    exact uint256_toNat_eq_zero hzero
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
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

theorem clipperEvalTakeDogCodeGuardFalseAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeDogDigsTargetAtCallbackMoveRet, evalBinaryOp?, EVM.Word.ofNat,
    hnoCode]

theorem clipperEvalTakeDogCodeGuardTrueAtCallbackMoveRet (v : ClipperImmutables)
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
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeDogDigsTargetAtCallbackMoveRet, evalBinaryOp?, EVM.Word.ofNat,
    hcode]

theorem clipperTakeDogDigsOweNoCodeBlockAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩)
    (hnoCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  apply ExecBlock.consRevert
  apply ExecStmt.iteFalse
  · exact clipperEvalTakeLotEqZeroFalseAtCallbackMoveRet v evmLoc evmRead evmVat
      evmMove I price slice owe0 owe slice' tabNew lotNew hlot
  · simpa [checkedExternalCallStmts] using
      ExecBlock.consRevert
        (ExecStmt.requireFalse
          (clipperEvalTakeDogCodeGuardFalseAtCallbackMoveRet v evmLoc evmRead evmVat
            evmMove I price slice owe0 owe slice' tabNew lotNew hnoCode))

theorem clipperTakeDogDigsOweCallFailureBlockAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlot : lotNew ≠ ⟨0⟩)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmMove
      (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
      "digs" 0
      [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (false, evmDog, outDog) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  apply ExecBlock.consRevert
  apply ExecStmt.iteFalse
  · exact clipperEvalTakeLotEqZeroFalseAtCallbackMoveRet v evmLoc evmRead evmVat
      evmMove I price slice owe0 owe slice' tabNew lotNew hlot
  · simpa [checkedExternalCallStmts] using
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (clipperEvalTakeDogCodeGuardTrueAtCallbackMoveRet v evmLoc evmRead evmVat
            evmMove I price slice owe0 owe slice' tabNew lotNew hcode))
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalTakeDogDigsTargetAtCallbackMoveRet v evmLoc evmRead evmVat
              evmMove I price slice owe0 owe slice' tabNew lotNew)
            (by simp [evalExpr?, pure])
            (clipperEvalTakeDogDigsOweArgsAtCallbackMoveRet v evmLoc evmRead evmVat
              evmMove I price slice owe0 owe slice' tabNew lotNew)
            hcall))

theorem clipperTakeDogDigsOweCallSuccessBlockAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlot : lotNew ≠ ⟨0⟩)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmMove
      (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
      "digs" 0
      [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (true, evmDog, outDog) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
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
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog) := by
  apply ExecBlock.consNormal
  · apply ExecStmt.iteFalse
    · exact clipperEvalTakeLotEqZeroFalseAtCallbackMoveRet v evmLoc evmRead evmVat
        evmMove I price slice owe0 owe slice' tabNew lotNew hlot
    · simpa [checkedExternalCallStmts, clipperTakeLocalsCallbackDigsRet,
        collapseReturns] using
        ExecBlock.consNormal
          (ExecStmt.requireTrue
            (clipperEvalTakeDogCodeGuardTrueAtCallbackMoveRet v evmLoc evmRead evmVat
              evmMove I price slice owe0 owe slice' tabNew lotNew hcode))
          (ExecBlock.consNormal
            (ExecStmt.externalCallSuccess
              (clipperEvalTakeDogDigsTargetAtCallbackMoveRet v evmLoc evmRead evmVat
                evmMove I price slice owe0 owe slice' tabNew lotNew)
              (by simp [evalExpr?, pure])
              (clipperEvalTakeDogDigsOweArgsAtCallbackMoveRet v evmLoc evmRead evmVat
                evmMove I price slice owe0 owe slice' tabNew lotNew)
              hcall (clipperTakeDecodeDigsVoid v outDog))
            ExecBlock.nil)
  · exact ExecBlock.nil

theorem clipperEvalTakeDigsAmtAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (htab : tabNew = ⟨0⟩)
    (howe : owe = clipperTakeSalesTabEVMWord evmRead I) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (wrap256 (.binary .add (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  subst tabNew
  subst owe
  let moveFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0
      (clipperTakeSalesTabEVMWord evmRead I) slice' ⟨0⟩ lotNew)
  have htabEval : evalExpr? (config v) moveFrame evmMove (.var "tab") =
      .ok (.int 0) := by
    simp only [moveFrame, evalExpr?]
    rw [clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_self]
    rfl
  have howeEval : evalExpr? (config v) moveFrame evmMove (.var "owe") =
      .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [moveFrame, evalExpr?]
    rw [clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_self]
    rfl
  have hmod :
      Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat % wordModulus =
        Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat := by
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · have hlt := (clipperTakeSalesTabEVMWord evmRead I).val.isLt
      norm_num [wordModulus, UInt256.size] at hlt ⊢
      exact_mod_cast hlt
  simp [moveFrame, wrap256, evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    htabEval, howeEval, wordModulus, hmod]
  simpa [wordModulus] using hmod

theorem clipperEvalTakeDogDigsTargetAtCallbackDigsAmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (.var "dog_") =
        .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsCallbackDigsAmt, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_self]
  rfl

theorem clipperEvalTakeDogDigsAmtArgsAtCallbackDigsAmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove [ilkExpr v, .var "digsAmt"] =
        .ok [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
  have hilk :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove (ilkExpr v) = .ok v.ilk := by
    rcases v.ilk_wf with ⟨bs, hbs, _hlen⟩
    simp [ilkExpr, hbs, evalExpr?, pure]
  have hdigs :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmMove (.var "digsAmt") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsCallbackDigsAmt, store_get_self]
    rfl
  simp only [evalExprs?, hilk, hdigs, EvalResult.bind, bind, pure]

theorem clipperEvalTakeDogCodeGuardAtCallbackDigsAmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool
          (0 <
            (UInt256.ofNat
              ((evmMove.lookupAccount
                (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
                0 (fun acc => acc.code.size))).toNat)) := by
  simp [evalExpr?, EvalResult.bind, bind,
    clipperEvalTakeDogDigsTargetAtCallbackDigsAmt, evalBinaryOp?, EVM.Word.ofNat]

theorem clipperTakeDogDigsOweZeroNoCodeBlockAtCallbackMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew = ⟨0⟩) (htab : tabNew = ⟨0⟩)
    (howe : owe = clipperTakeSalesTabEVMWord evmRead I)
    (hnoCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove
      [ .ite (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  let moveFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hdigs : ExecStmt (config v) moveFrame evmMove
      (.letDecl "digsAmt" (some uint256)
        (wrap256 (.binary .add (.var "tab") (.var "owe"))))
      (.ok digsFrame evmMove) := by
    simpa [moveFrame, digsFrame, clipperTakeLocalsCallbackDigsAmt] using
      ExecStmt.letDecl
        (clipperEvalTakeDigsAmtAtCallbackMoveRet v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe slice' tabNew lotNew htab howe)
  have hdog : ExecBlock (config v) digsFrame evmMove
      (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
        [ilkExpr v, .var "digsAmt"] "_digsRet") .reverted := by
    have hguard : evalExpr? (config v) digsFrame evmMove
        (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
          .ok (.bool false) := by
      simpa [digsFrame, hnoCode] using
        (clipperEvalTakeDogCodeGuardAtCallbackDigsAmt v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe slice' tabNew lotNew)
    simpa [checkedExternalCallStmts] using
      ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  apply ExecBlock.consRevert
  apply ExecStmt.iteTrue
  · simpa [moveFrame] using
      (clipperEvalTakeLotEqZeroTrueAtCallbackMoveRet v evmLoc evmRead evmVat evmMove I
        price slice owe0 owe slice' tabNew lotNew hlot)
  · simpa [wrappingAddInto, moveFrame] using ExecBlock.consNormal hdigs hdog

theorem clipperTakeDogDigsOweZeroCallFailureBlockAtCallbackMoveRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlot : lotNew = ⟨0⟩) (htab : tabNew = ⟨0⟩)
    (howe : owe = clipperTakeSalesTabEVMWord evmRead I)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmMove
      (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
      "digs" 0
      [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (false, evmDog, outDog) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove
      [ .ite (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      .reverted := by
  let moveFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hdigs : ExecStmt (config v) moveFrame evmMove
      (.letDecl "digsAmt" (some uint256)
        (wrap256 (.binary .add (.var "tab") (.var "owe"))))
      (.ok digsFrame evmMove) := by
    simpa [moveFrame, digsFrame, clipperTakeLocalsCallbackDigsAmt] using
      ExecStmt.letDecl
        (clipperEvalTakeDigsAmtAtCallbackMoveRet v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe slice' tabNew lotNew htab howe)
  have hdog : ExecBlock (config v) digsFrame evmMove
      (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
        [ilkExpr v, .var "digsAmt"] "_digsRet") .reverted := by
    have hguard : evalExpr? (config v) digsFrame evmMove
        (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
          .ok (.bool true) := by
      simpa [digsFrame, hcode] using
        (clipperEvalTakeDogCodeGuardAtCallbackDigsAmt v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe slice' tabNew lotNew)
    simpa [checkedExternalCallStmts] using
      ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalTakeDogDigsTargetAtCallbackDigsAmt v evmLoc evmRead evmVat
              evmMove I price slice owe0 owe slice' tabNew lotNew)
            (by simp [evalExpr?, pure])
            (clipperEvalTakeDogDigsAmtArgsAtCallbackDigsAmt v evmLoc evmRead evmVat
              evmMove I price slice owe0 owe slice' tabNew lotNew)
            hcall))
  apply ExecBlock.consRevert
  apply ExecStmt.iteTrue
  · simpa [moveFrame] using
      (clipperEvalTakeLotEqZeroTrueAtCallbackMoveRet v evmLoc evmRead evmVat evmMove I
        price slice owe0 owe slice' tabNew lotNew hlot)
  · simpa [wrappingAddInto, moveFrame] using ExecBlock.consNormal hdigs hdog

theorem clipperTakeDogDigsOweZeroCallSuccessBlockAtCallbackMoveRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlot : lotNew = ⟨0⟩) (htab : tabNew = ⟨0⟩)
    (howe : owe = clipperTakeSalesTabEVMWord evmRead I)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmMove.lookupAccount
            (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmMove
      (EVM.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
      "digs" 0
      [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)]
      (true, evmDog, outDog) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmMove
      [ .ite (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog) := by
  let moveFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  let retFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hdigs : ExecStmt (config v) moveFrame evmMove
      (.letDecl "digsAmt" (some uint256)
        (wrap256 (.binary .add (.var "tab") (.var "owe"))))
      (.ok digsFrame evmMove) := by
    simpa [moveFrame, digsFrame, clipperTakeLocalsCallbackDigsAmt] using
      ExecStmt.letDecl
        (clipperEvalTakeDigsAmtAtCallbackMoveRet v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe slice' tabNew lotNew htab howe)
  have hdog : ExecBlock (config v) digsFrame evmMove
      (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
        [ilkExpr v, .var "digsAmt"] "_digsRet") (.ok retFrame evmDog) := by
    have hguard : evalExpr? (config v) digsFrame evmMove
        (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
          .ok (.bool true) := by
      simpa [digsFrame, hcode] using
        (clipperEvalTakeDogCodeGuardAtCallbackDigsAmt v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe slice' tabNew lotNew)
    simpa [checkedExternalCallStmts, retFrame,
      clipperTakeLocalsCallbackDigsAmtRet, collapseReturns] using
      ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consNormal
          (ExecStmt.externalCallSuccess
            (clipperEvalTakeDogDigsTargetAtCallbackDigsAmt v evmLoc evmRead evmVat
              evmMove I price slice owe0 owe slice' tabNew lotNew)
            (by simp [evalExpr?, pure])
            (clipperEvalTakeDogDigsAmtArgsAtCallbackDigsAmt v evmLoc evmRead evmVat
              evmMove I price slice owe0 owe slice' tabNew lotNew)
            hcall (clipperTakeDecodeDigsVoid v outDog))
          ExecBlock.nil)
  apply ExecBlock.consNormal
  · apply ExecStmt.iteTrue
    · simpa [moveFrame] using
        (clipperEvalTakeLotEqZeroTrueAtCallbackMoveRet v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe slice' tabNew lotNew hlot)
    · simpa [wrappingAddInto, moveFrame, retFrame] using
        execBlockAppendOk (ExecBlock.consNormal hdigs ExecBlock.nil) hdog
  · exact ExecBlock.nil

theorem clipperTakeLocalsCallbackDigsRetLocked
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew).get? "locked" = none := by
  simp [clipperTakeLocalsCallbackDigsRet, clipperTakeLocalsCallbackMoveRet,
    clipperTakeLocalsCallbackRet, clipperTakeLocalsDogLoaded,
    clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
    clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew, clipperTakeLocalsTabNew,
    clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab, clipperTakeLocalsOwe,
    clipperTakeLocalsOwe0, clipperTakeLocalsSlice, clipperTakeLocalsTab,
    clipperTakeLocalsLot, clipperTakeLocalsPrice, clipperTakeLocalsDone,
    clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
    clipperTakeStore]

theorem clipperEvalTakeVarIdAtCallbackDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.var "id") = .ok (clipperTakeIdValue I) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsCallbackDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
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

theorem clipperEvalTakeVarTabAtCallbackDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.var "tab") = .ok (.int (Int.ofNat tabNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsCallbackDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_self]
  rfl

theorem clipperEvalTakeVarLotAtCallbackDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evmDog : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.var "lot") = .ok (.int (Int.ofNat lotNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsCallbackDigsRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  rfl

theorem clipperEvalTakeLotEqZeroFalseAtCallbackDigsRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool false) := by
  have htoNat : lotNew.toNat ≠ 0 := by
    intro hzero
    exact hlot (uint256_toNat_eq_zero hzero)
  simp [evalExpr?, EvalResult.bind, bind, pure,
    clipperEvalTakeVarLotAtCallbackDigsRet, evalBinaryOp?, htoNat]

theorem clipperEvalTakeTabEqZeroTrueAtCallbackDigsRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (htab : tabNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "tab") (.intLit 0)) = .ok (.bool true) := by
  subst tabNew
  simp [evalExpr?, EvalResult.bind, bind, pure,
    clipperEvalTakeVarTabAtCallbackDigsRet, evalBinaryOp?]

theorem clipperEvalTakeVatFluxUsrArgsAtCallbackDigsRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog [ilkExpr v, thisAddr, .var "usr", .var "lot"] =
        .ok
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
            .int (Int.ofNat lotNew.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  have hilkEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog (ilkExpr v) = .ok v.ilk := by
    simp [ilkExpr, hilk, evalExpr?, pure]
  have hthisEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog thisAddr = .ok (.address evmDog.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have husrEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog (.var "usr") =
          .ok (.address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsCallbackDigsRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
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
      clipperTakeLocalsUsr, store_get_self]
    rfl
  simp only [evalExprs?, hilkEval, hthisEval, husrEval,
    clipperEvalTakeVarLotAtCallbackDigsRet, EvalResult.bind, bind, pure]

theorem clipperTakePostDogTabZeroFluxNoCodeBlockAtCallbackDigsRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew ≠ ⟨0⟩) (htab : tabNew = ⟨0⟩)
    (hnoCode :
      (UInt256.ofNat ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (clipperTakePostDogStmts v) .reverted := by
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hflux :
      ExecBlock (config v) digsFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        .reverted := by
    simpa [checkedExternalCallStmts, digsFrame] using
      ExecBlock.consRevert
        (ExecStmt.requireFalse
          (clipperEvalTakeVatCodeGuard_false v evmDog digsFrame.locals hnoCode))
  have htabIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        .reverted := by
    exact ExecStmt.iteTrue
      (by
        simpa [digsFrame] using
          (clipperEvalTakeTabEqZeroTrueAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew htab))
      (execBlockAppendReverted hflux)
  have hlotIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        .reverted := by
    exact ExecStmt.iteFalse
      (by
        simpa [digsFrame] using
          (clipperEvalTakeLotEqZeroFalseAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew hlot))
      (ExecBlock.consRevert htabIte)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hlotIte

theorem clipperTakePostDogTabZeroFluxCallFailureBlockAtCallbackDigsRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outFlux : ByteArray}
    (hlot : lotNew ≠ ⟨0⟩) (htab : tabNew = ⟨0⟩)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
      [v.ilk, .address evmDog.executionEnv.codeOwner,
        .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
        .int (Int.ofNat lotNew.toNat)]
      (false, evmFlux, outFlux) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (clipperTakePostDogStmts v) .reverted := by
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hflux :
      ExecBlock (config v) digsFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        .reverted := by
    simpa [checkedExternalCallStmts, digsFrame] using
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (clipperEvalTakeVatCodeGuard_true v evmDog digsFrame.locals hcode))
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalVat v evmDog digsFrame.locals)
            (by simp [evalExpr?, pure])
            (clipperEvalTakeVatFluxUsrArgsAtCallbackDigsRet v evmLoc evmRead evmVat
              evmDog I price slice owe0 owe slice' tabNew lotNew)
            hcall))
  have htabIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        .reverted := by
    exact ExecStmt.iteTrue
      (by
        simpa [digsFrame] using
          (clipperEvalTakeTabEqZeroTrueAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew htab))
      (execBlockAppendReverted hflux)
  have hlotIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        .reverted := by
    exact ExecStmt.iteFalse
      (by
        simpa [digsFrame] using
          (clipperEvalTakeLotEqZeroFalseAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew hlot))
      (ExecBlock.consRevert htabIte)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hlotIte

theorem clipperTakePostDogFluxRetRemoveArgsAtCallbackDigsRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    let fluxFrame : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_fluxUsrRet" .unit }
    evalExprs? (config v) fluxFrame evmFlux [.var "id"] =
      .ok [clipperYankArgValue I] := by
  intro fluxFrame
  apply evalExprs?_singleton
  simp only [fluxFrame, evalExpr?]
  rw [store_get_ne _ _ (by decide)]
  simpa only [evalExpr?, clipperTakeIdValue, clipperYankArgValue,
    clipperTakeIdWord, clipperYankArgWord] using
    (clipperEvalTakeVarIdAtCallbackDigsRet v evmLoc evmRead evmVat evmFlux I price
      slice owe0 owe slice' tabNew lotNew)

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogTabZeroFluxRemoveSourceRevertsAtCallbackDigsRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outFlux : ByteArray}
    (hlot : lotNew ≠ ⟨0⟩) (htab : tabNew = ⟨0⟩)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
      [v.ilk, .address evmDog.executionEnv.codeOwner,
        .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
        .int (Int.ofNat lotNew.toNat)]
      (true, evmFlux, outFlux) true)
    (hremove : ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I }
      evmFlux removeFunction.body .reverted) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (clipperTakePostDogStmts v) .reverted := by
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  let fluxFrame : Frame :=
    { contract := contract v, locals := digsFrame.locals.insert "_fluxUsrRet" .unit }
  have hflux :
      ExecBlock (config v) digsFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        (.ok fluxFrame evmFlux) := by
    simpa [checkedExternalCallStmts, digsFrame, fluxFrame, collapseReturns] using
      checkedExternalCallSuccess
        (clipperEvalTakeVatCodeGuard_true v evmDog digsFrame.locals hcode)
        (clipperEvalVat v evmDog digsFrame.locals)
        (clipperEvalTakeVatFluxUsrArgsAtCallbackDigsRet v evmLoc evmRead evmVat
          evmDog I price slice owe0 owe slice' tabNew lotNew)
        hcall (clipperTakeDecodeFluxVoid v outFlux)
  have hremoveStmt :
      ExecStmt (config v) fluxFrame evmFlux
        (.internalCall "_remove" [.var "id"] "_removeRet2") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config v) (caller := fluxFrame) (evm := evmFlux)
      (name := "_remove") (retVar := "_removeRet2") (args := [.var "id"])
      (argVals := [clipperYankArgValue I]) (callee := removeFunction)
      (locals := clipperYankRemoveStore I)
      (by
        simpa [fluxFrame, digsFrame] using
          (clipperTakePostDogFluxRetRemoveArgsAtCallbackDigsRet v evmLoc evmRead evmVat
            evmFlux I price slice owe0 owe slice' tabNew lotNew))
      (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremove
  have htabIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        .reverted := by
    exact ExecStmt.iteTrue
      (by
        simpa [digsFrame] using
          (clipperEvalTakeTabEqZeroTrueAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew htab))
      (execBlockAppendOk hflux (ExecBlock.consRevert hremoveStmt))
  have hlotIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        .reverted := by
    exact ExecStmt.iteFalse
      (by
        simpa [digsFrame] using
          (clipperEvalTakeLotEqZeroFalseAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew hlot))
      (ExecBlock.consRevert htabIte)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hlotIte

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogTabZeroFluxRemoveSourceOkAtCallbackDigsRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux evmRemove : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256)
    {outFlux : ByteArray} {calleeSolm : Frame}
    (hlot : lotNew ≠ ⟨0⟩) (htab : tabNew = ⟨0⟩)
    (hcode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
      [v.ilk, .address evmDog.executionEnv.codeOwner,
        .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
        .int (Int.ofNat lotNew.toNat)]
      (true, evmFlux, outFlux) true)
    (hremove : ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I }
      evmFlux removeFunction.body (.returned calleeSolm evmRemove none)) :
    let resultFrame : Frame :=
      { contract := contract v,
        locals :=
          ((clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_fluxUsrRet" .unit).insert
              "_removeRet2" .unit }
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (clipperTakePostDogStmts v)
      (.ok resultFrame
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro resultFrame
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  let fluxFrame : Frame :=
    { contract := contract v, locals := digsFrame.locals.insert "_fluxUsrRet" .unit }
  have hflux :
      ExecBlock (config v) digsFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        (.ok fluxFrame evmFlux) := by
    simpa [checkedExternalCallStmts, digsFrame, fluxFrame, collapseReturns] using
      checkedExternalCallSuccess
        (clipperEvalTakeVatCodeGuard_true v evmDog digsFrame.locals hcode)
        (clipperEvalVat v evmDog digsFrame.locals)
        (clipperEvalTakeVatFluxUsrArgsAtCallbackDigsRet v evmLoc evmRead evmVat
          evmDog I price slice owe0 owe slice' tabNew lotNew)
        hcall (clipperTakeDecodeFluxVoid v outFlux)
  have hremoveStmt :
      ExecStmt (config v) fluxFrame evmFlux
        (.internalCall "_remove" [.var "id"] "_removeRet2")
        (.ok resultFrame evmRemove) := by
    simpa [resumeAfterInternalCall, fluxFrame, digsFrame, resultFrame] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := fluxFrame) (evm := evmFlux)
        (name := "_remove") (retVar := "_removeRet2") (args := [.var "id"])
        (argVals := [clipperYankArgValue I]) (callee := removeFunction)
        (locals := clipperYankRemoveStore I) (calleeSolm := calleeSolm)
        (calleeEvm := evmRemove) (value := none)
        (by
          simpa [fluxFrame, digsFrame] using
            (clipperTakePostDogFluxRetRemoveArgsAtCallbackDigsRet v evmLoc evmRead evmVat
              evmFlux I price slice owe0 owe slice' tabNew lotNew))
        (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremove)
  have htabIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        (.ok resultFrame evmRemove) := by
    exact ExecStmt.iteTrue
      (by
        simpa [digsFrame] using
          (clipperEvalTakeTabEqZeroTrueAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew htab))
      (execBlockAppendOk hflux (ExecBlock.consNormal hremoveStmt ExecBlock.nil))
  have hlotIte :
      ExecStmt (config v) digsFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        (.ok resultFrame evmRemove) := by
    exact ExecStmt.iteFalse
      (by
        simpa [digsFrame] using
          (clipperEvalTakeLotEqZeroFalseAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew hlot))
      (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hunlock :
      ExecStmt (config v) resultFrame evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok resultFrame
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    have hlocked : resultFrame.locals.get? "locked" = none := by
      simp only [resultFrame]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
      exact clipperTakeLocalsCallbackDigsRetLocked evmLoc evmRead evmVat I price slice
        owe0 owe slice' tabNew lotNew
    apply ExecStmt.assign (value := .int 0)
    · simp [evalExpr?, pure]
    · simpa [resultFrame] using
        (assign_clipperLocked v evmRemove resultFrame.locals hlocked ⟨0⟩)
  simpa only [clipperTakePostDogStmts] using
    ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)

theorem clipperTakeRemoveArgsAtCallbackDigsAmtRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog [.var "id"] = .ok [clipperYankArgValue I] := by
  apply evalExprs?_singleton
  simp only [evalExpr?]
  rw [clipperTakeLocalsCallbackDigsAmtRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackDigsAmt, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
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

theorem clipperEvalTakeLotEqZeroTrueAtCallbackDigsAmtRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
  subst lotNew
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsCallbackDigsAmtRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackDigsAmt, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsCallbackRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_self]
  rfl

theorem clipperTakePostDogLotZeroRemoveSourceRevertsAtCallbackDigsAmtRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlot : lotNew = ⟨0⟩)
    (hremove : ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I }
      evmDog removeFunction.body .reverted) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (clipperTakePostDogStmts v) .reverted := by
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hremoveStmt : ExecStmt (config v) digsFrame evmDog
      (.internalCall "_remove" [.var "id"] "_removeRet") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config v) (caller := digsFrame) (evm := evmDog)
      (name := "_remove") (retVar := "_removeRet") (args := [.var "id"])
      (argVals := [clipperYankArgValue I]) (callee := removeFunction)
      (locals := clipperYankRemoveStore I)
      (by simpa [digsFrame] using
        (clipperTakeRemoveArgsAtCallbackDigsAmtRet v evmLoc evmRead evmVat evmDog I
          price slice owe0 owe slice' tabNew lotNew))
      (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremove
  have hlotIte : ExecStmt (config v) digsFrame evmDog
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
              [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      .reverted := by
    exact ExecStmt.iteTrue
      (by simpa [digsFrame] using
        (clipperEvalTakeLotEqZeroTrueAtCallbackDigsAmtRet v evmLoc evmRead evmVat evmDog I
          price slice owe0 owe slice' tabNew lotNew hlot))
      (ExecBlock.consRevert hremoveStmt)
  simpa only [clipperTakePostDogStmts] using ExecBlock.consRevert hlotIte

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogLotZeroRemoveSourceOkAtCallbackDigsAmtRet
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmRemove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {calleeSolm : Frame}
    (hlot : lotNew = ⟨0⟩)
    (hremove : ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I }
      evmDog removeFunction.body (.returned calleeSolm evmRemove none)) :
    let resultFrame : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_removeRet" .unit }
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (clipperTakePostDogStmts v)
      (.ok resultFrame
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro resultFrame
  let digsFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
      slice' tabNew lotNew)
  have hremoveStmt : ExecStmt (config v) digsFrame evmDog
      (.internalCall "_remove" [.var "id"] "_removeRet")
      (.ok resultFrame evmRemove) := by
    simpa [resumeAfterInternalCall, digsFrame, resultFrame] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := digsFrame) (evm := evmDog)
        (name := "_remove") (retVar := "_removeRet") (args := [.var "id"])
        (argVals := [clipperYankArgValue I]) (callee := removeFunction)
        (locals := clipperYankRemoveStore I) (calleeSolm := calleeSolm)
        (calleeEvm := evmRemove) (value := none)
        (by simpa [digsFrame] using
          (clipperTakeRemoveArgsAtCallbackDigsAmtRet v evmLoc evmRead evmVat evmDog I
            price slice owe0 owe slice' tabNew lotNew))
        (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremove)
  have hlotIte : ExecStmt (config v) digsFrame evmDog
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
              [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      (.ok resultFrame evmRemove) := by
    exact ExecStmt.iteTrue
      (by simpa [digsFrame] using
        (clipperEvalTakeLotEqZeroTrueAtCallbackDigsAmtRet v evmLoc evmRead evmVat evmDog I
          price slice owe0 owe slice' tabNew lotNew hlot))
      (ExecBlock.consNormal hremoveStmt ExecBlock.nil)
  have hlocked : resultFrame.locals.get? "locked" = none := by
    simp only [resultFrame]
    rw [store_get_ne _ _ (by decide)]
    simp [clipperTakeLocalsCallbackDigsAmtRet,
      clipperTakeLocalsCallbackDigsAmt, clipperTakeLocalsCallbackMoveRet,
      clipperTakeLocalsCallbackRet, clipperTakeLocalsDogLoaded,
      clipperTakeLocalsFluxBuyerRet, clipperTakeLocalsLotAssigned,
      clipperTakeLocalsTabAssigned, clipperTakeLocalsLotNew,
      clipperTakeLocalsTabNew, clipperTakeLocalsOweTabSlice,
      clipperTakeLocalsOweTab, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
      clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
      clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
      clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore]
  have hunlock : ExecStmt (config v) resultFrame evmRemove
      (.assign .storage lockedRef (.intLit 0))
      (.ok resultFrame
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    apply ExecStmt.assign (value := .int 0)
    · simp [evalExpr?, pure]
    · simpa [resultFrame] using
        (assign_clipperLocked v evmRemove resultFrame.locals hlocked ⟨0⟩)
  simpa only [clipperTakePostDogStmts] using
    ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)

theorem clipperEvalTakeTabEqZeroFalseAtCallbackDigsRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (htab : tabNew ≠ ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog (.binary .eq (.var "tab") (.intLit 0)) = .ok (.bool false) := by
  have htoNat : tabNew.toNat ≠ 0 := by
    intro hzero
    exact htab (uint256_toNat_eq_zero hzero)
  simp [evalExpr?, EvalResult.bind, bind, pure,
    clipperEvalTakeVarTabAtCallbackDigsRet, evalBinaryOp?, htoNat]

theorem clipperTakeAssignSalesTabAtCallbackDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evm : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    assignStorageRef? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evm .storage (salesF (.var "id") "tab") (.int (Int.ofNat tabNew.toNat)) =
      .ok
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperTakeSalesTabSlot I)
            tabNew) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesTabRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesTabSlot I))
  · simp [salesF, clipperTakeLocalsCallbackDigsRet,
      clipperTakeLocalsCallbackMoveRet, clipperTakeLocalsCallbackRet,
      clipperTakeLocalsDogLoaded, clipperTakeLocalsFluxBuyerRet,
      clipperTakeLocalsLotAssigned, clipperTakeLocalsTabAssigned,
      clipperTakeLocalsLotNew, clipperTakeLocalsTabNew,
      clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab, clipperTakeLocalsOwe,
      clipperTakeLocalsOwe0, clipperTakeLocalsSlice, clipperTakeLocalsTab,
      clipperTakeLocalsLot, clipperTakeLocalsPrice, clipperTakeLocalsDone,
      clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
      clipperTakeStore]
  · simp [clipperTakeSalesTabRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeVarIdAtCallbackDigsRet v evmLoc evmRead evmVat evm I price slice
        owe0 owe slice' tabNew lotNew,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesTabSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesTabSlot I) tabNew

theorem clipperTakeAssignSalesLotAtCallbackDigsRet
    (v : ClipperImmutables) (evmLoc evmRead evmVat evm : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    assignStorageRef? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evm .storage (salesF (.var "id") "lot") (.int (Int.ofNat lotNew.toNat)) =
      .ok
        (Frame.mk (contract v)
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew),
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperTakeSalesLotSlot I)
            lotNew) := by
  apply assignStorageRef_storage_scalar
    (er := clipperTakeSalesLotRef I) (ty := uint256St)
    (loc := wordLoc (clipperTakeSalesLotSlot I))
  · simp [salesF, clipperTakeLocalsCallbackDigsRet,
      clipperTakeLocalsCallbackMoveRet, clipperTakeLocalsCallbackRet,
      clipperTakeLocalsDogLoaded, clipperTakeLocalsFluxBuyerRet,
      clipperTakeLocalsLotAssigned, clipperTakeLocalsTabAssigned,
      clipperTakeLocalsLotNew, clipperTakeLocalsTabNew,
      clipperTakeLocalsOweTabSlice, clipperTakeLocalsOweTab, clipperTakeLocalsOwe,
      clipperTakeLocalsOwe0, clipperTakeLocalsSlice, clipperTakeLocalsTab,
      clipperTakeLocalsLot, clipperTakeLocalsPrice, clipperTakeLocalsDone,
      clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
      clipperTakeStore]
  · simp [clipperTakeSalesLotRef, clipperTakeIdKey, salesF,
      evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      clipperEvalTakeVarIdAtCallbackDigsRet v evmLoc evmRead evmVat evm I price slice
        owe0 owe slice' tabNew lotNew,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  · simp [clipperTakeIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperTakeSalesLotSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperTakeSalesLotSlot I) lotNew

theorem clipperTakeDogDigsOweNonzeroStoreSourceOkAtCallbackMoveRet
    (v : ClipperImmutables)
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
        (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
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
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro evmTab evmLot
  let moveFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackMoveRet evmLoc evmRead evmVat I price slice owe0 owe slice'
      tabNew lotNew)
  let digsRetFrame := Frame.mk (contract v)
    (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe slice'
      tabNew lotNew)
  have hdog : ExecBlock (config v) moveFrame evmMove
      [ .ite (.binary .eq (.var "lot") (.intLit 0))
          (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
            checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
              [ilkExpr v, .var "digsAmt"] "_digsRet")
          (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "owe"] "_digsRet") ]
      (.ok digsRetFrame evmDog) := by
    simpa [moveFrame, digsRetFrame] using
      clipperTakeDogDigsOweCallSuccessBlockAtCallbackMoveRet v evmLoc evmRead evmVat
        evmMove evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew hdogCode hcallDog
  have hlotCond := clipperEvalTakeLotEqZeroFalseAtCallbackDigsRet v evmLoc evmRead
    evmVat evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroFalseAtCallbackDigsRet v evmLoc evmRead
    evmVat evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have htabStmt : ExecStmt (config v) digsRetFrame evmDog
      (.assign .storage (salesF (.var "id") "tab") (.var "tab"))
      (.ok digsRetFrame evmTab) := by
    exact ExecStmt.assign
      (by simpa [digsRetFrame] using
        (clipperEvalTakeVarTabAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I price
          slice owe0 owe slice' tabNew lotNew))
      (by simpa [digsRetFrame, evmTab] using
        (clipperTakeAssignSalesTabAtCallbackDigsRet v evmLoc evmRead evmVat evmDog I
          price slice owe0 owe slice' tabNew lotNew))
  have hlotStmt : ExecStmt (config v) digsRetFrame evmTab
      (.assign .storage (salesF (.var "id") "lot") (.var "lot"))
      (.ok digsRetFrame evmLot) := by
    exact ExecStmt.assign
      (by simpa [digsRetFrame] using
        (clipperEvalTakeVarLotAtCallbackDigsRet v evmLoc evmRead evmVat evmTab I price
          slice owe0 owe slice' tabNew lotNew))
      (by simpa [digsRetFrame, evmLot] using
        (clipperTakeAssignSalesLotAtCallbackDigsRet v evmLoc evmRead evmVat evmTab I
          price slice owe0 owe slice' tabNew lotNew))
  have hstoreBlock := ExecBlock.consNormal htabStmt
    (ExecBlock.consNormal hlotStmt ExecBlock.nil)
  have htabIte : ExecStmt (config v) digsRetFrame evmDog
      (.ite (.binary .eq (.var "tab") (.intLit 0))
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
          [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
        [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
          .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
      (.ok digsRetFrame evmLot) := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using htabCond) hstoreBlock
  have hlotIte : ExecStmt (config v) digsRetFrame evmDog
      (.ite (.binary .eq (.var "lot") (.intLit 0))
        [ .internalCall "_remove" [.var "id"] "_removeRet" ]
        [ .ite (.binary .eq (.var "tab") (.intLit 0))
            (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
              [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
              [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
            [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
              .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
      (.ok digsRetFrame evmLot) := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hunlock : ExecStmt (config v) digsRetFrame evmLot
      (.assign .storage lockedRef (.intLit 0))
      (.ok digsRetFrame
        (Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    have hzero : evalExpr? (config v) digsRetFrame evmLot (.intLit 0) =
        .ok (.int 0) := by
      simp [evalExpr?, pure, digsRetFrame]
    have hassign : assignStorageRef? (config v) digsRetFrame evmLot
        .storage lockedRef (.int 0) =
        .ok (digsRetFrame,
          Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
      simpa [digsRetFrame] using
        (assign_clipperLocked v evmLot
          (clipperTakeLocalsCallbackDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew)
          (clipperTakeLocalsCallbackDigsRetLocked evmLoc evmRead evmVat I price slice owe0
            owe slice' tabNew lotNew) ⟨0⟩)
    exact ExecStmt.assign hzero hassign
  exact execBlockAppendOk hdog
    (ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil))

end Benchmarks.Dss.Clipper
