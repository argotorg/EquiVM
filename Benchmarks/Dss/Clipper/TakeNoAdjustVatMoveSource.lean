import Benchmarks.Dss.Clipper.TakeNoAdjustSource
import Benchmarks.Dss.Clipper.TakeVatMoveSource
import Benchmarks.Dss.Clipper.YankSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperTakeLocalsNoAdjustDogLoaded (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe tabNew
    lotNew).insert "dog_"
      (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))

abbrev clipperTakeLocalsNoAdjustMoveRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
    tabNew lotNew).insert "_moveRet" .unit

abbrev clipperTakeLocalsNoAdjustDigsRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
    tabNew lotNew).insert "_digsRet" .unit

abbrev clipperTakeLocalsNoAdjustDigsAmt (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
    tabNew lotNew).insert "digsAmt"
      (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat))

abbrev clipperTakeLocalsNoAdjustDigsAmtRet (evmLoc evmRead evmVat : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
    tabNew lotNew).insert "_digsRet" .unit

theorem clipperEvalTakeNoAdjustDataLengthZero (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmVat (bytesLength "data") = .ok (.int 0) := by
  simp only [bytesLength, localRef, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
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
    clipperTakeStore, store_get_self]
  simp [clipperTakeDataBytes, hdataLen]

theorem clipperEvalTakeNoAdjustCallbackGuardDataEmpty (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) =
        .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperEvalTakeNoAdjustDataLengthZero v evmLoc evmRead evmVat I price slice owe0
    owe tabNew lotNew hdataLen]
  simp [evalBinaryOp?]

theorem clipperEvalTakeNoAdjustVatMoveArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmVat [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmVat.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
            .int (Int.ofNat owe.toNat)] := by
  have hsender :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmVat sender = .ok (.address evmVat.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  have hvow :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmVat (.storage vowRef) =
          .ok (.address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat)) := by
    simpa [clipperTakeVowEVMWord] using
      clipperEvalVow v evmVat
        (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew)
        (by
          simp [clipperTakeLocalsNoAdjustDogLoaded,
            clipperTakeLocalsNoAdjustFluxBuyerRet, clipperTakeLocalsNoAdjustLotAssigned,
            clipperTakeLocalsNoAdjustTabAssigned, clipperTakeLocalsNoAdjustLotNew,
            clipperTakeLocalsNoAdjustTabNew, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
            clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
            clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
            clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore])
  have howe :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmVat (.var "owe") = .ok (.int (Int.ofNat owe.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_self]
    rfl
  simp only [evalExprs?, hsender, hvow, howe, EvalResult.bind, bind, pure]

theorem clipperTakeNoAdjustVatMoveNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hnoVatCode :
      (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
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
      (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
        tabNew lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsNoAdjustDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                tabNew lotNew)
              (by
                simp [clipperTakeLocalsNoAdjustFluxBuyerRet,
                  clipperTakeLocalsNoAdjustLotAssigned,
                  clipperTakeLocalsNoAdjustTabAssigned, clipperTakeLocalsNoAdjustLotNew,
                  clipperTakeLocalsNoAdjustTabNew, clipperTakeLocalsOwe,
                  clipperTakeLocalsOwe0, clipperTakeLocalsSlice, clipperTakeLocalsTab,
                  clipperTakeLocalsLot, clipperTakeLocalsPrice, clipperTakeLocalsDone,
                  clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
                  clipperTakeStore])))
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
        (clipperEvalTakeNoAdjustCallbackGuardDataEmpty v evmLoc evmRead evmVat I price
          slice owe0 owe tabNew lotNew hdataLen)
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
        (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew) hnoVatCode
    simpa [checkedExternalCallStmts, dogFrame] using
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
  simpa [startFrame, dogFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal hcallback hmoveRevert))

theorem clipperTakeNoAdjustVatMoveCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outMove : ByteArray}
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat owe.toNat)]
        (false, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
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
      (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
        tabNew lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsNoAdjustDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                tabNew lotNew)
              (by
                simp [clipperTakeLocalsNoAdjustFluxBuyerRet,
                  clipperTakeLocalsNoAdjustLotAssigned,
                  clipperTakeLocalsNoAdjustTabAssigned, clipperTakeLocalsNoAdjustLotNew,
                  clipperTakeLocalsNoAdjustTabNew, clipperTakeLocalsOwe,
                  clipperTakeLocalsOwe0, clipperTakeLocalsSlice, clipperTakeLocalsTab,
                  clipperTakeLocalsLot, clipperTakeLocalsPrice, clipperTakeLocalsDone,
                  clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
                  clipperTakeStore])))
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
        (clipperEvalTakeNoAdjustCallbackGuardDataEmpty v evmLoc evmRead evmVat I price
          slice owe0 owe tabNew lotNew hdataLen)
        ExecBlock.nil
  have hargs :
      evalExprs? (config v) dogFrame evmVat [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmVat.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
            .int (Int.ofNat owe.toNat)] := by
    simpa [dogFrame] using
      clipperEvalTakeNoAdjustVatMoveArgs v evmLoc evmRead evmVat I price slice owe0 owe
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
        (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew) hvatCode
    simpa [checkedExternalCallStmts, dogFrame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalVat v evmVat
              (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
                tabNew lotNew))
            (by simp [evalExpr?, pure]) hargs hcallMove)))
  simpa [startFrame, dogFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal hcallback hmoveRevert))

theorem clipperTakeNoAdjustVatMoveCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outMove : ByteArray}
    (hdataLen : clipperTakeDataLenWord I = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmVat.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallMove :
      typedCallViaEVM (config v) evmVat (EVM.address v.vat) "move" 0
        [.address evmVat.executionEnv.source,
          .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
          .int (Int.ofNat owe.toNat)]
        (true, evmMove, outMove) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
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
          (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmMove) := by
  let startFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
        tabNew lotNew)
  let dogFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hletDog :
      ExecStmt (config v) startFrame evmVat
        (.letDecl "dog_" (some addr) (.storage dogRef))
        (.ok dogFrame evmVat) := by
    simpa [startFrame, dogFrame, clipperTakeLocalsNoAdjustDogLoaded] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmVat) (name := "dog_")
        (ty := some addr) (expr := .storage dogRef)
        (value := .address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat))
        (by
          simpa [startFrame, clipperTakeDogEVMWord] using
            clipperEvalDog v evmVat
              (clipperTakeLocalsNoAdjustFluxBuyerRet evmLoc evmRead I price slice owe0 owe
                tabNew lotNew)
              (by
                simp [clipperTakeLocalsNoAdjustFluxBuyerRet,
                  clipperTakeLocalsNoAdjustLotAssigned,
                  clipperTakeLocalsNoAdjustTabAssigned, clipperTakeLocalsNoAdjustLotNew,
                  clipperTakeLocalsNoAdjustTabNew, clipperTakeLocalsOwe,
                  clipperTakeLocalsOwe0, clipperTakeLocalsSlice, clipperTakeLocalsTab,
                  clipperTakeLocalsLot, clipperTakeLocalsPrice, clipperTakeLocalsDone,
                  clipperTakeLocalsSt, clipperTakeLocalsTic, clipperTakeLocalsUsr,
                  clipperTakeStore])))
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
        (clipperEvalTakeNoAdjustCallbackGuardDataEmpty v evmLoc evmRead evmVat I price
          slice owe0 owe tabNew lotNew hdataLen)
        ExecBlock.nil
  have hargs :
      evalExprs? (config v) dogFrame evmVat [sender, .storage vowRef, .var "owe"] =
        .ok
          [.address evmVat.executionEnv.source,
            .address (AccountAddress.ofNat (clipperTakeVowEVMWord evmVat).toNat),
            .int (Int.ofNat owe.toNat)] := by
    simpa [dogFrame] using
      clipperEvalTakeNoAdjustVatMoveArgs v evmLoc evmRead evmVat I price slice owe0 owe
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
        (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew) hvatCode
    simpa [checkedExternalCallStmts, dogFrame, moveFrame, clipperTakeLocalsNoAdjustMoveRet,
      collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consNormal
          (ExecStmt.externalCallSuccess
            (clipperEvalVat v evmVat
              (clipperTakeLocalsNoAdjustDogLoaded evmLoc evmRead evmVat I price slice owe0 owe
                tabNew lotNew))
            (by simp [evalExpr?, pure]) hargs hcallMove
            (clipperTakeDecodeMoveVoid v outMove))
          ExecBlock.nil))
  simpa [startFrame, dogFrame, moveFrame, List.append_assoc] using
    (ExecBlock.consNormal hletDog
      (ExecBlock.consNormal hcallback hmove))

theorem clipperEvalTakeTabAtNoAdjustMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.var "tab") = .ok (.int (Int.ofNat tabNew.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustTabAssigned, store_get_self]
  rfl

theorem clipperEvalTakeOweAtNoAdjustMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.var "owe") = .ok (.int (Int.ofNat owe.toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustTabAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustTabNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe, store_get_self]
  rfl

theorem clipperEvalTakeNoAdjustDigsAmtAtMoveRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (htabNew : tabNew = UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (wrap256 (.binary .add (.var "tab") (.var "owe"))) =
        .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
  let tab := clipperTakeSalesTabEVMWord evmRead I
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have htabEval :
      evalExpr? (config v) moveFrame evmMove (.var "tab") =
        .ok (.int (Int.ofNat tabNew.toNat)) := by
    simpa [moveFrame] using
      clipperEvalTakeTabAtNoAdjustMoveRet v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe tabNew lotNew
  have howeEval :
      evalExpr? (config v) moveFrame evmMove (.var "owe") =
        .ok (.int (Int.ofNat owe.toNat)) := by
    simpa [moveFrame] using
      clipperEvalTakeOweAtNoAdjustMoveRet v evmLoc evmRead evmVat evmMove I price slice
        owe0 owe tabNew lotNew
  have htabNewNat : tabNew.toNat = tab.toNat - owe.toNat := by
    have hsub : (UInt256.sub tab owe).toNat = tab.toNat - owe.toNat :=
      usub_toNat (a := tab) (b := owe) (by simpa [tab] using howeTab)
    have heq : tabNew = UInt256.sub tab owe := by
      simpa [tab] using htabNew
    rw [heq, hsub]
  have howeTab' : owe.toNat ≤ tab.toNat := by
    simpa [tab] using howeTab
  have haddNat : tabNew.toNat + owe.toNat = tab.toNat := by
    omega
  have hwordNonzero : ¬wordModulus = 0 := by
    norm_num [wordModulus]
  have hmod :
      (Int.ofNat tabNew.toNat + Int.ofNat owe.toNat) % wordModulus =
        Int.ofNat tab.toNat := by
    rw [show Int.ofNat tabNew.toNat + Int.ofNat owe.toNat =
        Int.ofNat tab.toNat by
      have hcast : (tabNew.toNat : Int) + (owe.toNat : Int) = (tab.toNat : Int) := by
        exact_mod_cast haddNat
      simpa using hcast]
    rw [Int.emod_eq_of_lt]
    · exact Int.natCast_nonneg _
    · have hltNat : tab.toNat < UInt256.size := tab.val.isLt
      norm_num [wordModulus, UInt256.size] at hltNat ⊢
      exact_mod_cast hltNat
  simp [moveFrame, wrap256, evalExpr?, EvalResult.bind, bind, evalBinaryOp?, htabEval,
    howeEval, hwordNonzero]
  exact hmod

theorem clipperEvalTakeNoAdjustLotEqZero_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hlot : lotNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool true) := by
  subst lotNew
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int 0) (.int 0) = .ok (.bool true)
  unfold evalBinaryOp?
  rfl

theorem clipperEvalTakeNoAdjustDogDigsTargetAtDigsAmt (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.var "dog_") =
        .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsNoAdjustDigsAmt, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_self]
  rfl

theorem clipperEvalTakeNoAdjustDogCodeGuardDigsAmt_true (v : ClipperImmutables)
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
        (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalTakeNoAdjustDogDigsTargetAtDigsAmt,
    evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem clipperEvalTakeNoAdjustDogCodeGuardDigsAmt_false (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hnoCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalTakeNoAdjustDogDigsTargetAtDigsAmt,
    evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem clipperEvalTakeNoAdjustDogDigsAmtArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
          tabNew lotNew))
      evmMove [ilkExpr v, .var "digsAmt"] =
        .ok [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
  have hilk :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmMove (ilkExpr v) = .ok v.ilk := by
    rcases v.ilk_wf with ⟨bs, hbs, _hlen⟩
    simp [ilkExpr, hbs, evalExpr?, pure]
  have hdigs :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmMove (.var "digsAmt") =
          .ok (.int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsNoAdjustDigsAmt, store_get_self]
    rfl
  simp only [evalExprs?, hilk, hdigs, EvalResult.bind, bind, pure]

theorem clipperTakeNoAdjustDogDigsOweZeroNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hlotNew : lotNew = ⟨0⟩)
    (htabNew : tabNew = UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hnoDogCode :
      (UInt256.ofNat
        ((evmMove.lookupAccount
          (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
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
      .reverted := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let digsAmtFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [moveFrame] using
      clipperEvalTakeNoAdjustLotEqZero_true v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe tabNew lotNew hlotNew
  have hdigsAmt :
      ExecStmt (config v) moveFrame evmMove
        (.letDecl "digsAmt" (some uint256) (wrap256 (.binary .add (.var "tab") (.var "owe"))))
        (.ok digsAmtFrame evmMove) := by
    have hrhs :=
      clipperEvalTakeNoAdjustDigsAmtAtMoveRet v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe tabNew lotNew htabNew howeTab
    simpa [moveFrame, digsAmtFrame, clipperTakeLocalsNoAdjustDigsAmt] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := moveFrame) (evm := evmMove) (name := "digsAmt")
        (ty := some uint256) (expr := wrap256 (.binary .add (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) hrhs)
  have hdogRevert :
      ExecBlock (config v) digsAmtFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    have hguard :
        evalExpr? (config v) digsAmtFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool false) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeNoAdjustDogCodeGuardDigsAmt_false v evmLoc evmRead evmVat
          evmMove I price slice owe0 owe tabNew lotNew hnoDogCode
    simpa [checkedExternalCallStmts, digsAmtFrame] using
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
  have hthen :
      ExecBlock (config v) moveFrame evmMove
        (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
          checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    simpa [wrappingAddInto, moveFrame] using
      (ExecBlock.consNormal hdigsAmt hdogRevert)
  simpa [moveFrame] using
    ExecBlock.consRevert (ExecStmt.iteTrue hlotCond hthen)

theorem clipperTakeNoAdjustDogDigsOweZeroCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlotNew : lotNew = ⟨0⟩)
    (htabNew : tabNew = UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
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
      .reverted := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let digsAmtFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [moveFrame] using
      clipperEvalTakeNoAdjustLotEqZero_true v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe tabNew lotNew hlotNew
  have hdigsAmt :
      ExecStmt (config v) moveFrame evmMove
        (.letDecl "digsAmt" (some uint256) (wrap256 (.binary .add (.var "tab") (.var "owe"))))
        (.ok digsAmtFrame evmMove) := by
    have hrhs :=
      clipperEvalTakeNoAdjustDigsAmtAtMoveRet v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe tabNew lotNew htabNew howeTab
    simpa [moveFrame, digsAmtFrame, clipperTakeLocalsNoAdjustDigsAmt] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := moveFrame) (evm := evmMove) (name := "digsAmt")
        (ty := some uint256) (expr := wrap256 (.binary .add (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) hrhs)
  have hdogRevert :
      ExecBlock (config v) digsAmtFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    have htarget :
        evalExpr? (config v) digsAmtFrame evmMove (.var "dog_") =
          .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeNoAdjustDogDigsTargetAtDigsAmt v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe tabNew lotNew
    have hguard :
        evalExpr? (config v) digsAmtFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeNoAdjustDogCodeGuardDigsAmt_true v evmLoc evmRead evmVat
          evmMove I price slice owe0 owe tabNew lotNew hdogCode
    have hargs :
        evalExprs? (config v) digsAmtFrame evmMove [ilkExpr v, .var "digsAmt"] =
          .ok [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
      simpa [digsAmtFrame] using
        clipperEvalTakeNoAdjustDogDigsAmtArgs v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe tabNew lotNew
    simpa [checkedExternalCallStmts, digsAmtFrame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consRevert
          (ExecStmt.externalCallFailure htarget (by simp [evalExpr?, pure]) hargs hcallDog)))
  have hthen :
      ExecBlock (config v) moveFrame evmMove
        (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
          checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "digsAmt"] "_digsRet")
        .reverted := by
    simpa [wrappingAddInto, moveFrame] using
      (ExecBlock.consNormal hdigsAmt hdogRevert)
  simpa [moveFrame] using
    ExecBlock.consRevert (ExecStmt.iteTrue hlotCond hthen)

theorem clipperTakeNoAdjustDogDigsOweZeroCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outDog : ByteArray}
    (hlotNew : lotNew = ⟨0⟩)
    (htabNew : tabNew = UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
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
          (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
            tabNew lotNew))
        evmDog) := by
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let digsAmtFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDigsAmt evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  have hlotCond :
      evalExpr? (config v) moveFrame evmMove
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [moveFrame] using
      clipperEvalTakeNoAdjustLotEqZero_true v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe tabNew lotNew hlotNew
  have hdigsAmt :
      ExecStmt (config v) moveFrame evmMove
        (.letDecl "digsAmt" (some uint256) (wrap256 (.binary .add (.var "tab") (.var "owe"))))
        (.ok digsAmtFrame evmMove) := by
    have hrhs :=
      clipperEvalTakeNoAdjustDigsAmtAtMoveRet v evmLoc evmRead evmVat evmMove I price
        slice owe0 owe tabNew lotNew htabNew howeTab
    simpa [moveFrame, digsAmtFrame, clipperTakeLocalsNoAdjustDigsAmt] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := moveFrame) (evm := evmMove) (name := "digsAmt")
        (ty := some uint256) (expr := wrap256 (.binary .add (.var "tab") (.var "owe")))
        (value := .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)) hrhs)
  have hdogOk :
      ExecBlock (config v) digsAmtFrame evmMove
        (checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
          [ilkExpr v, .var "digsAmt"] "_digsRet")
        (.ok digsRetFrame evmDog) := by
    have htarget :
        evalExpr? (config v) digsAmtFrame evmMove (.var "dog_") =
          .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeNoAdjustDogDigsTargetAtDigsAmt v evmLoc evmRead evmVat evmMove I
          price slice owe0 owe tabNew lotNew
    have hguard :
        evalExpr? (config v) digsAmtFrame evmMove
          (.binary .gt (.extCodeSize (.var "dog_")) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [digsAmtFrame] using
        clipperEvalTakeNoAdjustDogCodeGuardDigsAmt_true v evmLoc evmRead evmVat
          evmMove I price slice owe0 owe tabNew lotNew hdogCode
    have hargs :
        evalExprs? (config v) digsAmtFrame evmMove [ilkExpr v, .var "digsAmt"] =
          .ok [v.ilk, .int (Int.ofNat (clipperTakeSalesTabEVMWord evmRead I).toNat)] := by
      simpa [digsAmtFrame] using
        clipperEvalTakeNoAdjustDogDigsAmtArgs v evmLoc evmRead evmVat evmMove I price
          slice owe0 owe tabNew lotNew
    simpa [checkedExternalCallStmts, digsAmtFrame, digsRetFrame,
      clipperTakeLocalsNoAdjustDigsAmtRet, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
        (ExecBlock.consNormal
          (ExecStmt.externalCallSuccess htarget (by simp [evalExpr?, pure]) hargs hcallDog
            (clipperTakeDecodeDigsVoid v outDog))
          ExecBlock.nil))
  have hthen :
      ExecBlock (config v) moveFrame evmMove
        (wrappingAddInto "digsAmt" (.var "tab") (.var "owe") ++
          checkedExternalCallStmts (.var "dog_") "digs" (.intLit 0)
            [ilkExpr v, .var "digsAmt"] "_digsRet")
        (.ok digsRetFrame evmDog) := by
    simpa [wrappingAddInto, moveFrame, digsRetFrame] using
      (ExecBlock.consNormal hdigsAmt hdogOk)
  simpa [moveFrame, digsRetFrame] using
    ExecBlock.consNormal (ExecStmt.iteTrue hlotCond hthen) ExecBlock.nil

theorem clipperTakeLocalsNoAdjustDigsAmtRet_removeArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0
          owe tabNew lotNew))
      evmDog [.var "id"] =
        .ok [clipperYankArgValue I] := by
  have hgetId :
      (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0
        owe tabNew lotNew).get? "id" = some (clipperYankArgValue I) := by
    rw [clipperTakeLocalsNoAdjustDigsAmtRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsNoAdjustDigsAmt, store_get_ne _ _ (by decide),
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
  have hidEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0
            owe tabNew lotNew))
        evmDog (.var "id") = .ok (clipperYankArgValue I) := by
    simp only [evalExpr?]
    rw [hgetId]
    rfl
  exact evalExprs?_singleton hidEval

theorem clipperTakeLocalsNoAdjustDigsAmtRet_removeRet_locked
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) :
    ((clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
      tabNew lotNew).insert "_removeRet" .unit).get? "locked" = none := by
  simp [clipperTakeLocalsNoAdjustDigsAmtRet, clipperTakeLocalsNoAdjustDigsAmt,
    clipperTakeLocalsNoAdjustMoveRet, clipperTakeLocalsNoAdjustDogLoaded,
    clipperTakeLocalsNoAdjustFluxBuyerRet, clipperTakeLocalsNoAdjustLotAssigned,
    clipperTakeLocalsNoAdjustTabAssigned, clipperTakeLocalsNoAdjustLotNew,
    clipperTakeLocalsNoAdjustTabNew, clipperTakeLocalsOwe, clipperTakeLocalsOwe0,
    clipperTakeLocalsSlice, clipperTakeLocalsTab, clipperTakeLocalsLot,
    clipperTakeLocalsPrice, clipperTakeLocalsDone, clipperTakeLocalsSt,
    clipperTakeLocalsTic, clipperTakeLocalsUsr, clipperTakeStore]

theorem clipperEvalTakeLotEqZeroAtNoAdjustDigsAmtRet_true (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256)
    (hlotNew : lotNew = ⟨0⟩) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0
          owe tabNew lotNew))
      evmDog (.binary .eq (.var "lot") (.intLit 0)) =
        .ok (.bool true) := by
  subst lotNew
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsNoAdjustDigsAmtRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDigsAmt, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustMoveRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsNoAdjustLotAssigned, store_get_self]
  change evalBinaryOp? .eq (.int 0) (.int 0) = .ok (.bool true)
  unfold evalBinaryOp?
  rfl

theorem clipperTakeNoAdjustDogDigsOweZeroRemoveIdEqMoveSourceOk (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmMove evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe tabNew lotNew : UInt256) {outDog : ByteArray}
    {acc : Account}
    (hlotNew : lotNew = ⟨0⟩)
    (htabNew : tabNew = UInt256.sub (clipperTakeSalesTabEVMWord evmRead I) owe)
    (howeTab : owe.toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
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
        (true, evmDog, outDog) true)
    (hacc : evmDog.accountMap.find? evmDog.executionEnv.codeOwner = some acc)
    (hlen : Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      clipperYankArgWord I =
        Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let evmRemove := clipperYankDeleteSaleState (clipperYankRemovePopState evmDog lastIndex) I
    let frameRemoveRet : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0
            owe tabNew lotNew).insert "_removeRet" .unit }
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
      (.ok frameRemoveRet
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro lastIndex evmRemove frameRemoveRet
  let move :=
    Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
      (clipperYankActiveSlot lastIndex)
  let moveFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustMoveRet evmLoc evmRead evmVat I price slice owe0 owe
        tabNew lotNew)
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0 owe
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
      clipperTakeNoAdjustDogDigsOweZeroCallSuccessBlock v evmLoc evmRead evmVat
        evmMove evmDog I price slice owe0 owe tabNew lotNew hlotNew htabNew howeTab
        hdogCode hcallDog
  have hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmDog
        removeFunction.body
        (.returned { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          evmRemove none) := by
    simpa [lastIndex, move, evmRemove] using
      clipperYankRemoveIdEqMoveSource v evmDog I hacc hlen heq
  have hremove :
      ExecStmt (config v) digsRetFrame evmDog
        (.internalCall "_remove" [.var "id"] "_removeRet")
        (.ok frameRemoveRet evmRemove) := by
    simpa [resumeAfterInternalCall, digsRetFrame, frameRemoveRet] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := digsRetFrame)
        (evm := evmDog)
        (name := "_remove") (retVar := "_removeRet")
        (args := [.var "id"])
        (argVals := [clipperYankArgValue I])
        (callee := removeFunction)
        (locals := clipperYankRemoveStore I)
        (calleeSolm := { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move })
        (calleeEvm := evmRemove)
        (value := none)
        (clipperTakeLocalsNoAdjustDigsAmtRet_removeArgs v evmLoc evmRead evmVat evmDog
          I price slice owe0 owe tabNew lotNew)
        (clipperYankRemoveLookup v)
        (clipperYankRemoveBind I)
        hremoveBody)
  have hlotCond :
      evalExpr? (config v) digsRetFrame evmDog
        (.binary .eq (.var "lot") (.intLit 0)) = .ok (.bool true) := by
    simpa [digsRetFrame] using
      clipperEvalTakeLotEqZeroAtNoAdjustDigsAmtRet_true v evmLoc evmRead evmVat evmDog
        I price slice owe0 owe tabNew lotNew hlotNew
  have hremoveIte :
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
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteTrue hlotCond (ExecBlock.consNormal hremove ExecBlock.nil)
  have hzero :
      evalExpr? (config v) frameRemoveRet evmRemove (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, frameRemoveRet]
  have hassign :
      assignStorageRef? (config v) frameRemoveRet evmRemove
        .storage lockedRef (.int 0) =
        .ok (frameRemoveRet,
          Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [frameRemoveRet] using
      assign_clipperLocked v evmRemove
        ((clipperTakeLocalsNoAdjustDigsAmtRet evmLoc evmRead evmVat I price slice owe0
          owe tabNew lotNew).insert "_removeRet" .unit)
        (clipperTakeLocalsNoAdjustDigsAmtRet_removeRet_locked evmLoc evmRead evmVat I
          price slice owe0 owe tabNew lotNew)
        ⟨0⟩
  have hunlock :
      ExecStmt (config v) frameRemoveRet evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
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
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecBlock.consNormal hremoveIte (ExecBlock.consNormal hunlock ExecBlock.nil)
  simpa [moveFrame, digsRetFrame] using
    execBlockAppendOk hdog htail

end Benchmarks.Dss.Clipper
