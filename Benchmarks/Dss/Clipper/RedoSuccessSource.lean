import Benchmarks.Dss.Clipper.RedoDoneSource
import Benchmarks.Dss.Clipper.GetFeedPriceSuccess
import Benchmarks.Dss.Clipper.Buf
import Benchmarks.Dss.Clipper.Tip
import Benchmarks.Dss.Clipper.Chip
import Benchmarks.Dss.Clipper.Chost
import Benchmarks.Dss.Clipper.Vat
import Benchmarks.Dss.Clipper.Vow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

abbrev clipperRedoLocalsFeedPrice (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price feedPrice : UInt256) : Store :=
  (clipperRedoLocalsLot evmLoc evmRead I price).insert "feedPrice"
    (.int (Int.ofNat feedPrice.toNat))

abbrev clipperRedoLocalsTopNew (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice).insert "topNew"
    (.int (Int.ofNat topNew.toNat))

def clipperRedoTopState (evm : EVM.State) (I : ExecutionEnv) (topNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperRedoSalesTopSlot I) topNew

abbrev clipperRedoTipWord (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)

abbrev clipperRedoChipWord (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
    (UInt256.ofNat (2 ^ 64 - 1))

abbrev clipperRedoLocalsTip (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew).insert "_tip"
    (.int (Int.ofNat (clipperRedoTipWord evmVals).toNat))

abbrev clipperRedoLocalsChip (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsTip evmLoc evmRead evmVals I price feedPrice topNew).insert "_chip"
    (.int (Int.ofNat (clipperRedoChipWord evmVals).toNat))

theorem clipperRedoLocalsFeedPrice_get_buf (evmLoc evmRead : EVM.State)
    (I : ExecutionEnv) (price feedPrice : UInt256) :
    (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice).get? "buf" = none := by
  simp [clipperRedoLocalsFeedPrice, clipperRedoLocalsLot, clipperRedoLocalsTab,
    clipperRedoLocalsSt, clipperRedoLocalsTop, clipperRedoLocalsTic,
    clipperRedoLocalsUsr, clipperRedoStore]

theorem clipperEvalRedoRmulArgs (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice : UInt256) :
    evalExprs? (config v)
      { contract := contract v,
        locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice }
      evm [.var "feedPrice", .storage bufRef] =
      .ok [.int (Int.ofNat feedPrice.toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)] := by
  have hfeed :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice }
        evm (.var "feedPrice") = .ok (.int (Int.ofNat feedPrice.toNat)) := by
    simp only [evalExpr?, clipperRedoLocalsFeedPrice, store_get_self,
      EvalResult.ofOption]
  have hbuf := clipperEvalBuf v evm
    (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice)
    (clipperRedoLocalsFeedPrice_get_buf evmLoc evmRead I price feedPrice)
  simp only [evalExprs?, hfeed, hbuf, EvalResult.bind, bind, pure]

theorem clipperRedoRmulCallReturns (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice : UInt256)
    (hmul : feedPrice.toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat < UInt256.size) :
    let topNew := UInt256.div
      (UInt256.mul feedPrice
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)) clipperRayWord
    ExecStmt (config v)
      { contract := contract v,
        locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice }
      evm (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "topNew")
      (.ok
        { contract := contract v,
          locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew }
        evm) := by
  intro topNew
  simpa [resumeAfterInternalCall, clipperRedoLocalsTopNew] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := Frame.mk (contract v)
        (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice))
      (evm := evm) (calleeEvm := evm)
      (name := "rmul") (retVar := "topNew")
      (args := [.var "feedPrice", .storage bufRef])
      (argVals := [.int (Int.ofNat feedPrice.toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)])
      (callee := rmulFunction)
      (locals := clipperUintBinaryLocals feedPrice
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
      (calleeSolm := Frame.mk (contract v)
        (clipperWmulReturnLocals feedPrice
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
          (UInt256.mul feedPrice
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))))
      (value := some [.int (Int.ofNat topNew.toNat)])
      (clipperEvalRedoRmulArgs v evmLoc evmRead evm I price feedPrice)
      (clipperLookupRmulFunction v)
      (clipperBindParamsRmul feedPrice
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
      (by
        exact clipperRmulFunctionReturns v evm feedPrice
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) hmul))

theorem clipperRedoRmulCallReverts (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice : UInt256)
    (hover : UInt256.size ≤ feedPrice.toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecStmt (config v)
      { contract := contract v,
        locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice }
      evm (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "topNew") .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := Frame.mk (contract v)
      (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice))
    (evm := evm) (name := "rmul") (retVar := "topNew")
    (args := [.var "feedPrice", .storage bufRef])
    (argVals := [.int (Int.ofNat feedPrice.toNat),
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)])
    (callee := rmulFunction)
    (locals := clipperUintBinaryLocals feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
    (clipperEvalRedoRmulArgs v evmLoc evmRead evm I price feedPrice)
    (clipperLookupRmulFunction v)
    (clipperBindParamsRmul feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
    (clipperRmulFunctionReverts v evm feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) hover)

theorem clipperEvalRedoTopNewPositive (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) (hpos : 0 < topNew.toNat) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew }
      evm (.binary .gt (.var "topNew") (.intLit 0)) = .ok (.bool true) := by
  simpa [evalExpr?, clipperRedoLocalsTopNew, EvalResult.ofOption,
    EvalResult.bind, bind, evalBinaryOp?] using hpos

theorem clipperEvalRedoTopNewNotPositive (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) (hzero : topNew = ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew }
      evm (.binary .gt (.var "topNew") (.intLit 0)) = .ok (.bool false) := by
  subst topNew
  simp [evalExpr?, clipperRedoLocalsTopNew, EvalResult.ofOption,
    EvalResult.bind, bind, evalBinaryOp?]

theorem clipperRedoAssignSalesTop (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    assignStorageRef? (config v)
      { contract := contract v,
        locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew }
      evm .storage (salesF (.var "id") "top") (.int (Int.ofNat topNew.toNat)) =
      .ok
        (Frame.mk (contract v)
          (clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew),
          clipperRedoTopState evm I topNew) := by
  have hid :
      evalExpr? (config v)
        { contract := contract v,
          locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew }
        evm (.var "id") = .ok (clipperRedoIdValue I) := by
    have hget :
        (clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew).get? "id" =
          some (clipperRedoIdValue I) := by
      unfold clipperRedoLocalsTopNew clipperRedoLocalsFeedPrice
        clipperRedoLocalsLot clipperRedoLocalsTab clipperRedoLocalsSt
        clipperRedoLocalsTop clipperRedoLocalsTic clipperRedoLocalsUsr clipperRedoStore
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide)]
      rw [store_get_self]
    rw [evalExpr?]
    change EvalResult.ofOption .unboundVariable
      ((clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew).get? "id") = _
    rw [hget]
    rfl
  apply assignStorageRef_storage_scalar
    (er := clipperRedoSalesTopRef I) (ty := uint256St)
    (loc := wordLoc (clipperRedoSalesTopSlot I))
  · simp [salesF, clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice,
      clipperRedoLocalsLot, clipperRedoLocalsTab, clipperRedoLocalsSt,
      clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr,
      clipperRedoStore]
  · simp [clipperRedoSalesTopRef, clipperRedoIdKey,
      salesF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hid,
      valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind,
      clipperRedoIdValue]
  · simp [clipperRedoIdKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperRedoTopState, clipperRedoSalesTopSlot, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperRedoSalesTopSlot I) topNew

theorem clipperRedoAfterTicSuccessPrefix
    (v : ClipperImmutables) (evmLoc evmRead evmFeed : EVM.State)
    (I : ExecutionEnv) (price feedPrice : UInt256)
    {result : ExecResult}
    (hgetFeed :
      ExecStmt (config v)
        { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
        evmRead (.internalCall "getFeedPrice" [] "feedPrice")
        (.ok
          { contract := contract v,
            locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice }
          evmFeed))
    (hmul : feedPrice.toNat *
      (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩).toNat <
        UInt256.size)
    (htop : 0 < (UInt256.div
      (UInt256.mul feedPrice
        (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩))
      clipperRayWord).toNat)
    (hafter :
      let topNew := UInt256.div
        (UInt256.mul feedPrice
          (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩))
        clipperRayWord
      let evmTop := clipperRedoTopState evmFeed I topNew
      ExecBlock (config v)
        { contract := contract v,
          locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew }
        evmTop
        [ .ite
            (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
              (.binary .gt (.var "_chip") (.intLit 0)))
            [ .letDecl "_chost" (some uint256) (.storage chostRef),
              .ite
                (.binary .ge (.var "tab") (.var "_chost"))
                (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
                  [ .ite
                      (.binary .ge (.var "lotFeed") (.var "_chost"))
                      ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                        checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                        checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
                          [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                      [] ])
                [] ]
            [],
          .assign .storage lockedRef (.intLit 0) ]
        result) :
    ExecBlock (config v)
      { contract := contract v, locals := clipperRedoLocalsLot evmLoc evmRead I price }
      evmRead (clipperRedoAfterTicBody v) result := by
  let buf := Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩
  let topNew := UInt256.div (UInt256.mul feedPrice buf) clipperRayWord
  let topFrame : Frame :=
    { contract := contract v,
      locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew }
  let evmTop := clipperRedoTopState evmFeed I topNew
  let tipFrame : Frame :=
    { contract := contract v,
      locals := clipperRedoLocalsTip evmLoc evmRead evmTop I price feedPrice topNew }
  let chipFrame : Frame :=
    { contract := contract v,
      locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew }
  have hrmul :
      ExecStmt (config v)
        { contract := contract v,
          locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice }
        evmFeed (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "topNew")
        (.ok topFrame evmFeed) := by
    simpa [buf, topNew, topFrame] using
      clipperRedoRmulCallReturns v evmLoc evmRead evmFeed I price feedPrice hmul
  have hrequire :
      ExecStmt (config v) topFrame evmFeed
        (.require (.binary .gt (.var "topNew") (.intLit 0)))
        (.ok topFrame evmFeed) := by
    exact ExecStmt.requireTrue (by
      simpa [buf, topNew, topFrame] using
        clipperEvalRedoTopNewPositive v evmLoc evmRead evmFeed I price feedPrice topNew
          (by simpa [buf, topNew] using htop))
  have htopValue :
      evalExpr? (config v) topFrame evmFeed (.var "topNew") =
        .ok (.int (Int.ofNat topNew.toNat)) := by
    simp only [topFrame, clipperRedoLocalsTopNew, evalExpr?, store_get_self,
      EvalResult.ofOption]
  have htopAssign :
      ExecStmt (config v) topFrame evmFeed
        (.assign .storage (salesF (.var "id") "top") (.var "topNew"))
        (.ok topFrame evmTop) := by
    exact ExecStmt.assign htopValue (by
      simpa [topFrame, evmTop] using
        clipperRedoAssignSalesTop v evmLoc evmRead evmFeed I price feedPrice topNew)
  have htip :
      ExecStmt (config v) topFrame evmTop
        (.letDecl "_tip" (some uint256) (.storage tipRef))
        (.ok tipFrame evmTop) := by
    exact ExecStmt.letDecl (by
      simpa [topFrame, tipFrame, clipperRedoLocalsTip] using
        clipperEvalTip v evmTop
          (clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew)
          (by
            simp [clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice,
              clipperRedoLocalsLot, clipperRedoLocalsTab, clipperRedoLocalsSt,
              clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr,
              clipperRedoStore]))
  have hchip :
      ExecStmt (config v) tipFrame evmTop
        (.letDecl "_chip" (some uint256) (.storage chipRef))
        (.ok chipFrame evmTop) := by
    exact ExecStmt.letDecl (by
      simpa [tipFrame, chipFrame, clipperRedoLocalsChip] using
        clipperEvalChip v evmTop
          (clipperRedoLocalsTip evmLoc evmRead evmTop I price feedPrice topNew)
          (by
            simp [clipperRedoLocalsTip, clipperRedoLocalsTopNew,
              clipperRedoLocalsFeedPrice, clipperRedoLocalsLot,
              clipperRedoLocalsTab, clipperRedoLocalsSt, clipperRedoLocalsTop,
              clipperRedoLocalsTic, clipperRedoLocalsUsr, clipperRedoStore]))
  have hafter' :
      ExecBlock (config v) chipFrame evmTop
        [ .ite
            (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
              (.binary .gt (.var "_chip") (.intLit 0)))
            [ .letDecl "_chost" (some uint256) (.storage chostRef),
              .ite
                (.binary .ge (.var "tab") (.var "_chost"))
                (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
                  [ .ite
                      (.binary .ge (.var "lotFeed") (.var "_chost"))
                      ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                        checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                        checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
                          [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                      [] ])
                [] ]
            [],
          .assign .storage lockedRef (.intLit 0) ] result := by
    simpa [buf, topNew, evmTop, chipFrame] using hafter
  simpa [clipperRedoAfterTicBody, topFrame, tipFrame, chipFrame] using
    (ExecBlock.consNormal hgetFeed <|
      ExecBlock.consNormal hrmul <|
        ExecBlock.consNormal hrequire <|
          ExecBlock.consNormal htopAssign <|
            ExecBlock.consNormal htip <|
              ExecBlock.consNormal hchip hafter')

theorem clipperRedoLocalsChip_get_locked
    (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    (clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew).get? "locked" =
      none := by
  simp [clipperRedoLocalsChip, clipperRedoLocalsTip, clipperRedoLocalsTopNew,
    clipperRedoLocalsFeedPrice, clipperRedoLocalsLot, clipperRedoLocalsTab,
    clipperRedoLocalsSt, clipperRedoLocalsTop, clipperRedoLocalsTic,
    clipperRedoLocalsUsr, clipperRedoStore]

theorem clipperRedoUnlock
    (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hlocked : locals.get? "locked" = none) :
    ExecStmt (config v) { contract := contract v, locals := locals } evm
      (.assign .storage lockedRef (.intLit 0))
      (.ok { contract := contract v, locals := locals }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  exact ExecStmt.assign (by simp [evalExpr?, pure])
    (assign_clipperLocked v evm locals hlocked ⟨0⟩)

theorem clipperEvalRedoIncentiveInactive
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipWord evmVals = ⟨0⟩)
    (hchip : clipperRedoChipWord evmVals = ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew }
      evm
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0))) = .ok (.bool false) := by
  rw [htip, hchip]
  simp [evalExpr?, clipperRedoLocalsChip, clipperRedoLocalsTip,
    EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?]

theorem clipperEvalRedoIncentiveActiveOfTip
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipWord evmVals ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew }
      evm
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0))) = .ok (.bool true) := by
  have hpos : 0 < (clipperRedoTipWord evmVals).toNat :=
    Nat.pos_of_ne_zero (fun h => htip (uint256_toNat_eq_zero h))
  simpa [evalExpr?, clipperRedoLocalsChip, clipperRedoLocalsTip,
    EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?] using hpos

theorem clipperEvalRedoIncentiveActiveOfChip
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipWord evmVals = ⟨0⟩)
    (hchip : clipperRedoChipWord evmVals ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew }
      evm
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0))) = .ok (.bool true) := by
  have hpos : 0 < (clipperRedoChipWord evmVals).toNat :=
    Nat.pos_of_ne_zero (fun h => hchip (uint256_toNat_eq_zero h))
  rw [htip]
  simpa [evalExpr?, clipperRedoLocalsChip, clipperRedoLocalsTip,
    EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?] using hpos

theorem clipperRedoIncentiveInactiveTail
    (v : ClipperImmutables) (evmLoc evmRead evmTop : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipWord evmTop = ⟨0⟩)
    (hchip : clipperRedoChipWord evmTop = ⟨0⟩) :
    let locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew
    ExecBlock (config v) { contract := contract v, locals := locals } evmTop
      [ .ite
          (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
            (.binary .gt (.var "_chip") (.intLit 0)))
          [ .letDecl "_chost" (some uint256) (.storage chostRef),
            .ite
              (.binary .ge (.var "tab") (.var "_chost"))
              (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
                [ .ite
                    (.binary .ge (.var "lotFeed") (.var "_chost"))
                    ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                      checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                      checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
                        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                    [] ])
              [] ]
          [],
        .assign .storage lockedRef (.intLit 0) ]
      (.ok { contract := contract v, locals := locals }
        (Solm.EVM.storageStore evmTop evmTop.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro locals
  have hite :
      ExecStmt (config v) { contract := contract v, locals := locals } evmTop
        (.ite
          (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
            (.binary .gt (.var "_chip") (.intLit 0)))
          [ .letDecl "_chost" (some uint256) (.storage chostRef),
            .ite
              (.binary .ge (.var "tab") (.var "_chost"))
              (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
                [ .ite
                    (.binary .ge (.var "lotFeed") (.var "_chost"))
                    ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                      checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                      checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
                        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                    [] ])
              [] ]
          [])
        (.ok { contract := contract v, locals := locals } evmTop) := by
    exact ExecStmt.iteFalse
      (by simpa [locals] using
        clipperEvalRedoIncentiveInactive v evmLoc evmRead evmTop evmTop I
          price feedPrice topNew htip hchip)
      ExecBlock.nil
  exact ExecBlock.consNormal hite <|
    ExecBlock.consNormal
      (by simpa [locals] using
        clipperRedoUnlock v evmTop locals
          (by simpa [locals] using
            clipperRedoLocalsChip_get_locked evmLoc evmRead evmTop I
              price feedPrice topNew))
      ExecBlock.nil

end Benchmarks.Dss.Clipper
