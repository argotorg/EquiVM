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

abbrev clipperRedoIncentiveCond : Expr :=
  .binary .or (.binary .gt (.var "_tip") (.intLit 0))
    (.binary .gt (.var "_chip") (.intLit 0))

def clipperRedoIncentiveBody : List Stmt :=
  [ .letDecl "_chost" (some uint256) (.storage chostRef),
    .ite
      (.binary .ge (.var "tab") (.var "_chost"))
      (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
        [ .ite
            (.binary .ge (.var "lotFeed") (.var "_chost"))
            ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
              checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
              checkedExternalCallStmts vatExpr "suck" (.intLit 0)
                [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
            [] ])
      [] ]

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

abbrev clipperRedoTipSolmWord (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)

abbrev clipperRedoChipSolmWord (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
    (UInt256.ofNat (2 ^ 64 - 1))

abbrev clipperRedoLocalsTip (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew).insert "_tip"
    (.int (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat))

abbrev clipperRedoLocalsChip (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsTip evmLoc evmRead evmVals I price feedPrice topNew).insert "_chip"
    (.int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat))

theorem clipperRedoLocalsFeedPrice_get_buf (evmLoc evmRead : EVM.State)
    (I : ExecutionEnv) (price feedPrice : UInt256) :
    (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice).get? "buf" = none := by
  simp [clipperRedoLocalsFeedPrice, clipperRedoLocalsLot, clipperRedoLocalsTab,
    clipperRedoLocalsSt, clipperRedoLocalsTop, clipperRedoLocalsTic,
    clipperRedoLocalsUsr, clipperRedoStore]

theorem clipperEvalRedoRmulArgs (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice : UInt256) :
    evalExprs? config
      { contract := contract,
        locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice, immutables := immStore v }
      evm [.var "feedPrice", .storage bufRef] =
      .ok [.int (Int.ofNat feedPrice.toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)] := by
  have hfeed :
      evalExpr? config
        { contract := contract,
          locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice, immutables := immStore v }
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
    ExecStmt config
      { contract := contract,
        locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice, immutables := immStore v }
      evm (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "topNew")
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew, immutables := immStore v }
        evm) := by
  intro topNew
  simpa [resumeAfterInternalCall, clipperRedoLocalsTopNew] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract
        (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice) (immStore v))
      (evm := evm) (calleeEvm := evm)
      (name := "rmul") (retVar := "topNew")
      (args := [.var "feedPrice", .storage bufRef])
      (argVals := [.int (Int.ofNat feedPrice.toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)])
      (callee := rmulFunction)
      (locals := clipperUintBinaryLocals feedPrice
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
      (calleeSolm := Frame.mk contract
        (clipperWmulReturnLocals feedPrice
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
          (UInt256.mul feedPrice
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))) (immStore v))
      (value := some [.int (Int.ofNat topNew.toNat)])
      (clipperEvalRedoRmulArgs v evmLoc evmRead evm I price feedPrice)
      (clipperLookupRmulFunction)
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
    ExecStmt config
      { contract := contract,
        locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice, immutables := immStore v }
      evm (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "topNew") .reverted :=
  internalCallFunctionRevert
    (cfg := config)
    (caller := Frame.mk contract
      (clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice) (immStore v))
    (evm := evm) (name := "rmul") (retVar := "topNew")
    (args := [.var "feedPrice", .storage bufRef])
    (argVals := [.int (Int.ofNat feedPrice.toNat),
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)])
    (callee := rmulFunction)
    (locals := clipperUintBinaryLocals feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
    (clipperEvalRedoRmulArgs v evmLoc evmRead evm I price feedPrice)
    (clipperLookupRmulFunction)
    (clipperBindParamsRmul feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
    (clipperRmulFunctionReverts v evm feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) hover)

theorem clipperEvalRedoTopNewPositive (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) (hpos : 0 < topNew.toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew, immutables := immStore v }
      evm (.binary .gt (.var "topNew") (.intLit 0)) = .ok (.bool true) := by
  simpa [evalExpr?, clipperRedoLocalsTopNew, EvalResult.ofOption,
    EvalResult.bind, bind, evalBinaryOp?] using hpos

theorem clipperEvalRedoTopNewNotPositive (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) (hzero : topNew = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew, immutables := immStore v }
      evm (.binary .gt (.var "topNew") (.intLit 0)) = .ok (.bool false) := by
  subst topNew
  simp [evalExpr?, clipperRedoLocalsTopNew, EvalResult.ofOption,
    EvalResult.bind, bind, evalBinaryOp?]

theorem clipperRedoAssignSalesTop (v : ClipperImmutables)
    (evmLoc evmRead evm : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    assignStorageRef? config
      { contract := contract,
        locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew, immutables := immStore v }
      evm .storage (salesF (.var "id") "top") (.int (Int.ofNat topNew.toNat)) =
      .ok
        (Frame.mk contract
          (clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew) (immStore v),
          clipperRedoTopState evm I topNew) := by
  have hid :
      evalExpr? config
        { contract := contract,
          locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew, immutables := immStore v }
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
    (v : ClipperImmutables) (evmLoc evmRead evmStart evmFeed : EVM.State)
    (I : ExecutionEnv) (price feedPrice : UInt256)
    {result : ExecResult}
    (hgetFeed :
      ExecStmt config
        { contract := contract, locals := clipperRedoLocalsLot evmLoc evmRead I price, immutables := immStore v }
        evmStart (.internalCall "getFeedPrice" [] "feedPrice")
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice, immutables := immStore v }
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
      ExecBlock config
        { contract := contract,
          locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
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
                        checkedExternalCallStmts vatExpr "suck" (.intLit 0)
                          [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                      [] ])
                [] ]
            [],
          .assign .storage lockedRef (.intLit 0) ]
        result) :
    ExecBlock config
      { contract := contract, locals := clipperRedoLocalsLot evmLoc evmRead I price, immutables := immStore v }
      evmStart (clipperRedoAfterTicBody) result := by
  let buf := Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩
  let topNew := UInt256.div (UInt256.mul feedPrice buf) clipperRayWord
  let topFrame : Frame :=
    { contract := contract,
      locals := clipperRedoLocalsTopNew evmLoc evmRead I price feedPrice topNew, immutables := immStore v }
  let evmTop := clipperRedoTopState evmFeed I topNew
  let tipFrame : Frame :=
    { contract := contract,
      locals := clipperRedoLocalsTip evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
  let chipFrame : Frame :=
    { contract := contract,
      locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
  have hrmul :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsFeedPrice evmLoc evmRead I price feedPrice, immutables := immStore v }
        evmFeed (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "topNew")
        (.ok topFrame evmFeed) := by
    simpa [buf, topNew, topFrame] using
      clipperRedoRmulCallReturns v evmLoc evmRead evmFeed I price feedPrice hmul
  have hrequire :
      ExecStmt config topFrame evmFeed
        (.require (.binary .gt (.var "topNew") (.intLit 0)))
        (.ok topFrame evmFeed) := by
    exact ExecStmt.requireTrue (by
      simpa [buf, topNew, topFrame] using
        clipperEvalRedoTopNewPositive v evmLoc evmRead evmFeed I price feedPrice topNew
          (by simpa [buf, topNew] using htop))
  have htopValue :
      evalExpr? config topFrame evmFeed (.var "topNew") =
        .ok (.int (Int.ofNat topNew.toNat)) := by
    simp only [topFrame, clipperRedoLocalsTopNew, evalExpr?, store_get_self,
      EvalResult.ofOption]
  have htopAssign :
      ExecStmt config topFrame evmFeed
        (.assign .storage (salesF (.var "id") "top") (.var "topNew"))
        (.ok topFrame evmTop) := by
    exact ExecStmt.assign htopValue (by
      simpa [topFrame, evmTop] using
        clipperRedoAssignSalesTop v evmLoc evmRead evmFeed I price feedPrice topNew)
  have htip :
      ExecStmt config topFrame evmTop
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
      ExecStmt config tipFrame evmTop
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
      ExecBlock config chipFrame evmTop
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
                        checkedExternalCallStmts vatExpr "suck" (.intLit 0)
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
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.assign .storage lockedRef (.intLit 0))
      (.ok { contract := contract, locals := locals, immutables := immStore v }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  exact ExecStmt.assign (by simp [evalExpr?, pure])
    (assign_clipperLocked v evm locals hlocked ⟨0⟩)

theorem clipperEvalRedoVarTip
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "_tip") =
      .ok (.int (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsChip]
  rw [store_get_ne _ _ (by decide), clipperRedoLocalsTip, store_get_self]
  rfl

theorem clipperEvalRedoVarChip
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "_chip") =
      .ok (.int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsChip]
  rw [store_get_self]
  rfl

theorem clipperEvalRedoIncentiveInactive
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipSolmWord evmVals = ⟨0⟩)
    (hchip : clipperRedoChipSolmWord evmVals = ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0))) = .ok (.bool false) := by
  simp only [evalExpr?,
    clipperEvalRedoVarTip v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarChip v evmLoc evmRead evmVals evm I price feedPrice topNew,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [htip, hchip]
  decide

theorem clipperEvalRedoIncentiveActiveOfTip
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipSolmWord evmVals ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0))) = .ok (.bool true) := by
  have hpos : 0 < (clipperRedoTipSolmWord evmVals).toNat :=
    Nat.pos_of_ne_zero (fun h => htip (uint256_toNat_eq_zero h))
  simp only [evalExpr?,
    clipperEvalRedoVarTip v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarChip v evmLoc evmRead evmVals evm I price feedPrice topNew,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  simp [hpos]

theorem clipperEvalRedoIncentiveActiveOfChip
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipSolmWord evmVals = ⟨0⟩)
    (hchip : clipperRedoChipSolmWord evmVals ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0))) = .ok (.bool true) := by
  have hpos : 0 < (clipperRedoChipSolmWord evmVals).toNat :=
    Nat.pos_of_ne_zero (fun h => hchip (uint256_toNat_eq_zero h))
  simp only [evalExpr?,
    clipperEvalRedoVarTip v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarChip v evmLoc evmRead evmVals evm I price feedPrice topNew,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [htip]
  simp [hpos]

theorem clipperEvalRedoIncentiveActive
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hactive : clipperRedoTipSolmWord evmVals ≠ ⟨0⟩ ∨
      clipperRedoChipSolmWord evmVals ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0))) = .ok (.bool true) := by
  by_cases htip : clipperRedoTipSolmWord evmVals = ⟨0⟩
  · exact clipperEvalRedoIncentiveActiveOfChip v evmLoc evmRead evmVals evm I
      price feedPrice topNew htip
      (hactive.resolve_left (fun hne => hne htip))
  · exact clipperEvalRedoIncentiveActiveOfTip v evmLoc evmRead evmVals evm I
      price feedPrice topNew htip

theorem clipperRedoIncentiveInactiveTail
    (v : ClipperImmutables) (evmLoc evmRead evmTop : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htip : clipperRedoTipSolmWord evmTop = ⟨0⟩)
    (hchip : clipperRedoChipSolmWord evmTop = ⟨0⟩) :
    let locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmTop
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
                      checkedExternalCallStmts vatExpr "suck" (.intLit 0)
                        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                    [] ])
              [] ]
          [],
        .assign .storage lockedRef (.intLit 0) ]
      (.ok { contract := contract, locals := locals, immutables := immStore v }
        (Solm.EVM.storageStore evmTop evmTop.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro locals
  have hite :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evmTop
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
                      checkedExternalCallStmts vatExpr "suck" (.intLit 0)
                        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                    [] ])
              [] ]
          [])
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmTop) := by
    exact ExecStmt.iteFalse
      (by
        simpa [locals] using
          (clipperEvalRedoIncentiveInactive v evmLoc evmRead evmTop evmTop I
            price feedPrice topNew htip hchip))
      ExecBlock.nil
  have hunlock := clipperRedoUnlock v evmTop locals
    (by simpa [locals] using
      (clipperRedoLocalsChip_get_locked evmLoc evmRead evmTop I
        price feedPrice topNew))
  exact ExecBlock.consNormal hite <|
      ExecBlock.consNormal hunlock ExecBlock.nil

theorem clipperRedoIncentiveTailReverts
    (frame : Frame) (evm : EVM.State)
    (hcond : evalExpr? config frame evm clipperRedoIncentiveCond = .ok (.bool true))
    (hbody : ExecBlock config frame evm (clipperRedoIncentiveBody) .reverted) :
    ExecBlock config frame evm
      [ .ite clipperRedoIncentiveCond (clipperRedoIncentiveBody) [],
        .assign .storage lockedRef (.intLit 0) ] .reverted := by
  exact ExecBlock.consRevert (ExecStmt.iteTrue hcond hbody)

theorem clipperRedoIncentiveTailOk
    (v : ClipperImmutables) (frame : Frame) (afterLocals : Store)
    (evm evmAfter : EVM.State)
    (hcond : evalExpr? config frame evm clipperRedoIncentiveCond = .ok (.bool true))
    (hbody : ExecBlock config frame evm (clipperRedoIncentiveBody)
      (.ok { contract := contract, locals := afterLocals, immutables := immStore v } evmAfter))
    (hlocked : afterLocals.get? "locked" = none) :
    ExecBlock config frame evm
      [ .ite clipperRedoIncentiveCond (clipperRedoIncentiveBody) [],
        .assign .storage lockedRef (.intLit 0) ]
      (.ok { contract := contract, locals := afterLocals, immutables := immStore v }
        (Solm.EVM.storageStore evmAfter evmAfter.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hbody) <|
    ExecBlock.consNormal (clipperRedoUnlock v evmAfter afterLocals hlocked) ExecBlock.nil

abbrev clipperRedoChostWordSource (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩

abbrev clipperRedoLocalsChost (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew).insert "_chost"
    (.int (Int.ofNat (clipperRedoChostWordSource evmVals).toNat))

theorem clipperRedoLocalsChost_get_locked
    (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    (clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew).get? "locked" =
      none := by
  simp [clipperRedoLocalsChost, clipperRedoLocalsChip, clipperRedoLocalsTip,
    clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice, clipperRedoLocalsLot,
    clipperRedoLocalsTab, clipperRedoLocalsSt, clipperRedoLocalsTop,
    clipperRedoLocalsTic, clipperRedoLocalsUsr, clipperRedoStore]

theorem clipperRedoLetChost
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    ExecStmt config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (.letDecl "_chost" (some uint256) (.storage chostRef))
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
        evmVals) := by
  exact ExecStmt.letDecl (by
    simpa [clipperRedoLocalsChost] using
      (clipperEvalChost v evmVals
        (clipperRedoLocalsChip evmLoc evmRead evmVals I price feedPrice topNew)
        (by
          simp [clipperRedoLocalsChip, clipperRedoLocalsTip,
            clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice,
            clipperRedoLocalsLot, clipperRedoLocalsTab, clipperRedoLocalsSt,
            clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr,
            clipperRedoStore])))

theorem clipperEvalRedoVarTabAtChost
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "tab") =
      .ok (.int (Int.ofNat (clipperRedoSalesTabEVMWord evmRead I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew).get? "tab") = _
  unfold clipperRedoLocalsChost clipperRedoLocalsChip clipperRedoLocalsTip
    clipperRedoLocalsTopNew clipperRedoLocalsFeedPrice clipperRedoLocalsLot
    clipperRedoLocalsTab
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoVarChost
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "_chost") =
      .ok (.int (Int.ofNat (clipperRedoChostWordSource evmVals).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsChost, store_get_self]
  rfl

theorem clipperEvalRedoTabGeChostFalse
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hlt : (clipperRedoSalesTabEVMWord evmRead I).toNat <
      (clipperRedoChostWordSource evmVals).toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.binary .ge (.var "tab") (.var "_chost")) = .ok (.bool false) := by
  simp only [evalExpr?,
    clipperEvalRedoVarTabAtChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    EvalResult.bind, bind, evalBinaryOp?]
  simpa using hlt

theorem clipperEvalRedoTabGeChostTrue
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hle : (clipperRedoChostWordSource evmVals).toNat ≤
      (clipperRedoSalesTabEVMWord evmRead I).toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.binary .ge (.var "tab") (.var "_chost")) = .ok (.bool true) := by
  simp only [evalExpr?,
    clipperEvalRedoVarTabAtChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    EvalResult.bind, bind, evalBinaryOp?]
  simpa using hle

theorem clipperRedoActiveTabBelowBody
    (v : ClipperImmutables) (evmLoc evmRead evmTop : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hlt : (clipperRedoSalesTabEVMWord evmRead I).toNat <
      (clipperRedoChostWordSource evmTop).toNat) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
      evmTop (clipperRedoIncentiveBody)
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop) := by
  have hlet := clipperRedoLetChost v evmLoc evmRead evmTop I price feedPrice topNew
  have hite :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop
        (.ite (.binary .ge (.var "tab") (.var "_chost"))
          (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
            [ .ite
                (.binary .ge (.var "lotFeed") (.var "_chost"))
                ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                  checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                  checkedExternalCallStmts vatExpr "suck" (.intLit 0)
                    [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                [] ])
          [])
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
          evmTop) := by
    exact ExecStmt.iteFalse
      (clipperEvalRedoTabGeChostFalse v evmLoc evmRead evmTop evmTop I
        price feedPrice topNew hlt)
      ExecBlock.nil
  simpa [clipperRedoIncentiveBody] using
    (ExecBlock.consNormal hlet (ExecBlock.consNormal hite ExecBlock.nil))

abbrev clipperRedoLotWordSource (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  clipperRedoSalesLotEVMWord evm I

abbrev clipperRedoLocalsLotFeed (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew).insert "lotFeed"
    (.int (Int.ofNat (UInt256.mul (clipperRedoLotWordSource evmRead I) feedPrice).toNat))

theorem clipperRedoLocalsLotFeed_get_locked
    (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    (clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew).get?
      "locked" = none := by
  simp [clipperRedoLocalsLotFeed, clipperRedoLocalsChost, clipperRedoLocalsChip,
    clipperRedoLocalsTip, clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice,
    clipperRedoLocalsLot, clipperRedoLocalsTab, clipperRedoLocalsSt,
    clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr,
    clipperRedoStore]

theorem clipperEvalRedoVarLotAtChost
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "lot") =
      .ok (.int (Int.ofNat (clipperRedoLotWordSource evmRead I).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsChost, clipperRedoLocalsChip,
    clipperRedoLocalsTip, clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice,
    clipperRedoLocalsLot]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoVarFeedPriceAtChost
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "feedPrice") = .ok (.int (Int.ofNat feedPrice.toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsChost, clipperRedoLocalsChip,
    clipperRedoLocalsTip, clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoLotFeedMulOk
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hmul : (clipperRedoLotWordSource evmRead I).toNat * feedPrice.toNat < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (mul256 (.var "lot") (.var "feedPrice")) =
      .ok (.int (Int.ofNat
        (UInt256.mul (clipperRedoLotWordSource evmRead I) feedPrice).toNat)) := by
  let lot := clipperRedoLotWordSource evmRead I
  have hlt : ¬ Int.ofNat (lot.toNat * feedPrice.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size, lot] using hmul))
  have hword : (UInt256.mul lot feedPrice).toNat = lot.toNat * feedPrice.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt]
    simpa [lot] using hmul
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind,
    clipperEvalRedoVarLotAtChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarFeedPriceAtChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    evalBinaryOp?, uint256Int, lot, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem clipperEvalRedoLotFeedMulRevert
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hover : UInt256.size ≤
      (clipperRedoLotWordSource evmRead I).toNat * feedPrice.toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (mul256 (.var "lot") (.var "feedPrice")) = .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind,
    clipperEvalRedoVarLotAtChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarFeedPriceAtChost v evmLoc evmRead evmVals evm I price feedPrice topNew,
    evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem clipperEvalRedoLotFeedRequire
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hmul : (clipperRedoLotWordSource evmRead I).toNat * feedPrice.toNat < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm
      (.binary .or
        (.binary .eq (.var "feedPrice") (.intLit 0))
        (.binary .eq (.binary .div (.var "lotFeed") (.var "feedPrice"))
          (.var "lot"))) = .ok (.bool true) := by
  let lot := clipperRedoLotWordSource evmRead I
  have hfeed :
      evalExpr? config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evm (.var "feedPrice") = .ok (.int (Int.ofNat feedPrice.toNat)) := by
    simp only [evalExpr?, clipperRedoLocalsLotFeed, clipperRedoLocalsChost,
      clipperRedoLocalsChip, clipperRedoLocalsTip, clipperRedoLocalsTopNew,
      clipperRedoLocalsFeedPrice]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hlotFeed :
      evalExpr? config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evm (.var "lotFeed") =
          .ok (.int (Int.ofNat (UInt256.mul lot feedPrice).toNat)) := by
    simp only [evalExpr?, clipperRedoLocalsLotFeed, store_get_self, lot]
    rfl
  have hlot :
      evalExpr? config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evm (.var "lot") = .ok (.int (Int.ofNat lot.toNat)) := by
    simp only [evalExpr?, clipperRedoLocalsLotFeed, clipperRedoLocalsChost,
      clipperRedoLocalsChip, clipperRedoLocalsTip, clipperRedoLocalsTopNew,
      clipperRedoLocalsFeedPrice, clipperRedoLocalsLot]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    rfl
  by_cases hy : feedPrice = ⟨0⟩
  · have hyNat : feedPrice.toNat = 0 := by rw [hy]; rfl
    have hleft :
        evalExpr? config
          { contract := contract,
            locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
              price feedPrice topNew, immutables := immStore v }
          evm (.binary .eq (.var "feedPrice") (.intLit 0)) = .ok (.bool true) := by
      simp [evalExpr?, hfeed, EvalResult.bind, bind, evalBinaryOp?, hyNat]
    simp [evalExpr?, hleft, EvalResult.bind, bind, pure]
  · have hcancel := Reasoning.Theory.clipperMulDiv_cancel
      (x := feedPrice) (y := lot) (by simpa [eq_comm] using hy)
      (by simpa [lot, Nat.mul_comm] using hmul)
    have hnat := congrArg UInt256.toNat hcancel
    rw [udiv_toNat, u256_mul_comm feedPrice lot] at hnat
    have hdiv :
        Int.ofNat (UInt256.mul lot feedPrice).toNat / Int.ofNat feedPrice.toNat =
          Int.ofNat lot.toNat :=
      (Int.ofNat_ediv_ofNat
        (a := (UInt256.mul lot feedPrice).toNat) (b := feedPrice.toNat)).trans
        (congrArg Int.ofNat hnat)
    have hyInt : ¬ Int.ofNat feedPrice.toNat = 0 := by
      intro hzero
      exact hy (uint256_toNat_eq_zero (Int.ofNat.inj hzero))
    have hyNat : ¬ feedPrice.toNat = 0 := by
      intro hzero
      exact hy (uint256_toNat_eq_zero hzero)
    have hleft :
        evalExpr? config
          { contract := contract,
            locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
              price feedPrice topNew, immutables := immStore v }
          evm (.binary .eq (.var "feedPrice") (.intLit 0)) = .ok (.bool false) := by
      simp [evalExpr?, hfeed, EvalResult.bind, bind, evalBinaryOp?, hyNat]
    have hright :
        evalExpr? config
          { contract := contract,
            locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
              price feedPrice topNew, immutables := immStore v }
          evm
          (.binary .eq (.binary .div (.var "lotFeed") (.var "feedPrice"))
            (.var "lot")) = .ok (.bool true) := by
      simp only [evalExpr?, hlotFeed, hfeed, hlot, EvalResult.bind, bind, evalBinaryOp?]
      rw [if_neg hyInt, hdiv]
      simp
    simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

theorem clipperRedoLotFeedSuccessBlock
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hmul : (clipperRedoLotWordSource evmRead I).toNat * feedPrice.toNat < UInt256.size) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice"))
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
        evmVals) := by
  have hlet :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
        evmVals
        (.letDecl "lotFeed" (some uint256) (mul256 (.var "lot") (.var "feedPrice")))
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
              price feedPrice topNew, immutables := immStore v }
          evmVals) :=
    ExecStmt.letDecl
      (clipperEvalRedoLotFeedMulOk v evmLoc evmRead evmVals evmVals I
        price feedPrice topNew hmul)
  have hreq :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
        evmVals
        (.require
          (.binary .or
            (.binary .eq (.var "feedPrice") (.intLit 0))
            (.binary .eq (.binary .div (.var "lotFeed") (.var "feedPrice"))
              (.var "lot"))))
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
              price feedPrice topNew, immutables := immStore v }
          evmVals) :=
    ExecStmt.requireTrue
      (clipperEvalRedoLotFeedRequire v evmLoc evmRead evmVals evmVals I
        price feedPrice topNew hmul)
  simpa [checkedMulUintInto, clipperRedoLocalsLotFeed] using
    (ExecBlock.consNormal hlet (ExecBlock.consNormal hreq ExecBlock.nil))

theorem clipperRedoActiveLotFeedOverflowBody
    (v : ClipperImmutables) (evmLoc evmRead evmTop : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htab : (clipperRedoChostWordSource evmTop).toNat ≤
      (clipperRedoSalesTabEVMWord evmRead I).toNat)
    (hover : UInt256.size ≤
      (clipperRedoLotWordSource evmRead I).toNat * feedPrice.toNat) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
      evmTop (clipperRedoIncentiveBody) .reverted := by
  have hlet := clipperRedoLetChost v evmLoc evmRead evmTop I price feedPrice topNew
  have hmul :
      ExecBlock config
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop
        (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
          [ .ite
              (.binary .ge (.var "lotFeed") (.var "_chost"))
              ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                checkedExternalCallStmts vatExpr "suck" (.intLit 0)
                  [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
              [] ]) .reverted := by
    have hmul0 :
        ExecBlock config
          { contract := contract,
            locals := clipperRedoLocalsChost evmLoc evmRead evmTop I
              price feedPrice topNew, immutables := immStore v }
          evmTop (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice"))
          .reverted := by
      simpa [checkedMulUintInto] using
        ExecBlock.consRevert (ExecStmt.letDeclRevert
          (clipperEvalRedoLotFeedMulRevert v evmLoc evmRead evmTop evmTop I
            price feedPrice topNew hover))
    exact execBlock_append_term hmul0 (by intro frame state h; cases h)
  have hite :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop
        (.ite (.binary .ge (.var "tab") (.var "_chost"))
          (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
            [ .ite
                (.binary .ge (.var "lotFeed") (.var "_chost"))
                ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
                  checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
                  checkedExternalCallStmts vatExpr "suck" (.intLit 0)
                    [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
                [] ])
          []) .reverted :=
    ExecStmt.iteTrue
      (clipperEvalRedoTabGeChostTrue v evmLoc evmRead evmTop evmTop I
        price feedPrice topNew htab) hmul
  simpa [clipperRedoIncentiveBody] using ExecBlock.consNormal hlet (ExecBlock.consRevert hite)

theorem clipperEvalRedoVarLotFeed
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "lotFeed") =
      .ok (.int (Int.ofNat
        (UInt256.mul (clipperRedoLotWordSource evmRead I) feedPrice).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsLotFeed, store_get_self]
  rfl

theorem clipperEvalRedoVarChostAtLotFeed
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "_chost") =
      .ok (.int (Int.ofNat (clipperRedoChostWordSource evmVals).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsLotFeed, clipperRedoLocalsChost]
  rw [store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoLotFeedGeChostFalse
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hlt : (UInt256.mul (clipperRedoLotWordSource evmRead I) feedPrice).toNat <
      (clipperRedoChostWordSource evmVals).toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.binary .ge (.var "lotFeed") (.var "_chost")) = .ok (.bool false) := by
  simp only [evalExpr?,
    clipperEvalRedoVarLotFeed v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarChostAtLotFeed v evmLoc evmRead evmVals evm I price feedPrice topNew,
    EvalResult.bind, bind, evalBinaryOp?]
  simpa using hlt

theorem clipperEvalRedoLotFeedGeChostTrue
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hle : (clipperRedoChostWordSource evmVals).toNat ≤
      (UInt256.mul (clipperRedoLotWordSource evmRead I) feedPrice).toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.binary .ge (.var "lotFeed") (.var "_chost")) = .ok (.bool true) := by
  simp only [evalExpr?,
    clipperEvalRedoVarLotFeed v evmLoc evmRead evmVals evm I price feedPrice topNew,
    clipperEvalRedoVarChostAtLotFeed v evmLoc evmRead evmVals evm I price feedPrice topNew,
    EvalResult.bind, bind, evalBinaryOp?]
  simpa using hle

abbrev clipperRedoPayoutStmts : List Stmt :=
  [ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
    checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
    checkedExternalCallStmts vatExpr "suck" (.intLit 0)
      [.storage vowRef, .var "kpr", .var "coin"] "_suckRet"

theorem clipperRedoActiveLotFeedBodyOfPayout
    (v : ClipperImmutables) (evmLoc evmRead evmTop : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    {result : ExecResult}
    (htab : (clipperRedoChostWordSource evmTop).toNat ≤
      (clipperRedoSalesTabEVMWord evmRead I).toNat)
    (hmul : (clipperRedoLotWordSource evmRead I).toNat * feedPrice.toNat < UInt256.size)
    (hlotFeed : (clipperRedoChostWordSource evmTop).toNat ≤
      (UInt256.mul (clipperRedoLotWordSource evmRead I) feedPrice).toNat)
    (hpayout :
      ExecBlock config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmTop I
            price feedPrice topNew, immutables := immStore v }
        evmTop (clipperRedoPayoutStmts) result) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
      evmTop (clipperRedoIncentiveBody) result := by
  have hlet := clipperRedoLetChost v evmLoc evmRead evmTop I price feedPrice topNew
  have hmulBlock :=
    clipperRedoLotFeedSuccessBlock v evmLoc evmRead evmTop I price feedPrice topNew hmul
  have hinner :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmTop I
            price feedPrice topNew, immutables := immStore v }
        evmTop
        (.ite (.binary .ge (.var "lotFeed") (.var "_chost"))
          (clipperRedoPayoutStmts) []) result :=
    ExecStmt.iteTrue
      (clipperEvalRedoLotFeedGeChostTrue v evmLoc evmRead evmTop evmTop I
        price feedPrice topNew hlotFeed) hpayout
  have houterBody :
      ExecBlock config
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop
        (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
          [.ite (.binary .ge (.var "lotFeed") (.var "_chost"))
            (clipperRedoPayoutStmts) []]) result := by
    exact execBlock_append hmulBlock <| by
      exact match result with
      | .ok frame state => ExecBlock.consNormal hinner ExecBlock.nil
      | .returned frame state values => ExecBlock.consReturn hinner
      | .reverted => ExecBlock.consRevert hinner
      | .break frame state => ExecBlock.consBreak hinner
      | .continue frame state => ExecBlock.consContinue hinner
  have houter :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop
        (.ite (.binary .ge (.var "tab") (.var "_chost"))
          (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
            [.ite (.binary .ge (.var "lotFeed") (.var "_chost"))
              (clipperRedoPayoutStmts) []]) []) result :=
    ExecStmt.iteTrue
      (clipperEvalRedoTabGeChostTrue v evmLoc evmRead evmTop evmTop I
        price feedPrice topNew htab) houterBody
  simpa [clipperRedoIncentiveBody, clipperRedoPayoutStmts] using
    (match result with
    | .ok frame state => ExecBlock.consNormal hlet (ExecBlock.consNormal houter ExecBlock.nil)
    | .returned frame state values => ExecBlock.consNormal hlet (ExecBlock.consReturn houter)
    | .reverted => ExecBlock.consNormal hlet (ExecBlock.consRevert houter)
    | .break frame state => ExecBlock.consNormal hlet (ExecBlock.consBreak houter)
    | .continue frame state => ExecBlock.consNormal hlet (ExecBlock.consContinue houter))

theorem clipperRedoActiveLotFeedBelowBody
    (v : ClipperImmutables) (evmLoc evmRead evmTop : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (htab : (clipperRedoChostWordSource evmTop).toNat ≤
      (clipperRedoSalesTabEVMWord evmRead I).toNat)
    (hmul : (clipperRedoLotWordSource evmRead I).toNat * feedPrice.toNat < UInt256.size)
    (hlt : (UInt256.mul (clipperRedoLotWordSource evmRead I) feedPrice).toNat <
      (clipperRedoChostWordSource evmTop).toNat) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsChip evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
      evmTop (clipperRedoIncentiveBody)
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop) := by
  have hlet := clipperRedoLetChost v evmLoc evmRead evmTop I price feedPrice topNew
  have hmulBlock :=
    clipperRedoLotFeedSuccessBlock v evmLoc evmRead evmTop I price feedPrice topNew hmul
  have hinner :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmTop I
            price feedPrice topNew, immutables := immStore v }
        evmTop
        (.ite (.binary .ge (.var "lotFeed") (.var "_chost"))
          (clipperRedoPayoutStmts) [])
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsLotFeed evmLoc evmRead evmTop I
              price feedPrice topNew, immutables := immStore v }
          evmTop) :=
    ExecStmt.iteFalse
      (clipperEvalRedoLotFeedGeChostFalse v evmLoc evmRead evmTop evmTop I
        price feedPrice topNew hlt) ExecBlock.nil
  have houterBody := execBlock_append hmulBlock
    (ExecBlock.consNormal hinner ExecBlock.nil)
  have houter :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsChost evmLoc evmRead evmTop I price feedPrice topNew, immutables := immStore v }
        evmTop
        (.ite (.binary .ge (.var "tab") (.var "_chost"))
          (checkedMulUintInto "lotFeed" (.var "lot") (.var "feedPrice") ++
            [.ite (.binary .ge (.var "lotFeed") (.var "_chost"))
              (clipperRedoPayoutStmts) []]) [])
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsLotFeed evmLoc evmRead evmTop I
              price feedPrice topNew, immutables := immStore v }
          evmTop) :=
    ExecStmt.iteTrue
      (clipperEvalRedoTabGeChostTrue v evmLoc evmRead evmTop evmTop I
        price feedPrice topNew htab) houterBody
  simpa [clipperRedoIncentiveBody, clipperRedoPayoutStmts] using
    ExecBlock.consNormal hlet (ExecBlock.consNormal houter ExecBlock.nil)

abbrev clipperRedoChipCoinWord (evmRead evmVals : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.div
    (UInt256.mul (clipperRedoSalesTabEVMWord evmRead I) (clipperRedoChipSolmWord evmVals))
    ⟨1000000000000000000⟩

abbrev clipperRedoLocalsChipCoin (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew).insert
    "chipCoin" (.int (Int.ofNat (clipperRedoChipCoinWord evmRead evmVals I).toNat))

theorem clipperRedoLocalsChipCoin_get_locked
    (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    (clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew).get?
      "locked" = none := by
  simp [clipperRedoLocalsChipCoin, clipperRedoLocalsLotFeed,
    clipperRedoLocalsChost, clipperRedoLocalsChip, clipperRedoLocalsTip,
    clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice, clipperRedoLocalsLot,
    clipperRedoLocalsTab, clipperRedoLocalsSt, clipperRedoLocalsTop,
    clipperRedoLocalsTic, clipperRedoLocalsUsr, clipperRedoStore]

theorem clipperEvalRedoVarTabAtLotFeed
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "tab") =
      .ok (.int (Int.ofNat (clipperRedoSalesTabEVMWord evmRead I).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsLotFeed, clipperRedoLocalsChost,
    clipperRedoLocalsChip, clipperRedoLocalsTip, clipperRedoLocalsTopNew,
    clipperRedoLocalsFeedPrice, clipperRedoLocalsLot, clipperRedoLocalsTab]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoVarChipAtLotFeed
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "_chip") =
      .ok (.int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsLotFeed, clipperRedoLocalsChost,
    clipperRedoLocalsChip]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoWmulArgs
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExprs? config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm [.var "tab", .var "_chip"] =
      .ok [.int (Int.ofNat (clipperRedoSalesTabEVMWord evmRead I).toNat),
        .int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat)] :=
  clipperEvalExprsUintBinary v evm
    (clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew)
    (clipperRedoSalesTabEVMWord evmRead I) (clipperRedoChipSolmWord evmVals)
    (clipperEvalRedoVarTabAtLotFeed v evmLoc evmRead evmVals evm I
      price feedPrice topNew)
    (clipperEvalRedoVarChipAtLotFeed v evmLoc evmRead evmVals evm I
      price feedPrice topNew)

theorem clipperRedoWmulCallReturns
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hmul : (clipperRedoSalesTabEVMWord evmRead I).toNat *
      (clipperRedoChipSolmWord evmVals).toNat < UInt256.size) :
    ExecStmt config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (.internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin")
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evmVals) := by
  let tab := clipperRedoSalesTabEVMWord evmRead I
  let chip := clipperRedoChipSolmWord evmVals
  have hargs :
      evalExprs? config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evmVals [.var "tab", .var "_chip"] =
        .ok [.int (Int.ofNat tab.toNat), .int (Int.ofNat chip.toNat)] := by
    simpa [tab, chip] using
      (clipperEvalRedoWmulArgs v evmLoc evmRead evmVals evmVals I
        price feedPrice topNew)
  simpa [resumeAfterInternalCall, clipperRedoLocalsChipCoin,
    clipperRedoChipCoinWord, tab, chip] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract
        (clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew) (immStore v))
      (evm := evmVals) (calleeEvm := evmVals)
      (name := "wmul") (retVar := "chipCoin")
      (args := [.var "tab", .var "_chip"])
      (argVals := [.int (Int.ofNat tab.toNat), .int (Int.ofNat chip.toNat)])
      (callee := wmulFunction) (locals := clipperUintBinaryLocals tab chip)
      (calleeSolm := Frame.mk contract
        (clipperWmulReturnLocals tab chip (UInt256.mul tab chip)) (immStore v))
      (value := some [.int (Int.ofNat
        (UInt256.div (UInt256.mul tab chip) ⟨1000000000000000000⟩).toNat)])
      hargs
      (clipperLookupWmulFunction) (clipperBindParamsWmul tab chip)
      (clipperWmulFunctionReturns v evmVals tab chip (by simpa [tab, chip] using hmul)))

theorem clipperRedoWmulCallReverts
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hover : UInt256.size ≤ (clipperRedoSalesTabEVMWord evmRead I).toNat *
      (clipperRedoChipSolmWord evmVals).toNat) :
    ExecStmt config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (.internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin") .reverted :=
  internalCallFunctionRevert
    (cfg := config)
    (caller := Frame.mk contract
      (clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew) (immStore v))
    (evm := evmVals) (name := "wmul") (retVar := "chipCoin")
    (args := [.var "tab", .var "_chip"])
    (argVals :=
      [.int (Int.ofNat (clipperRedoSalesTabEVMWord evmRead I).toNat),
        .int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat)])
    (callee := wmulFunction)
    (locals := clipperUintBinaryLocals (clipperRedoSalesTabEVMWord evmRead I)
      (clipperRedoChipSolmWord evmVals))
    (clipperEvalRedoWmulArgs v evmLoc evmRead evmVals evmVals I
      price feedPrice topNew)
    (clipperLookupWmulFunction)
    (clipperBindParamsWmul (clipperRedoSalesTabEVMWord evmRead I)
      (clipperRedoChipSolmWord evmVals))
    (clipperWmulFunctionReverts v evmVals (clipperRedoSalesTabEVMWord evmRead I)
      (clipperRedoChipSolmWord evmVals) hover)

theorem clipperRedoPayoutWmulOverflow
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hover : UInt256.size ≤ (clipperRedoSalesTabEVMWord evmRead I).toNat *
      (clipperRedoChipSolmWord evmVals).toNat) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (clipperRedoPayoutStmts) .reverted := by
  have hcall := clipperRedoWmulCallReverts v evmLoc evmRead evmVals I
    price feedPrice topNew hover
  have hfirst :
      ExecBlock config
        { contract := contract,
          locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evmVals [.internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin"]
        .reverted := ExecBlock.consRevert hcall
  have hwhole := execBlock_append_term
    (s2 := checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
      checkedExternalCallStmts vatExpr "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
    hfirst (by intro frame state h; cases h)
  simpa [clipperRedoPayoutStmts, List.append_assoc] using hwhole

theorem clipperRedoPayoutOfWmulSuccess
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) {result : ExecResult}
    (hmul : (clipperRedoSalesTabEVMWord evmRead I).toNat *
      (clipperRedoChipSolmWord evmVals).toNat < UInt256.size)
    (hafter :
      ExecBlock config
        { contract := contract,
          locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evmVals
        (checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
          checkedExternalCallStmts vatExpr "suck" (.intLit 0)
            [.storage vowRef, .var "kpr", .var "coin"] "_suckRet") result) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsLotFeed evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (clipperRedoPayoutStmts) result := by
  have hcall := clipperRedoWmulCallReturns v evmLoc evmRead evmVals I
    price feedPrice topNew hmul
  simpa [clipperRedoPayoutStmts] using ExecBlock.consNormal hcall hafter

abbrev clipperRedoCoinWord (evmRead evmVals : EVM.State) (I : ExecutionEnv) : UInt256 :=
  clipperRedoTipSolmWord evmVals + clipperRedoChipCoinWord evmRead evmVals I

abbrev clipperRedoLocalsCoin (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew).insert
    "coin" (.int (Int.ofNat (clipperRedoCoinWord evmRead evmVals I).toNat))

theorem clipperRedoLocalsCoin_get_locked
    (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew).get?
      "locked" = none := by
  simp [clipperRedoLocalsCoin, clipperRedoLocalsChipCoin,
    clipperRedoLocalsLotFeed, clipperRedoLocalsChost, clipperRedoLocalsChip,
    clipperRedoLocalsTip, clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice,
    clipperRedoLocalsLot, clipperRedoLocalsTab, clipperRedoLocalsSt,
    clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr,
    clipperRedoStore]

theorem clipperEvalRedoVarTipAtChipCoin
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "_tip") =
      .ok (.int (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsChipCoin, clipperRedoLocalsLotFeed,
    clipperRedoLocalsChost, clipperRedoLocalsChip, clipperRedoLocalsTip]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoVarChipCoin
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "chipCoin") =
      .ok (.int (Int.ofNat (clipperRedoChipCoinWord evmRead evmVals I).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsChipCoin, store_get_self]
  rfl

theorem clipperEvalRedoVarCoin
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "coin") =
      .ok (.int (Int.ofNat (clipperRedoCoinWord evmRead evmVals I).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsCoin, store_get_self]
  rfl

theorem clipperEvalRedoVarTipAtCoin
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "_tip") =
      .ok (.int (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat)) := by
  simp only [evalExpr?, clipperRedoLocalsCoin]
  unfold clipperRedoLocalsChipCoin clipperRedoLocalsLotFeed
    clipperRedoLocalsChost clipperRedoLocalsChip clipperRedoLocalsTip
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoAddOk
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hfit : (clipperRedoTipSolmWord evmVals).toNat +
      (clipperRedoChipCoinWord evmRead evmVals I).toNat < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (add256 (.var "_tip") (.var "chipCoin")) =
      .ok (.int (Int.ofNat (clipperRedoCoinWord evmRead evmVals I).toNat)) :=
  clipperEvalAdd256_ok v
    (clipperEvalRedoVarTipAtChipCoin v evmLoc evmRead evmVals evmVals I
      price feedPrice topNew)
    (clipperEvalRedoVarChipCoin v evmLoc evmRead evmVals evmVals I
      price feedPrice topNew)
    rfl hfit

theorem clipperEvalRedoAddRevert
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hover : UInt256.size ≤ (clipperRedoTipSolmWord evmVals).toNat +
      (clipperRedoChipCoinWord evmRead evmVals I).toNat) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (add256 (.var "_tip") (.var "chipCoin")) = .revert :=
  clipperEvalAdd256_revert v
    (clipperEvalRedoVarTipAtChipCoin v evmLoc evmRead evmVals evmVals I
      price feedPrice topNew)
    (clipperEvalRedoVarChipCoin v evmLoc evmRead evmVals evmVals I
      price feedPrice topNew)
    hover

theorem clipperEvalRedoAddRequire
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hfit : (clipperRedoTipSolmWord evmVals).toNat +
      (clipperRedoChipCoinWord evmRead evmVals I).toNat < UInt256.size) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (.binary .ge (.var "coin") (.var "_tip")) = .ok (.bool true) := by
  have hcoinNat :
      (clipperRedoCoinWord evmRead evmVals I).toNat =
        (clipperRedoTipSolmWord evmVals).toNat +
          (clipperRedoChipCoinWord evmRead evmVals I).toNat := by
    rw [clipperRedoCoinWord, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hle : (clipperRedoTipSolmWord evmVals).toNat ≤
      (clipperRedoCoinWord evmRead evmVals I).toNat := by
    rw [hcoinNat]
    omega
  simp only [evalExpr?,
    clipperEvalRedoVarCoin v evmLoc evmRead evmVals evmVals I price feedPrice topNew,
    clipperEvalRedoVarTipAtCoin v evmLoc evmRead evmVals evmVals I
      price feedPrice topNew,
    EvalResult.bind, bind, evalBinaryOp?]
  simpa using hle

theorem clipperRedoAddSuccessBlock
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hfit : (clipperRedoTipSolmWord evmVals).toNat +
      (clipperRedoChipCoinWord evmRead evmVals I).toNat < UInt256.size) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals (checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin"))
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
        evmVals) := by
  have hlet :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evmVals (.letDecl "coin" (some uint256) (add256 (.var "_tip") (.var "chipCoin")))
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I
              price feedPrice topNew, immutables := immStore v }
          evmVals) := ExecStmt.letDecl
      (clipperEvalRedoAddOk v evmLoc evmRead evmVals I price feedPrice topNew hfit)
  have hreq :
      ExecStmt config
        { contract := contract,
          locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
        evmVals (.require (.binary .ge (.var "coin") (.var "_tip")))
        (.ok
          { contract := contract,
            locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I
              price feedPrice topNew, immutables := immStore v }
          evmVals) := ExecStmt.requireTrue
      (clipperEvalRedoAddRequire v evmLoc evmRead evmVals I price feedPrice topNew hfit)
  simpa [checkedAddUintInto, clipperRedoLocalsCoin] using
    ExecBlock.consNormal hlet (ExecBlock.consNormal hreq ExecBlock.nil)

theorem clipperRedoAfterWmulAddOverflow
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hover : UInt256.size ≤ (clipperRedoTipSolmWord evmVals).toNat +
      (clipperRedoChipCoinWord evmRead evmVals I).toNat) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals
      (checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin") ++
        checkedExternalCallStmts vatExpr "suck" (.intLit 0)
          [.storage vowRef, .var "kpr", .var "coin"] "_suckRet") .reverted := by
  have hadd :
      ExecBlock config
        { contract := contract,
          locals := clipperRedoLocalsChipCoin evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evmVals (checkedAddUintInto "coin" (.var "_tip") (.var "chipCoin"))
        .reverted := by
    simpa [checkedAddUintInto] using ExecBlock.consRevert
      (ExecStmt.letDeclRevert
        (clipperEvalRedoAddRevert v evmLoc evmRead evmVals I
          price feedPrice topNew hover))
  exact execBlock_append_term hadd (by intro frame state h; cases h)

abbrev clipperRedoVowAddressSource (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      solcAddrMask).toNat

abbrev clipperRedoLocalsSuckRet (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) : Store :=
  (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew).insert
    "_suckRet" .unit

theorem clipperRedoLocalsCoin_get_vow
    (evmLoc evmRead evmVals : EVM.State) (I : ExecutionEnv)
    (price feedPrice topNew : UInt256) :
    (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew).get? "vow" =
      none := by
  simp [clipperRedoLocalsCoin, clipperRedoLocalsChipCoin,
    clipperRedoLocalsLotFeed, clipperRedoLocalsChost, clipperRedoLocalsChip,
    clipperRedoLocalsTip, clipperRedoLocalsTopNew, clipperRedoLocalsFeedPrice,
    clipperRedoLocalsLot, clipperRedoLocalsTab, clipperRedoLocalsSt,
    clipperRedoLocalsTop, clipperRedoLocalsTic, clipperRedoLocalsUsr,
    clipperRedoStore]

theorem clipperEvalRedoVarKprAtCoin
    (v : ClipperImmutables) (evmLoc evmRead evmVals evm : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evm (.var "kpr") = .ok (clipperRedoKprValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew).get? "kpr") = _
  unfold clipperRedoLocalsCoin clipperRedoLocalsChipCoin clipperRedoLocalsLotFeed
    clipperRedoLocalsChost clipperRedoLocalsChip clipperRedoLocalsTip
    clipperRedoLocalsTopNew clipperRedoLocalsFeedPrice clipperRedoLocalsLot
    clipperRedoLocalsTab clipperRedoLocalsSt clipperRedoLocalsTop
    clipperRedoLocalsTic clipperRedoLocalsUsr clipperRedoStore
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRedoSuckArgs
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) :
    evalExprs? config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals [.storage vowRef, .var "kpr", .var "coin"] =
      .ok
        [.address (clipperRedoVowAddressSource evmVals),
          clipperRedoKprValue I,
          .int (Int.ofNat (clipperRedoCoinWord evmRead evmVals I).toNat)] := by
  have hvow := clipperEvalVow v evmVals
    (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew)
    (clipperRedoLocalsCoin_get_vow evmLoc evmRead evmVals I price feedPrice topNew)
  have hkpr := clipperEvalRedoVarKprAtCoin v evmLoc evmRead evmVals evmVals I
    price feedPrice topNew
  have hcoin := clipperEvalRedoVarCoin v evmLoc evmRead evmVals evmVals I
    price feedPrice topNew
  simp only [evalExprs?, hvow, hkpr, hcoin, EvalResult.bind, bind, pure]

theorem clipperEvalRedoVatCodeGuardFalse
    (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?,
    EVM.Word.ofNat, hnoCode]

theorem clipperEvalRedoVatCodeGuardTrue
    (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?,
    EVM.Word.ofNat, hcode]

theorem clipperRedoDecodeSuckVoid (out : ByteArray) :
    config.externalABI.decode? "suck" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem clipperRedoSuckNoCodeSource
    (v : ClipperImmutables) (evmLoc evmRead evmVals : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256)
    (hnoCode :
      (UInt256.ofNat ((evmVals.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals
      (checkedExternalCallStmts vatExpr "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet") .reverted := by
  simpa [checkedExternalCallStmts] using checkedExternalCallNoCode
    (cfg := config) (C := contract) (evm := evmVals)
    (locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew)
    (receiver := vatExpr) (retVar := "_suckRet") (name := "suck")
    (sendVal := 0) (args := [.storage vowRef, .var "kpr", .var "coin"])
    (perm := true)
    (clipperEvalRedoVatCodeGuardFalse v evmVals
      (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew) hnoCode)

theorem clipperRedoSuckCallFailureSource
    (v : ClipperImmutables) (evmLoc evmRead evmVals evmAfter : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) (out : ByteArray)
    (hcode :
      0 < (UInt256.ofNat ((evmVals.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evmVals (EVM.address v.vat) "suck" 0
      [.address (clipperRedoVowAddressSource evmVals), clipperRedoKprValue I,
        .int (Int.ofNat (clipperRedoCoinWord evmRead evmVals I).toNat)]
      (false, evmAfter, out) true) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals
      (checkedExternalCallStmts vatExpr "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet") .reverted := by
  simpa [checkedExternalCallStmts] using checkedExternalCallFailure
    (clipperEvalRedoVatCodeGuardTrue v evmVals
      (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew) hcode)
    (clipperEvalVat v evmVals
      (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew))
    (clipperEvalRedoSuckArgs v evmLoc evmRead evmVals I price feedPrice topNew)
    hcall

theorem clipperRedoSuckCallSuccessSource
    (v : ClipperImmutables) (evmLoc evmRead evmVals evmAfter : EVM.State)
    (I : ExecutionEnv) (price feedPrice topNew : UInt256) (out : ByteArray)
    (hcode :
      0 < (UInt256.ofNat ((evmVals.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evmVals (EVM.address v.vat) "suck" 0
      [.address (clipperRedoVowAddressSource evmVals), clipperRedoKprValue I,
        .int (Int.ofNat (clipperRedoCoinWord evmRead evmVals I).toNat)]
      (true, evmAfter, out) true) :
    ExecBlock config
      { contract := contract,
        locals := clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew, immutables := immStore v }
      evmVals
      (checkedExternalCallStmts vatExpr "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
      (.ok
        { contract := contract,
          locals := clipperRedoLocalsSuckRet evmLoc evmRead evmVals I
            price feedPrice topNew, immutables := immStore v }
        evmAfter) := by
  simpa [checkedExternalCallStmts, clipperRedoLocalsSuckRet] using checkedExternalCallSuccess
    (clipperEvalRedoVatCodeGuardTrue v evmVals
      (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew) hcode)
    (clipperEvalVat v evmVals
      (clipperRedoLocalsCoin evmLoc evmRead evmVals I price feedPrice topNew))
    (clipperEvalRedoSuckArgs v evmLoc evmRead evmVals I price feedPrice topNew)
    hcall (clipperRedoDecodeSuckVoid out)

theorem clipperRedoDoneTrueSourceRevertsOfAfterTic
    {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt config { contract := contract, locals := clipperRedoLocalsTop evmLock I, immutables := immStore v }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract, locals := clipperRedoLocalsSt evmLock I true price, immutables := immStore v }
          evmPrice))
    (hafter :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecBlock config
        { contract := contract, locals := clipperRedoLocalsLot evmLock evmPrice I price, immutables := immStore v }
        (clipperRedoPostTicState evmPrice I) (clipperRedoAfterTicBody) .reverted) :
    let locals := clipperRedoStore I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals redoTransition.body .reverted (immStore v) := by
  intro locals evm0
  have hblock := clipperRedoDoneTrueSourcePrefix
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus hafter
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert
    (by simpa [locals, evm0] using hblock)

theorem clipperRedoDoneTrueSourceOkOfAfterTic
    {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    {finalFrame : Frame} {evmFinal : EVM.State}
    (hstatus :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt config { contract := contract, locals := clipperRedoLocalsTop evmLock I, immutables := immStore v }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract, locals := clipperRedoLocalsSt evmLock I true price, immutables := immStore v }
          evmPrice))
    (hafter :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecBlock config
        { contract := contract, locals := clipperRedoLocalsLot evmLock evmPrice I price, immutables := immStore v }
        (clipperRedoPostTicState evmPrice I) (clipperRedoAfterTicBody)
        (.ok finalFrame evmFinal)) :
    let locals := clipperRedoStore I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals redoTransition.body
      (.returned finalFrame evmFinal none) (immStore v) := by
  intro locals evm0
  have hblock := clipperRedoDoneTrueSourcePrefix
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (evmPrice := evmPrice) v hwv hlocked hstopped husr price hstatus hafter
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockOK
    (by simpa [locals, evm0] using hblock)

end Benchmarks.Dss.Clipper
