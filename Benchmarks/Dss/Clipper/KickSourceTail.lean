import Benchmarks.Dss.Clipper.KickSourcePrefix
import Benchmarks.Dss.Clipper.GetFeedPriceSuccess
import Benchmarks.Dss.Clipper.RedoSuccessSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

/-! Source-side `kick` after `sales[id]` has been initialized. -/

abbrev clipperKickLocalsFeedPrice (evmLock : EVM.State) (I : ExecutionEnv)
    (feedPrice : UInt256) : Store :=
  (clipperKickLocalsActivePos evmLock I).insert "feedPrice"
    (.int (Int.ofNat feedPrice.toNat))

abbrev clipperKickLocalsTop (evmLock : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsFeedPrice evmLock I feedPrice).insert "top"
    (.int (Int.ofNat top.toNat))

def clipperKickSourceTopState (evmLock evm : EVM.State)
    (top : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (clipperKickSourceSalesBaseSlot evmLock + ⟨4⟩) top

abbrev clipperKickLocalsTip (evmLock evmVals : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsTop evmLock I feedPrice top).insert "_tip"
    (.int (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat))

abbrev clipperKickLocalsChip (evmLock evmVals : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsTip evmLock evmVals I feedPrice top).insert "_chip"
    (.int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat))

abbrev clipperKickLocalsCoinZero (evmLock evmVals : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) : Store :=
  (clipperKickLocalsChip evmLock evmVals I feedPrice top).insert "coin" (.int 0)

abbrev clipperKickIncentiveCond : Expr :=
  .binary .or (.binary .gt (.var "_tip") (.intLit 0))
    (.binary .gt (.var "_chip") (.intLit 0))

def clipperKickIncentiveBody (v : ClipperImmutables) : List Stmt :=
  [ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
    checkedAddUintInto "coinNew" (.var "_tip") (.var "chipCoin") ++
    [ .assign .localVar (varRef "coin") (.var "coinNew") ] ++
    checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
      [.storage vowRef, .var "kpr", .var "coin"] "_suckRet"

theorem clipperKickLocalsFeedPrice_get_buf (evmLock : EVM.State)
    (I : ExecutionEnv) (feedPrice : UInt256) :
    (clipperKickLocalsFeedPrice evmLock I feedPrice).get? "buf" = none := by
  simp [clipperKickLocalsFeedPrice, clipperKickLocalsActivePos,
    clipperKickLocalsId, clipperKickStore]

theorem clipperEvalKickRmulArgs (v : ClipperImmutables)
    (evmLock evm : EVM.State) (I : ExecutionEnv) (feedPrice : UInt256) :
    evalExprs? (config v)
      { contract := contract v, locals := clipperKickLocalsFeedPrice evmLock I feedPrice }
      evm [.var "feedPrice", .storage bufRef] =
      .ok [.int (Int.ofNat feedPrice.toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)] := by
  have hfeed : evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsFeedPrice evmLock I feedPrice }
      evm (.var "feedPrice") = .ok (.int (Int.ofNat feedPrice.toNat)) := by
    simp only [evalExpr?, clipperKickLocalsFeedPrice, store_get_self,
      EvalResult.ofOption]
  have hbuf := clipperEvalBuf v evm (clipperKickLocalsFeedPrice evmLock I feedPrice)
    (clipperKickLocalsFeedPrice_get_buf evmLock I feedPrice)
  simp only [evalExprs?, hfeed, hbuf, EvalResult.bind, bind, pure]

theorem clipperKickRmulCallReturns (v : ClipperImmutables)
    (evmLock evm : EVM.State) (I : ExecutionEnv) (feedPrice : UInt256)
    (hmul : feedPrice.toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat < UInt256.size) :
    let top := UInt256.div
      (UInt256.mul feedPrice
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)) clipperRayWord
    ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsFeedPrice evmLock I feedPrice }
      evm (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "top")
      (.ok (Frame.mk (contract v) (clipperKickLocalsTop evmLock I feedPrice top)) evm) := by
  intro top
  simpa [resumeAfterInternalCall, clipperKickLocalsTop] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := Frame.mk (contract v) (clipperKickLocalsFeedPrice evmLock I feedPrice))
      (evm := evm) (calleeEvm := evm) (name := "rmul") (retVar := "top")
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
      (value := some [.int (Int.ofNat top.toNat)])
      (clipperEvalKickRmulArgs v evmLock evm I feedPrice)
      (clipperLookupRmulFunction v)
      (clipperBindParamsRmul feedPrice
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
      (clipperRmulFunctionReturns v evm feedPrice
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) hmul))

theorem clipperKickRmulCallReverts (v : ClipperImmutables)
    (evmLock evm : EVM.State) (I : ExecutionEnv) (feedPrice : UInt256)
    (hover : UInt256.size ≤ feedPrice.toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsFeedPrice evmLock I feedPrice }
      evm (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "top") .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := Frame.mk (contract v) (clipperKickLocalsFeedPrice evmLock I feedPrice))
    (evm := evm) (name := "rmul") (retVar := "top")
    (args := [.var "feedPrice", .storage bufRef])
    (argVals := [.int (Int.ofNat feedPrice.toNat),
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)])
    (callee := rmulFunction)
    (locals := clipperUintBinaryLocals feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
    (clipperEvalKickRmulArgs v evmLock evm I feedPrice)
    (clipperLookupRmulFunction v)
    (clipperBindParamsRmul feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩))
    (clipperRmulFunctionReverts v evm feedPrice
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) hover)

theorem clipperEvalKickTopPositive (v : ClipperImmutables)
    (evmLock evm : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hpos : 0 < top.toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsTop evmLock I feedPrice top }
      evm (.binary .gt (.var "top") (.intLit 0)) = .ok (.bool true) := by
  simpa [evalExpr?, clipperKickLocalsTop, EvalResult.ofOption,
    EvalResult.bind, bind, evalBinaryOp?] using hpos

theorem clipperEvalKickTopZero (v : ClipperImmutables)
    (evmLock evm : EVM.State) (I : ExecutionEnv) (feedPrice : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsTop evmLock I feedPrice ⟨0⟩ }
      evm (.binary .gt (.var "top") (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, clipperKickLocalsTop, EvalResult.ofOption,
    EvalResult.bind, bind, evalBinaryOp?]

theorem clipperKickAssignSalesTop (v : ClipperImmutables)
    (evmLock evm : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256) :
    assignStorageRef? (config v)
      { contract := contract v, locals := clipperKickLocalsTop evmLock I feedPrice top }
      evm .storage (salesF (.var "id") "top") (.int (Int.ofNat top.toNat)) =
      .ok (Frame.mk (contract v) (clipperKickLocalsTop evmLock I feedPrice top),
        clipperKickSourceTopState evmLock evm top) := by
  have hid : evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsTop evmLock I feedPrice top }
      evm (.var "id") =
      .ok (.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsTop, clipperKickLocalsFeedPrice]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      clipperKickLocalsActivePos, store_get_ne _ _ (by decide),
      clipperKickLocalsId, store_get_self]
    rfl
  apply assignStorageRef_storage_scalar
    (er := clipperKickSourceSalesRef evmLock "top") (ty := uint256St)
    (loc := wordLoc (clipperKickSourceSalesBaseSlot evmLock + ⟨4⟩))
  · simp [salesF, clipperKickLocalsTop, clipperKickLocalsFeedPrice,
      clipperKickLocalsActivePos_get_sales]
  · simp [salesF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hid,
      clipperKickSourceSalesRef, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
      SaleStructTy, uint256St]
  · rfl
  · simpa [clipperKickSourceTopState, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperKickSourceSalesBaseSlot evmLock + ⟨4⟩) top

theorem clipperKickLocalsTop_get_tip (evmLock : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256) :
    (clipperKickLocalsTop evmLock I feedPrice top).get? "tip" = none := by
  simp [clipperKickLocalsTop, clipperKickLocalsFeedPrice,
    clipperKickLocalsActivePos, clipperKickLocalsId, clipperKickStore]

theorem clipperKickLocalsTip_get_chip (evmLock evmVals : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) :
    (clipperKickLocalsTip evmLock evmVals I feedPrice top).get? "chip" = none := by
  simp [clipperKickLocalsTip, clipperKickLocalsTop, clipperKickLocalsFeedPrice,
    clipperKickLocalsActivePos, clipperKickLocalsId, clipperKickStore]

theorem clipperEvalKickIncentiveInactive (v : ClipperImmutables)
    (evmLock evmVals evm : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (htip : clipperRedoTipSolmWord evmVals = ⟨0⟩)
    (hchip : clipperRedoChipSolmWord evmVals = ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmVals I feedPrice top }
      evm clipperKickIncentiveCond = .ok (.bool false) := by
  have hTip : evalExpr? (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmVals I feedPrice top }
      evm (.var "_tip") =
      .ok (.int (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinZero, clipperKickLocalsChip]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      clipperKickLocalsTip, store_get_self]
    rfl
  have hChip : evalExpr? (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmVals I feedPrice top }
      evm (.var "_chip") =
      .ok (.int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinZero]
    rw [store_get_ne _ _ (by decide), clipperKickLocalsChip, store_get_self]
    rfl
  simp only [clipperKickIncentiveCond, evalExpr?, hTip, hChip,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [htip, hchip]
  decide

theorem clipperEvalKickIncentiveActive (v : ClipperImmutables)
    (evmLock evmVals evm : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hactive : clipperRedoTipSolmWord evmVals ≠ ⟨0⟩ ∨
      clipperRedoChipSolmWord evmVals ≠ ⟨0⟩) :
    evalExpr? (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmVals I feedPrice top }
      evm clipperKickIncentiveCond = .ok (.bool true) := by
  have hTip : evalExpr? (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmVals I feedPrice top }
      evm (.var "_tip") =
      .ok (.int (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinZero, clipperKickLocalsChip]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      clipperKickLocalsTip, store_get_self]
    rfl
  have hChip : evalExpr? (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmVals I feedPrice top }
      evm (.var "_chip") =
      .ok (.int (Int.ofNat (clipperRedoChipSolmWord evmVals).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsCoinZero]
    rw [store_get_ne _ _ (by decide), clipperKickLocalsChip, store_get_self]
    rfl
  rcases hactive with htip | hchip
  · have hpos : 0 < (clipperRedoTipSolmWord evmVals).toNat :=
      Nat.pos_of_ne_zero (fun h => htip (uint256_toNat_eq_zero h))
    simp only [clipperKickIncentiveCond, evalExpr?, hTip, hChip,
      EvalResult.bind, bind, pure, evalBinaryOp?]
    simp [hpos]
  · have hpos : 0 < (clipperRedoChipSolmWord evmVals).toNat :=
      Nat.pos_of_ne_zero (fun h => hchip (uint256_toNat_eq_zero h))
    have hposInt : (0 : Int) < Int.ofNat (clipperRedoChipSolmWord evmVals).toNat := by
      simpa using hpos
    simp only [clipperKickIncentiveCond, evalExpr?, hTip, hChip,
      EvalResult.bind, bind, pure, evalBinaryOp?]
    rw [decide_eq_true hposInt]
    cases decide (Int.ofNat (clipperRedoTipSolmWord evmVals).toNat > 0) <;> rfl

theorem clipperKickLocalsCoinZero_get_locked (evmLock evmVals : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) :
    (clipperKickLocalsCoinZero evmLock evmVals I feedPrice top).get? "locked" = none := by
  simp [clipperKickLocalsCoinZero, clipperKickLocalsChip, clipperKickLocalsTip,
    clipperKickLocalsTop, clipperKickLocalsFeedPrice, clipperKickLocalsActivePos,
    clipperKickLocalsId, clipperKickStore]

theorem clipperKickUnlockReturn (v : ClipperImmutables)
    (evmLock evmVals evm : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (locals : Store)
    (hlocked : locals.get? "locked" = none)
    (hid : locals.get? "id" =
      some (.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat))) :
    ExecBlock (config v) { contract := contract v, locals := locals } evm
      [.assign .storage lockedRef (.intLit 0), .return [.var "id"]]
      (.returned { contract := contract v, locals := locals }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
        (some [.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)])) := by
  have hunlock := clipperRedoUnlock v evm locals hlocked
  have hret : evalExprs? (config v) { contract := contract v, locals := locals }
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
      [.var "id"] =
      .ok [.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)] := by
    simp only [evalExprs?, evalExpr?, hid, EvalResult.ofOption, EvalResult.bind,
      bind, pure]
  exact ExecBlock.consNormal hunlock (ExecBlock.consReturn (ExecStmt.return hret))

theorem clipperKickIncentiveInactiveTail (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (htip : clipperRedoTipSolmWord evmTop = ⟨0⟩)
    (hchip : clipperRedoChipSolmWord evmTop = ⟨0⟩) :
    let locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top
    ExecBlock (config v) { contract := contract v, locals := locals } evmTop
      [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
        .assign .storage lockedRef (.intLit 0), .return [.var "id"] ]
      (.returned { contract := contract v, locals := locals }
        (Solm.EVM.storageStore evmTop evmTop.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
        (some [.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)])) := by
  intro locals
  have hite : ExecStmt (config v) { contract := contract v, locals := locals } evmTop
      (.ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [])
      (.ok { contract := contract v, locals := locals } evmTop) :=
    ExecStmt.iteFalse
      (by simpa [locals] using
        clipperEvalKickIncentiveInactive v evmLock evmTop evmTop I feedPrice top htip hchip)
      ExecBlock.nil
  have htail := clipperKickUnlockReturn v evmLock evmTop evmTop I feedPrice top locals
    (by simpa [locals] using
      clipperKickLocalsCoinZero_get_locked evmLock evmTop I feedPrice top)
    (by
      simp only [locals, clipperKickLocalsCoinZero]
      rw [store_get_ne _ _ (by decide), clipperKickLocalsChip,
        store_get_ne _ _ (by decide), clipperKickLocalsTip,
        store_get_ne _ _ (by decide), clipperKickLocalsTop,
        store_get_ne _ _ (by decide), clipperKickLocalsFeedPrice,
        store_get_ne _ _ (by decide), clipperKickLocalsActivePos,
        store_get_ne _ _ (by decide), clipperKickLocalsId, store_get_self])
  exact ExecBlock.consNormal hite htail

theorem clipperKickAfterInitializationGetFeedReverts
    (v : ClipperImmutables) (evmLock evm : EVM.State) (I : ExecutionEnv)
    (hgetFeed : ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (.internalCall "getFeedPrice" [] "feedPrice") .reverted) :
    ExecBlock (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (clipperKickAfterInitializationBody v) .reverted := by
  simpa [clipperKickAfterInitializationBody] using ExecBlock.consRevert hgetFeed

theorem clipperKickAfterInitializationRmulReverts
    (v : ClipperImmutables) (evmLock evm evmFeed : EVM.State)
    (I : ExecutionEnv) (feedPrice : UInt256)
    (hgetFeed : ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (.internalCall "getFeedPrice" [] "feedPrice")
      (.ok (Frame.mk (contract v) (clipperKickLocalsFeedPrice evmLock I feedPrice))
        evmFeed))
    (hover : UInt256.size ≤ feedPrice.toNat *
      (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecBlock (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (clipperKickAfterInitializationBody v) .reverted := by
  have hrmul := clipperKickRmulCallReverts v evmLock evmFeed I feedPrice hover
  simpa [clipperKickAfterInitializationBody] using
    ExecBlock.consNormal hgetFeed (ExecBlock.consRevert hrmul)

theorem clipperKickAfterInitializationTopZeroReverts
    (v : ClipperImmutables) (evmLock evm evmFeed : EVM.State)
    (I : ExecutionEnv) (feedPrice : UInt256)
    (hgetFeed : ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (.internalCall "getFeedPrice" [] "feedPrice")
      (.ok (Frame.mk (contract v) (clipperKickLocalsFeedPrice evmLock I feedPrice))
        evmFeed))
    (hmul : feedPrice.toNat *
      (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩).toNat <
        UInt256.size)
    (htop : UInt256.div
      (UInt256.mul feedPrice
        (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩))
      clipperRayWord = ⟨0⟩) :
    ExecBlock (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (clipperKickAfterInitializationBody v) .reverted := by
  let top := UInt256.div
    (UInt256.mul feedPrice
      (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩)) clipperRayWord
  have hrmul : ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsFeedPrice evmLock I feedPrice }
      evmFeed (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "top")
      (.ok (Frame.mk (contract v) (clipperKickLocalsTop evmLock I feedPrice top))
        evmFeed) := by
    simpa [top] using clipperKickRmulCallReturns v evmLock evmFeed I feedPrice hmul
  have hzero : top = ⟨0⟩ := by simpa [top] using htop
  have hreq : ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsTop evmLock I feedPrice top }
      evmFeed (.require (.binary .gt (.var "top") (.intLit 0))) .reverted :=
    ExecStmt.requireFalse (by
      rw [hzero]
      exact clipperEvalKickTopZero v evmLock evmFeed I feedPrice)
  simpa [clipperKickAfterInitializationBody] using
    ExecBlock.consNormal hgetFeed (ExecBlock.consNormal hrmul (ExecBlock.consRevert hreq))

theorem clipperKickAfterInitializationSuccessPrefix
    (v : ClipperImmutables) (evmLock evm evmFeed : EVM.State)
    (I : ExecutionEnv) (feedPrice : UInt256)
    (hgetFeed : ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (.internalCall "getFeedPrice" [] "feedPrice")
      (.ok (Frame.mk (contract v) (clipperKickLocalsFeedPrice evmLock I feedPrice))
        evmFeed))
    (hmul : feedPrice.toNat *
      (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩).toNat <
        UInt256.size)
    (htop : 0 < (UInt256.div
      (UInt256.mul feedPrice
        (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩))
      clipperRayWord).toNat)
    {result : ExecResult}
    (hafter :
      let top := UInt256.div
        (UInt256.mul feedPrice
          (Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩))
        clipperRayWord
      let evmTop := clipperKickSourceTopState evmLock evmFeed top
      ExecBlock (config v)
        { contract := contract v,
          locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
        evmTop
        [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
          .assign .storage lockedRef (.intLit 0), .return [.var "id"] ] result) :
    ExecBlock (config v)
      { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
      evm (clipperKickAfterInitializationBody v) result := by
  let buf := Solm.EVM.storageLoad evmFeed evmFeed.executionEnv.codeOwner ⟨5⟩
  let top := UInt256.div (UInt256.mul feedPrice buf) clipperRayWord
  let topFrame : Frame :=
    { contract := contract v, locals := clipperKickLocalsTop evmLock I feedPrice top }
  let evmTop := clipperKickSourceTopState evmLock evmFeed top
  let tipFrame : Frame :=
    { contract := contract v,
      locals := clipperKickLocalsTip evmLock evmTop I feedPrice top }
  let chipFrame : Frame :=
    { contract := contract v,
      locals := clipperKickLocalsChip evmLock evmTop I feedPrice top }
  let coinFrame : Frame :=
    { contract := contract v,
      locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
  have hrmul : ExecStmt (config v)
      { contract := contract v, locals := clipperKickLocalsFeedPrice evmLock I feedPrice }
      evmFeed (.internalCall "rmul" [.var "feedPrice", .storage bufRef] "top")
      (.ok topFrame evmFeed) := by
    simpa [buf, top, topFrame] using
      clipperKickRmulCallReturns v evmLock evmFeed I feedPrice hmul
  have hrequire : ExecStmt (config v) topFrame evmFeed
      (.require (.binary .gt (.var "top") (.intLit 0)))
      (.ok topFrame evmFeed) :=
    ExecStmt.requireTrue (by
      simpa [buf, top, topFrame] using
        clipperEvalKickTopPositive v evmLock evmFeed I feedPrice top
          (by simpa [buf, top] using htop))
  have htopValue : evalExpr? (config v) topFrame evmFeed (.var "top") =
      .ok (.int (Int.ofNat top.toNat)) := by
    simp only [topFrame, evalExpr?, clipperKickLocalsTop, store_get_self,
      EvalResult.ofOption]
  have htopAssign : ExecStmt (config v) topFrame evmFeed
      (.assign .storage (salesF (.var "id") "top") (.var "top"))
      (.ok topFrame evmTop) :=
    ExecStmt.assign htopValue (by
      simpa [topFrame, evmTop] using
        clipperKickAssignSalesTop v evmLock evmFeed I feedPrice top)
  have htip : ExecStmt (config v) topFrame evmTop
      (.letDecl "_tip" (some uint256) (.storage tipRef))
      (.ok tipFrame evmTop) := by
    exact ExecStmt.letDecl (by
      simpa [topFrame, tipFrame, clipperKickLocalsTip] using
        clipperEvalTip v evmTop (clipperKickLocalsTop evmLock I feedPrice top)
          (clipperKickLocalsTop_get_tip evmLock I feedPrice top))
  have hchip : ExecStmt (config v) tipFrame evmTop
      (.letDecl "_chip" (some uint256) (.storage chipRef))
      (.ok chipFrame evmTop) := by
    exact ExecStmt.letDecl (by
      simpa [tipFrame, chipFrame, clipperKickLocalsChip] using
        clipperEvalChip v evmTop (clipperKickLocalsTip evmLock evmTop I feedPrice top)
          (clipperKickLocalsTip_get_chip evmLock evmTop I feedPrice top))
  have hcoin : ExecStmt (config v) chipFrame evmTop
      (.letDecl "coin" (some uint256) (.intLit 0)) (.ok coinFrame evmTop) := by
    exact ExecStmt.letDecl (by simp [chipFrame, coinFrame, clipperKickLocalsCoinZero,
      evalExpr?, pure])
  have hafter' : ExecBlock (config v) coinFrame evmTop
      [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
        .assign .storage lockedRef (.intLit 0), .return [.var "id"] ] result := by
    simpa [buf, top, evmTop, coinFrame] using hafter
  simpa [clipperKickAfterInitializationBody, clipperKickIncentiveCond,
    clipperKickIncentiveBody, topFrame, tipFrame, chipFrame, coinFrame,
    checkedAddUintInto, checkedExternalCallStmts] using
    (ExecBlock.consNormal hgetFeed <|
      ExecBlock.consNormal hrmul <|
        ExecBlock.consNormal hrequire <|
          ExecBlock.consNormal htopAssign <|
            ExecBlock.consNormal htip <|
              ExecBlock.consNormal hchip <|
                ExecBlock.consNormal hcoin hafter')

end Benchmarks.Dss.Clipper
