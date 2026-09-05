import Benchmarks.Dss.Clipper.KickSourceInit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! The source-level `kick` prefix through construction of `sales[id]`. -/

def clipperKickAfterInitializationBody (v : ClipperImmutables) : List Stmt :=
  [ .internalCall "getFeedPrice" [] "feedPrice",
    .internalCall "rmul" [.var "feedPrice", .storage bufRef] "top",
    .require (.binary .gt (.var "top") (.intLit 0)),
    .assign .storage (salesF (.var "id") "top") (.var "top"),
    .letDecl "_tip" (some uint256) (.storage tipRef),
    .letDecl "_chip" (some uint256) (.storage chipRef),
    .letDecl "coin" (some uint256) (.intLit 0),
    .ite
      (.binary .or (.binary .gt (.var "_tip") (.intLit 0))
        (.binary .gt (.var "_chip") (.intLit 0)))
      ([ .internalCall "wmul" [.var "tab", .var "_chip"] "chipCoin" ] ++
        checkedAddUintInto "coinNew" (.var "_tip") (.var "chipCoin") ++
        [ .assign .localVar (varRef "coin") (.var "coinNew") ] ++
        checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
          [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
      [],
    .assign .storage lockedRef (.intLit 0),
    .return [.var "id"] ]

theorem clipperKickSourcePrefix
    (v : ClipperImmutables) (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Solm.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : 0 < (clipperKickTabWord I).toNat)
    (hlot : 0 < (clipperKickLotWord I).toNat)
    (husr : clipperKickUsrMaskedWord I ≠ ⟨0⟩)
    (hid : clipperKickSourceIdWord (clipperKickLockedState evm) ≠ ⟨0⟩)
    (hlen :
      (clipperKickSourceActiveLengthWord (clipperKickLockedState evm)).toNat + 1 <
        UInt256.size)
    {result : ExecResult}
    (hafter :
      ExecBlock (config v)
        { contract := contract v,
          locals := clipperKickLocalsActivePos (clipperKickLockedState evm) I }
        (clipperKickSourceInitializedState (clipperKickLockedState evm) I)
        (clipperKickAfterInitializationBody v) result) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body result := by
  let evmLock := clipperKickLockedState evm
  let startFrame : Frame := { contract := contract v, locals := clipperKickStore I }
  let idFrame : Frame :=
    { contract := contract v, locals := clipperKickLocalsId evmLock I }
  let posFrame : Frame :=
    { contract := contract v, locals := clipperKickLocalsActivePos evmLock I }
  have hauthEval :
      evalExpr? (config v) startFrame evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
      (clipperKickStore_get_wards I) hauth
  have hlockedEval :
      evalExpr? (config v) startFrame evm
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
      (clipperKickStore_get_locked I) hlocked
  have hlockAssign :
      ExecStmt (config v) startFrame evm
        (.assign .storage lockedRef (.intLit 1)) (.ok startFrame evmLock) := by
    have hone : evalExpr? (config v) startFrame evm (.intLit 1) =
        .ok (.int 1) := by simp [startFrame, evalExpr?, pure]
    apply ExecStmt.assign hone
    simpa [startFrame, evmLock, clipperKickLockedState] using
      assign_clipperLocked v evm (clipperKickStore I)
        (clipperKickStore_get_locked I) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_clipperStopped_lt_one v evmLock (clipperKickStore I)
      (clipperKickStore_get_stopped I) hstopped
  have hidLet :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "id" (some uint256)
          (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))))
        (.ok idFrame evmLock) := by
    simpa [startFrame, idFrame, evmLock] using
      (ExecStmt.letDecl (clipperEvalKickIdExpr v evmLock I))
  have hidAssign :
      ExecStmt (config v) idFrame evmLock
        (.assign .storage kicksRef (.var "id"))
        (.ok idFrame (clipperKickSourceIdState evmLock)) := by
    have hidValue : evalExpr? (config v) idFrame evmLock (.var "id") =
        .ok (.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)) := by
      simp only [idFrame, evalExpr?, clipperKickLocalsId, store_get_self,
        EvalResult.ofOption]
    apply ExecStmt.assign hidValue
    · simpa [idFrame] using clipperKickAssignId v evmLock I
  have hpush :
      ExecStmt (config v) idFrame (clipperKickSourceIdState evmLock)
        (.push activeRef (some (.var "id")))
        (.ok idFrame (clipperKickSourceActiveState evmLock)) := by
    have hidValue : evalExpr? (config v) idFrame (clipperKickSourceIdState evmLock)
        (.var "id") =
        .ok (.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)) := by
      simp only [idFrame, evalExpr?, clipperKickLocalsId, store_get_self,
        EvalResult.ofOption]
    apply ExecStmt.pushVal hidValue
    · simpa [idFrame] using clipperKickPushActive v evmLock I hlen
  have hposLet :
      ExecStmt (config v) idFrame (clipperKickSourceActiveState evmLock)
        (.letDecl "activePos" (some uint256)
          (wrap256 (.binary .sub (.arrayLength .storage activeRef) (.intLit 1))))
        (.ok posFrame (clipperKickSourceActiveState evmLock)) := by
    simpa [idFrame, posFrame] using
      (ExecStmt.letDecl (clipperEvalKickActivePosExpr v evmLock I))
  have hbody :
      ExecBlock (config v) startFrame evm (kickTransition v).body result := by
    simpa [kickTransition, nonpayable, auth, lockPrefix, isStopped,
      wrappingSubInto, checkedAddUintInto, checkedExternalCallStmts,
      clipperKickAfterInitializationBody, startFrame, idFrame, posFrame,
      evmLock] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true hvalue
        refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal hlockAssign ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue
          (clipperEvalKickTabPositive v evmLock I htab)) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue
          (clipperEvalKickLotPositive v evmLock I hlot)) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue
          (clipperEvalKickUsrNonzero v evmLock I husr)) ?_
        refine ExecBlock.consNormal hidLet ?_
        refine ExecBlock.consNormal hidAssign ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue
          (clipperEvalKickIdPositive v evmLock I hid)) ?_
        refine ExecBlock.consNormal hpush ?_
        refine ExecBlock.consNormal hposLet ?_
        refine ExecBlock.consNormal (clipperKickAssignSalesPos v evmLock I) ?_
        refine ExecBlock.consNormal (clipperKickAssignSalesTab v evmLock I) ?_
        refine ExecBlock.consNormal (clipperKickAssignSalesLot v evmLock I) ?_
        refine ExecBlock.consNormal (clipperKickAssignSalesUsr v evmLock I) ?_
        refine ExecBlock.consNormal (clipperKickAssignSalesTic v evmLock I) ?_
        simpa [posFrame, evmLock] using hafter)
  simpa [startFrame] using hbody

end Benchmarks.Dss.Clipper
