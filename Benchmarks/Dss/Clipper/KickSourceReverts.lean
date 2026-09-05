import Benchmarks.Dss.Clipper.KickSourcePrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! Source-level reverts in the validation prefix of `kick`. -/

private theorem clipperKickLockAssign (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    ExecStmt (config v) { contract := contract v, locals := clipperKickStore I } evm
      (.assign .storage lockedRef (.intLit 1))
      (.ok { contract := contract v, locals := clipperKickStore I }
        (clipperKickLockedState evm)) := by
  have hone : evalExpr? (config v)
      { contract := contract v, locals := clipperKickStore I } evm (.intLit 1) =
      .ok (.int 1) := by simp [evalExpr?, pure]
  apply ExecStmt.assign hone
  simpa [clipperKickLockedState] using
    assign_clipperLocked v evm (clipperKickStore I)
      (clipperKickStore_get_locked I) ⟨1⟩

private theorem clipperKickIdLet (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    ExecStmt (config v) { contract := contract v, locals := clipperKickStore I } evm
      (.letDecl "id" (some uint256)
        (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))))
      (.ok { contract := contract v, locals := clipperKickLocalsId evm I } evm) := by
  simpa using ExecStmt.letDecl (clipperEvalKickIdExpr v evm I)

private theorem clipperKickIdAssign (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    ExecStmt (config v) { contract := contract v, locals := clipperKickLocalsId evm I } evm
      (.assign .storage kicksRef (.var "id"))
      (.ok { contract := contract v, locals := clipperKickLocalsId evm I }
        (clipperKickSourceIdState evm)) := by
  have hid : evalExpr? (config v)
      { contract := contract v, locals := clipperKickLocalsId evm I } evm (.var "id") =
      .ok (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsId, store_get_self, EvalResult.ofOption]
  apply ExecStmt.assign hid
  simpa using clipperKickAssignId v evm I

theorem clipperKickSourceRevertsUnauthorized (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body .reverted := by
  have hauthEval := evalExpr_clipperAuth_false v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  simpa [kickTransition, nonpayable, auth] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consRevert (ExecStmt.requireFalse hauthEval))

theorem clipperKickSourceRevertsLocked (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ ≠ ⟨0⟩) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body .reverted := by
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_false v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  simpa [kickTransition, nonpayable, auth, lockPrefix] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consRevert (ExecStmt.requireFalse hlockedEval)))

theorem clipperKickSourceRevertsStopped (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : 1 ≤ (Solm.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body .reverted := by
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  have hstoppedEval := evalExpr_clipperStopped_lt_one_false v
    (clipperKickLockedState evm) (clipperKickStore I)
    (clipperKickStore_get_stopped I) hstopped
  simpa [kickTransition, nonpayable, auth, lockPrefix, isStopped] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval)
          (ExecBlock.consNormal (clipperKickLockAssign v evm I)
            (ExecBlock.consRevert (ExecStmt.requireFalse hstoppedEval)))))

theorem clipperKickSourceRevertsTab (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Solm.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : ¬ 0 < (clipperKickTabWord I).toNat) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body .reverted := by
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  have hstoppedEval := evalExpr_clipperStopped_lt_one v (clipperKickLockedState evm)
    (clipperKickStore I) (clipperKickStore_get_stopped I) hstopped
  have htabEval := clipperEvalKickTabNotPositive v (clipperKickLockedState evm) I htab
  simpa [kickTransition, nonpayable, auth, lockPrefix, isStopped] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval)
          (ExecBlock.consNormal (clipperKickLockAssign v evm I)
            (ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval)
              (ExecBlock.consRevert (ExecStmt.requireFalse htabEval))))))

theorem clipperKickSourceRevertsLot (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Solm.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : 0 < (clipperKickTabWord I).toNat)
    (hlot : ¬ 0 < (clipperKickLotWord I).toNat) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body .reverted := by
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  have hstoppedEval := evalExpr_clipperStopped_lt_one v (clipperKickLockedState evm)
    (clipperKickStore I) (clipperKickStore_get_stopped I) hstopped
  simpa [kickTransition, nonpayable, auth, lockPrefix, isStopped] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval)
          (ExecBlock.consNormal (clipperKickLockAssign v evm I)
            (ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval)
              (ExecBlock.consNormal (ExecStmt.requireTrue
                (clipperEvalKickTabPositive v (clipperKickLockedState evm) I htab))
                (ExecBlock.consRevert (ExecStmt.requireFalse
                  (clipperEvalKickLotNotPositive v (clipperKickLockedState evm) I hlot))))))))

theorem clipperKickSourceRevertsUsr (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Solm.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : 0 < (clipperKickTabWord I).toNat)
    (hlot : 0 < (clipperKickLotWord I).toNat)
    (husr : clipperKickUsrMaskedWord I = ⟨0⟩) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body .reverted := by
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  have hstoppedEval := evalExpr_clipperStopped_lt_one v (clipperKickLockedState evm)
    (clipperKickStore I) (clipperKickStore_get_stopped I) hstopped
  simpa [kickTransition, nonpayable, auth, lockPrefix, isStopped] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval)
          (ExecBlock.consNormal (clipperKickLockAssign v evm I)
            (ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval)
              (ExecBlock.consNormal (ExecStmt.requireTrue
                (clipperEvalKickTabPositive v (clipperKickLockedState evm) I htab))
                (ExecBlock.consNormal (ExecStmt.requireTrue
                  (clipperEvalKickLotPositive v (clipperKickLockedState evm) I hlot))
                  (ExecBlock.consRevert (ExecStmt.requireFalse
                    (clipperEvalKickUsrZero v (clipperKickLockedState evm) I husr)))))))))

theorem clipperKickSourceRevertsId (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
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
    (hid : clipperKickSourceIdWord (clipperKickLockedState evm) = ⟨0⟩) :
    ExecBlock (config v) { contract := contract v, locals := clipperKickStore I }
      evm (kickTransition v).body .reverted := by
  let evmLock := clipperKickLockedState evm
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  have hstoppedEval := evalExpr_clipperStopped_lt_one v evmLock (clipperKickStore I)
    (clipperKickStore_get_stopped I) (by simpa [evmLock] using hstopped)
  have hidAssign := clipperKickIdAssign v evmLock I
  simpa [kickTransition, nonpayable, auth, lockPrefix, isStopped, evmLock] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval)
          (ExecBlock.consNormal (clipperKickLockAssign v evm I)
            (ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval)
              (ExecBlock.consNormal (ExecStmt.requireTrue
                (clipperEvalKickTabPositive v evmLock I htab))
                (ExecBlock.consNormal (ExecStmt.requireTrue
                  (clipperEvalKickLotPositive v evmLock I hlot))
                  (ExecBlock.consNormal (ExecStmt.requireTrue
                    (clipperEvalKickUsrNonzero v evmLock I husr))
                    (ExecBlock.consNormal (clipperKickIdLet v evmLock I)
                      (ExecBlock.consNormal hidAssign
                        (ExecBlock.consRevert (ExecStmt.requireFalse
                          (clipperEvalKickIdNotPositive v evmLock I hid))))))))))))

end Benchmarks.Dss.Clipper
