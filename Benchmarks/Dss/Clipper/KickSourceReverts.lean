import Benchmarks.Dss.Clipper.KickSourcePrefix

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! Source-level reverts in the validation prefix of `kick`. -/

private theorem clipperKickLockAssignSplit (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    (evm.executionEnv.perm = true →
    ExecStmt fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm
      (.assign .storage lockedRef (.intLit 1))
      (.ok { contract := contract, locals := clipperKickStore I, immutables := immStore v }
        (clipperKickLockedState evm))) ∧
    (evm.executionEnv.perm = false →
      ExecStmt fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm
        (.assign .storage lockedRef (.intLit 1)) .staticViolation) := by
  have hone : evalExpr? config
      { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm (.intLit 1) =
      .ok (.int 1) := by simp [evalExpr?, pure]
  have hassign : assignStorageRef? config
      { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm
      .storage lockedRef (.int 1) =
        .ok ({ contract := contract, locals := clipperKickStore I, immutables := immStore v },
          clipperKickLockedState evm) := by
    simpa [clipperKickLockedState] using
      assign_clipperLocked v evm (clipperKickStore I)
        (clipperKickStore_get_locked I) ⟨1⟩
  constructor
  · intro hperm
    exact ExecStmt.assign (hperm := Or.inr hperm) hone hassign
  · intro hperm
    exact ExecStmt.assignStatic hone hassign hperm

private theorem clipperKickLockAssign (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm
      (.assign .storage lockedRef (.intLit 1))
      (.ok { contract := contract, locals := clipperKickStore I, immutables := immStore v }
        (clipperKickLockedState evm)) :=
  (clipperKickLockAssignSplit v evm I).1 hperm

private theorem clipperKickIdLet (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    ExecStmt fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm
      (.letDecl "id" (some uint256)
        (wrap256 (.binary .add (.storage kicksRef) (.intLit 1))))
      (.ok { contract := contract, locals := clipperKickLocalsId evm I, immutables := immStore v } evm) := by
  simpa using ExecStmt.letDecl (clipperEvalKickIdExpr v evm I)

private theorem clipperKickIdAssign (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config { contract := contract, locals := clipperKickLocalsId evm I, immutables := immStore v } evm
      (.assign .storage kicksRef (.var "id"))
      (.ok { contract := contract, locals := clipperKickLocalsId evm I, immutables := immStore v }
        (clipperKickSourceIdState evm)) := by
  have hid : evalExpr? config
      { contract := contract, locals := clipperKickLocalsId evm I, immutables := immStore v } evm (.var "id") =
      .ok (.int (Int.ofNat (clipperKickSourceIdWord evm).toNat)) := by
    simp only [evalExpr?, clipperKickLocalsId, store_get_self, EvalResult.ofOption]
  apply ExecStmt.assign (hperm := Or.inr hperm) hid
  simpa using clipperKickAssignId v evm I

theorem clipperKickSourceRevertsUnauthorized (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted := by
  have hauthEval := evalExpr_clipperAuth_false v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  simpa [kickTransition, nonpayable, auth] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consRevert (ExecStmt.requireFalse hauthEval))

theorem clipperKickSourceRevertsLocked (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ ≠ ⟨0⟩) :
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted := by
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_false v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  simpa [kickTransition, nonpayable, auth, lockPrefix] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consRevert (ExecStmt.requireFalse hlockedEval)))

theorem clipperKickSourceRevertsStoppedSplit (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩) :
    (evm.executionEnv.perm = true →
     1 ≤ (Stele.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat →
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted) ∧
    (evm.executionEnv.perm = false →
      ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
        evm kickTransition.body .staticViolation) := by
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  have hprefix {result : ExecResult}
      (hrest : ExecBlock fork config
        { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm
        (kickTransition.body.drop 3) result) :
      ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v } evm
        kickTransition.body result := by
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) hrest))
  constructor
  · intro hperm hstopped
    have hstoppedEval := evalExpr_clipperStopped_lt_one_false v
      (clipperKickLockedState evm) (clipperKickStore I)
      (clipperKickStore_get_stopped I) hstopped
    exact hprefix (ExecBlock.consNormal (clipperKickLockAssign (fork := fork) (hperm := by assumption) v evm I)
      (ExecBlock.consRevert (ExecStmt.requireFalse hstoppedEval)))
  · intro hperm
    exact hprefix (ExecBlock.consStatic ((clipperKickLockAssignSplit v evm I).2 hperm))

theorem clipperKickSourceRevertsStopped (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : 1 ≤ (Stele.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted :=
  (clipperKickSourceRevertsStoppedSplit v evm I hvalue hsrc hauth hlocked).1 hperm hstopped

theorem clipperKickSourceRevertsTab (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Stele.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : ¬ 0 < (clipperKickTabWord I).toNat)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted := by
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
          (ExecBlock.consNormal (clipperKickLockAssign (fork := fork) (hperm := by assumption) v evm I)
            (ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval)
              (ExecBlock.consRevert (ExecStmt.requireFalse htabEval))))))

theorem clipperKickSourceRevertsLot (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Stele.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : 0 < (clipperKickTabWord I).toNat)
    (hlot : ¬ 0 < (clipperKickLotWord I).toNat)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted := by
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
          (ExecBlock.consNormal (clipperKickLockAssign (fork := fork) (hperm := by assumption) v evm I)
            (ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval)
              (ExecBlock.consNormal (ExecStmt.requireTrue
                (clipperEvalKickTabPositive v (clipperKickLockedState evm) I htab))
                (ExecBlock.consRevert (ExecStmt.requireFalse
                  (clipperEvalKickLotNotPositive v (clipperKickLockedState evm) I hlot))))))))

theorem clipperKickSourceRevertsUsr (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Stele.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : 0 < (clipperKickTabWord I).toNat)
    (hlot : 0 < (clipperKickLotWord I).toNat)
    (husr : clipperKickUsrMaskedWord I = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted := by
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
          (ExecBlock.consNormal (clipperKickLockAssign (fork := fork) (hperm := by assumption) v evm I)
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
    (hauth : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperRelyAuthStorageSlot I) = ⟨1⟩)
    (hlocked : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨13⟩ = ⟨0⟩)
    (hstopped : (Stele.EVM.storageLoad (clipperKickLockedState evm)
      (clipperKickLockedState evm).executionEnv.codeOwner ⟨14⟩).toNat < 1)
    (htab : 0 < (clipperKickTabWord I).toNat)
    (hlot : 0 < (clipperKickLotWord I).toNat)
    (husr : clipperKickUsrMaskedWord I ≠ ⟨0⟩)
    (hid : clipperKickSourceIdWord (clipperKickLockedState evm) = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config { contract := contract, locals := clipperKickStore I, immutables := immStore v }
      evm kickTransition.body .reverted := by
  let evmLock := clipperKickLockedState evm
  have hauthEval := evalExpr_clipperAuth_true v evm I (clipperKickStore I) hsrc
    (clipperKickStore_get_wards I) hauth
  have hlockedEval := evalExpr_clipperLocked_zero_true v evm (clipperKickStore I)
    (clipperKickStore_get_locked I) hlocked
  have hstoppedEval := evalExpr_clipperStopped_lt_one v evmLock (clipperKickStore I)
    (clipperKickStore_get_stopped I) (by simpa [evmLock] using hstopped)
  have hidAssign := clipperKickIdAssign (fork := fork) (hperm := by
    simpa only [evmLock, clipperKickLockedState, storageStore_executionEnv] using hperm) v evmLock I
  simpa [kickTransition, nonpayable, auth, lockPrefix, isStopped, evmLock] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
      (ExecBlock.consNormal (ExecStmt.requireTrue hauthEval)
        (ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval)
          (ExecBlock.consNormal (clipperKickLockAssign (fork := fork) (hperm := by assumption) v evm I)
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
