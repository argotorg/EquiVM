import Benchmarks.Dss.Clipper.Guards
import Benchmarks.Dss.Clipper.TakeStatus
import Benchmarks.Dss.Clipper.Vat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem evalStorageRef_clipperTakeStopped (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) :
    evalStorageRef (config v) { contract := contract v, locals := locals } evm
      stoppedRef = .ok { base := "stopped", steps := [] } := by
  simp [stoppedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalExpr_clipperTakeStopped_lt_three_false (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "stopped" = none)
    (hload : 3 ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage stoppedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := stoppedRef)
      (er := { base := "stopped", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨14⟩)
      (hbase := hbase)
      (her := evalStorageRef_clipperTakeStopped v evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa using clipperStorageLocLoad_uint256 evm ⟨14⟩)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.lt
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat))
      (Value.int 3) = .ok (.bool false)
  simp [evalBinaryOp?]
  omega

theorem evalExpr_clipperTakeStopped_lt_three_true (v : ClipperImmutables)
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "stopped" = none)
    (hload : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat < 3) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.storage stoppedRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := locals })
      (slot := stoppedRef)
      (er := { base := "stopped", steps := [] })
      (t := .int uint256Int)
      (loc := wordLoc ⟨14⟩)
      (hbase := hbase)
      (her := evalStorageRef_clipperTakeStopped v evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa using clipperStorageLocLoad_uint256 evm ⟨14⟩)
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.lt
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨14⟩).toNat))
      (Value.int 3) = .ok (.bool true)
  simp [evalBinaryOp?]
  omega

theorem clipperTakeBodyRevertsLocked {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
      clipperTakeStore] using
      evalExpr_clipperLocked_zero_false v evm0 locals (by simp [locals, clipperTakeStore])
        hlocked
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        exact ExecBlock.consRevert (ExecStmt.requireFalse hlockedEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperTakeStoppedSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      3 ≤ (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool false) := by
    apply evalExpr_clipperTakeStopped_lt_three_false
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using
        hstopped
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse hstoppedEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperTakeInactiveSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I = ⟨0⟩) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using
        hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I = ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool false) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_false v evmLock I husrLoad
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse husrEval))
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeStatusSourceRevertsOfStatus {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        .reverted) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using
        hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        .reverted := by
    simpa [ticFrame, evmLock, evm0] using hstatus
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        exact ExecBlock.consRevert hstatus)
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeStatusDoneTrueSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I true price }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperTakeLocalsSt evmLock I true price }
  let doneFrame : Frame := { contract := contract v, locals := clipperTakeLocalsDone evmLock I true price }
  let priceFrame : Frame := { contract := contract v, locals := clipperTakeLocalsPrice evmLock I true price }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using
        hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool true)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I true price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I true price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool false) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_false v evmLock evmPrice I price
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal hletDone ?_
        refine ExecBlock.consNormal hletPrice ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse hdoneEval))
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeTooExpensiveSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hmax : (clipperTakeMaxWord I).toNat < price.toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
  let doneFrame : Frame := { contract := contract v, locals := clipperTakeLocalsDone evmLock I false price }
  let priceFrame : Frame := { contract := contract v, locals := clipperTakeLocalsPrice evmLock I false price }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using
        hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? (config v) priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool false) := by
    simpa [priceFrame] using
      clipperEvalTakeMaxGePrice_false v evmLock evmPrice I price hmax
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal hletDone ?_
        refine ExecBlock.consNormal hletPrice ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse hmaxEval))
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeOwe0MulOverflowSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hover :
      UInt256.size ≤
        (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
          (clipperTakeAmtWord I)).toNat * price.toNat)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
  let doneFrame : Frame := { contract := contract v, locals := clipperTakeLocalsDone evmLock I false price }
  let priceFrame : Frame := { contract := contract v, locals := clipperTakeLocalsPrice evmLock I false price }
  let lotFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsLot evmLock evmPrice I false price }
  let tabFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsTab evmLock evmPrice I false price }
  let sliceFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using
        hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? (config v) priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using
      clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt (config v) priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt (config v) lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt (config v) tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeSolm :=
          { contract := contract v, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I) })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction v)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have hletOwe0Revert :
      ExecStmt (config v) sliceFrame evmPrice
        (.letDecl "owe0" (some uint256) (mul256 (.var "slice") (.var "price")))
        .reverted := by
    exact ExecStmt.letDeclRevert
      (by simpa [sliceFrame, slice] using
        (clipperEvalTakeOwe0Mul_revert v evmLock evmPrice I price slice
          (by simpa [slice] using hover)))
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal hletDone ?_
        refine ExecBlock.consNormal hletPrice ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hmaxEval) ?_
        refine ExecBlock.consNormal hletLot ?_
        refine ExecBlock.consNormal hletTab ?_
        refine ExecBlock.consNormal hminCall ?_
        exact ExecBlock.consRevert hletOwe0Revert)
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeOwe0MulSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size) :
    let owe0 := UInt256.mul slice price
    ExecBlock (config v)
      { contract := contract v,
        locals := clipperTakeLocalsSlice evmLoc evmRead I false price slice }
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [.letDecl "owe" (some uint256) (.var "owe0")])
      (.ok
        { contract := contract v,
          locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0 }
        evmRead) := by
  intro owe0
  let sliceFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsSlice evmLoc evmRead I false price slice }
  let owe0Frame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsOwe0 evmLoc evmRead I false price slice owe0 }
  let oweFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0 }
  have hletOwe0 :
      ExecStmt (config v) sliceFrame evmRead
        (.letDecl "owe0" (some uint256) (mul256 (.var "slice") (.var "price")))
        (.ok owe0Frame evmRead) := by
    simpa [sliceFrame, owe0Frame, owe0, clipperTakeLocalsOwe0] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := sliceFrame) (evm := evmRead) (name := "owe0")
        (ty := some uint256) (expr := mul256 (.var "slice") (.var "price"))
        (value := .int (Int.ofNat owe0.toNat))
        (by simpa [sliceFrame, owe0] using
          clipperEvalTakeOwe0Mul_ok v evmLoc evmRead I price slice hmul))
  have hrequire :
      evalExpr? (config v) owe0Frame evmRead
        (.binary .or
          (.binary .eq (.var "price") (.intLit 0))
          (.binary .eq (.binary .div (.var "owe0") (.var "price")) (.var "slice"))) =
        .ok (.bool true) := by
    simpa [owe0Frame, owe0] using
      clipperEvalTakeCheckedOwe0Require_true v evmLoc evmRead I price slice hmul
  have hletOwe :
      ExecStmt (config v) owe0Frame evmRead
        (.letDecl "owe" (some uint256) (.var "owe0"))
        (.ok oweFrame evmRead) := by
    simpa [owe0Frame, oweFrame, clipperTakeLocalsOwe] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := owe0Frame) (evm := evmRead) (name := "owe")
        (ty := some uint256) (expr := .var "owe0")
        (value := .int (Int.ofNat owe0.toNat))
        (by simpa [owe0Frame] using
          clipperEvalTakeVarOwe0AtOwe0 v evmLoc evmRead evmRead I false price slice owe0))
  simpa [checkedMulUintInto, sliceFrame, oweFrame] using
    (ExecBlock.consNormal hletOwe0
      (ExecBlock.consNormal (ExecStmt.requireTrue hrequire)
        (ExecBlock.consNormal hletOwe ExecBlock.nil)))

theorem clipperTakeOweGtTabIte (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat) :
    let owe0 := UInt256.mul slice price
    let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
      evmRead
      (.ite
        (.binary .gt (.var "owe") (.var "tab"))
        [ .assign .localVar (varRef "owe") (.var "tab"),
          .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
        [ .ite
          (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite
              (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [] ])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe0 slice'))
        evmRead) := by
  intro owe0 slice'
  have hprice : price ≠ ⟨0⟩ := by
    intro hprice
    subst price
    have hzero : UInt256.mul slice ⟨0⟩ = ⟨0⟩ := by
      rw [u256_mul_comm slice ⟨0⟩]
      exact Reasoning.Theory.clipperMul_zero_left slice
    simp [hzero] at hgt
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let oweTabFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweTab evmLoc evmRead I false price slice owe0 owe0)
  let sliceFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe0 slice')
  have hcond :
      evalExpr? (config v) oweFrame evmRead
        (.binary .gt (.var "owe") (.var "tab")) = .ok (.bool true) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeOweGtTab_true v evmLoc evmRead I price slice owe0 owe0 hgt
  have hassignOwe :
      ExecStmt (config v) oweFrame evmRead
        (.assign .localVar (varRef "owe") (.var "tab"))
        (.ok oweTabFrame evmRead) := by
    simpa [oweFrame, oweTabFrame, owe0] using
      clipperTakeAssignOweToTab v evmLoc evmRead I price slice owe0 owe0
  have hassignSlice :
      ExecStmt (config v) oweTabFrame evmRead
        (.assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")))
        (.ok sliceFrame evmRead) := by
    simpa [oweTabFrame, sliceFrame, owe0, slice'] using
      clipperTakeAssignSliceFromOweTab v evmLoc evmRead I price slice owe0 (hprice := hprice)
  have hthen :
      ExecBlock (config v) oweFrame evmRead
        [ .assign .localVar (varRef "owe") (.var "tab"),
          .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
        (.ok sliceFrame evmRead) := by
    exact ExecBlock.consNormal hassignOwe
      (ExecBlock.consNormal hassignSlice ExecBlock.nil)
  simpa [oweFrame, sliceFrame] using ExecStmt.iteTrue hcond hthen

theorem clipperTakeOweEqTabIte (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hle :
      (UInt256.mul slice price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hge :
      (clipperTakeSalesTabEVMWord evmRead I).toNat ≤
        (UInt256.mul slice price).toNat) :
    let owe0 := UInt256.mul slice price
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
      evmRead
      (.ite
        (.binary .gt (.var "owe") (.var "tab"))
        [ .assign .localVar (varRef "owe") (.var "tab"),
          .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
        [ .ite
          (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite
              (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [] ])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead) := by
  intro owe0
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  have houter :
      evalExpr? (config v) oweFrame evmRead
        (.binary .gt (.var "owe") (.var "tab")) = .ok (.bool false) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeOweGtTab_false v evmLoc evmRead I price slice owe0 owe0 hle
  have hinnerCond :
      evalExpr? (config v) oweFrame evmRead
        (.binary .and (.binary .lt (.var "owe") (.var "tab"))
          (.binary .lt (.var "slice") (.var "lot"))) = .ok (.bool false) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeNoChostCond_false_left v evmLoc evmRead I price slice owe0 owe0 hge
  have hinner :
      ExecStmt (config v) oweFrame evmRead
        (.ite
          (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite
              (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [])
        (.ok oweFrame evmRead) :=
    ExecStmt.iteFalse hinnerCond ExecBlock.nil
  have helse :
      ExecBlock (config v) oweFrame evmRead
        [ .ite
          (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite
              (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [] ]
        (.ok oweFrame evmRead) :=
    ExecBlock.consNormal hinner ExecBlock.nil
  simpa [oweFrame] using ExecStmt.iteFalse houter helse

theorem clipperTakeOweLtTabSliceGeLotIte (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hle :
      (UInt256.mul slice price).toNat ≤ (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hlt :
      (UInt256.mul slice price).toNat < (clipperTakeSalesTabEVMWord evmRead I).toNat)
    (hsliceGe : (clipperTakeSalesLotEVMWord evmRead I).toNat ≤ slice.toNat) :
    let owe0 := UInt256.mul slice price
    ExecStmt (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
      evmRead
      (.ite
        (.binary .gt (.var "owe") (.var "tab"))
        [ .assign .localVar (varRef "owe") (.var "tab"),
          .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
        [ .ite
          (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite
              (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [] ])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0))
        evmRead) := by
  intro owe0
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  have houter :
      evalExpr? (config v) oweFrame evmRead
        (.binary .gt (.var "owe") (.var "tab")) = .ok (.bool false) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeOweGtTab_false v evmLoc evmRead I price slice owe0 owe0 hle
  have hinnerCond :
      evalExpr? (config v) oweFrame evmRead
        (.binary .and (.binary .lt (.var "owe") (.var "tab"))
          (.binary .lt (.var "slice") (.var "lot"))) = .ok (.bool false) := by
    simpa [oweFrame, owe0] using
      clipperEvalTakeNoChostCond_false_right v evmLoc evmRead I price slice owe0 owe0
        hlt hsliceGe
  have hinner :
      ExecStmt (config v) oweFrame evmRead
        (.ite
          (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite
              (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [])
        (.ok oweFrame evmRead) :=
    ExecStmt.iteFalse hinnerCond ExecBlock.nil
  have helse :
      ExecBlock (config v) oweFrame evmRead
        [ .ite
          (.binary .and (.binary .lt (.var "owe") (.var "tab"))
            (.binary .lt (.var "slice") (.var "lot")))
          ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
            wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
            [ .ite
              (.binary .lt (.var "remainingTab") (.var "_chost"))
              ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                  .assign .localVar (varRef "slice")
                    (.binary .div (.var "owe") (.var "price")) ])
              [] ])
          [] ]
        (.ok oweFrame evmRead) :=
    ExecBlock.consNormal hinner ExecBlock.nil
  simpa [oweFrame] using ExecStmt.iteFalse houter helse

theorem clipperTakePostOweGtTabSubBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice owe0 : UInt256)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat) :
    let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
    let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
      (clipperTakeSalesTabEVMWord evmRead I)
    let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe0
          slice'))
      evmRead
      (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ])
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe0
            slice' tabNew lotNew))
        evmRead) := by
  intro slice' tabNew lotNew
  let sliceFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe0 slice')
  let tabNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsTabNew evmLoc evmRead I false price slice owe0 owe0 slice' tabNew)
  let lotNewFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsLotNew evmLoc evmRead I false price slice owe0 owe0 slice' tabNew
        lotNew)
  let tabFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsTabAssigned evmLoc evmRead I false price slice owe0 owe0 slice'
        tabNew lotNew)
  let lotFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe0 slice'
        tabNew lotNew)
  have htabNew :
      ExecStmt (config v) sliceFrame evmRead
        (.letDecl "tabNew" (some uint256)
          (wrap256 (.binary .sub (.var "tab") (.var "owe"))))
        (.ok tabNewFrame evmRead) := by
    simpa [sliceFrame, tabNewFrame, tabNew] using
      clipperTakeLetTabNew v evmLoc evmRead I price slice owe0 owe0 slice'
  have hlotNew :
      ExecStmt (config v) tabNewFrame evmRead
        (.letDecl "lotNew" (some uint256)
          (wrap256 (.binary .sub (.var "lot") (.var "slice"))))
        (.ok lotNewFrame evmRead) := by
    simpa [tabNewFrame, lotNewFrame, lotNew, slice'] using
      clipperTakeLetLotNew v evmLoc evmRead I price slice owe0 owe0 slice' tabNew
        hsliceLot
  have hassignTab :
      ExecStmt (config v) lotNewFrame evmRead
        (.assign .localVar (varRef "tab") (.var "tabNew"))
        (.ok tabFrame evmRead) := by
    simpa [lotNewFrame, tabFrame] using
      clipperTakeAssignTabFromTabNew v evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew
  have hassignLot :
      ExecStmt (config v) tabFrame evmRead
        (.assign .localVar (varRef "lot") (.var "lotNew"))
        (.ok lotFrame evmRead) := by
    simpa [tabFrame, lotFrame] using
      clipperTakeAssignLotFromLotNew v evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew
  simpa [wrappingSubInto, sliceFrame, lotFrame] using
    (ExecBlock.consNormal htabNew
      (ExecBlock.consNormal hlotNew
        (ExecBlock.consNormal hassignTab
          (ExecBlock.consNormal hassignLot ExecBlock.nil))))

abbrev clipperTakeLocalsFluxBuyerRet (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) : Store :=
  (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice' tabNew
    lotNew).insert "_fluxBuyerRet" .unit

theorem clipperTakeDecodeFluxVoid (v : ClipperImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "flux" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem clipperEvalTakeVatCodeGuard_false (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?, EVM.Word.ofNat,
    hnoCode]

theorem clipperEvalTakeVatCodeGuard_true (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hcode :
      0 <
        (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?, EVM.Word.ofNat,
    hcode]

theorem clipperEvalTakeVatFluxBuyerArgs (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
          tabNew lotNew))
      evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] =
        .ok
          [v.ilk, .address evmRead.executionEnv.codeOwner,
            .address (AccountAddress.ofNat
              (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
            .int (Int.ofNat slice'.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  have hwho :
      Value.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat) =
        Value.address (AccountAddress.ofNat
          (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat) := by
    rw [solcAddressValue_masked (clipperTakeWhoWord I)]
    rw [u256_land_comm solcAddrMask (clipperTakeWhoWord I)]
  have hilkEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead (ilkExpr v) = .ok v.ilk := by
    simp [ilkExpr, hilk, evalExpr?, pure]
  have hthisEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead thisAddr = .ok (.address evmRead.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hwhoRaw :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
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
      clipperTakeStore, store_get_ne _ _ (by decide), store_get_self]
    rfl
  have hwhoEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead (.var "who") =
          .ok (.address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat)) := by
    simpa [hwho] using hwhoRaw
  have hsliceEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead (.var "slice") = .ok (.int (Int.ofNat slice'.toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_self]
    rfl
  simp only [evalExprs?, hilkEval, hthisEval, hwhoEval, hsliceEval, EvalResult.bind, bind,
    pure]

theorem clipperTakeVatFluxBuyerNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
          tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool false) := by
    exact clipperEvalTakeVatCodeGuard_false v evmRead
      (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
        tabNew lotNew) hnoVatCode
  simpa [checkedExternalCallStmts] using
    (ExecBlock.consRevert (ExecStmt.requireFalse hguard))

-- LIBRARY CANDIDATE: compose an `ExecBlock` prefix that reaches `.ok` with a reverting suffix.
theorem execBlockAppendRevert {cfg : Config} {solm solm' : Frame} {evm evm' : EVM.State}
    {pref suff : List Stmt}
    (hp : ExecBlock cfg solm evm pref (.ok solm' evm'))
    (hs : ExecBlock cfg solm' evm' suff .reverted) :
    ExecBlock cfg solm evm (pref ++ suff) .reverted := by
  induction pref generalizing solm evm with
  | nil =>
      cases hp
      simpa using hs
  | cons stmt rest ih =>
      cases hp with
      | consNormal hstmt hrest =>
          simpa using ExecBlock.consNormal hstmt (ih hrest)

-- LIBRARY CANDIDATE: compose an `ExecBlock` prefix that reaches `.ok` with any suffix.
theorem execBlockAppendOk {cfg : Config} {solm solm' : Frame} {evm evm' : EVM.State}
    {pref suff : List Stmt} {res : ExecResult}
    (hp : ExecBlock cfg solm evm pref (.ok solm' evm'))
    (hs : ExecBlock cfg solm' evm' suff res) :
    ExecBlock cfg solm evm (pref ++ suff) res := by
  induction pref generalizing solm evm with
  | nil =>
      cases hp
      simpa using hs
  | cons _ _ ih =>
      cases hp with
      | consNormal hstmt hrest =>
          simpa using ExecBlock.consNormal hstmt (ih hrest)

-- LIBRARY CANDIDATE: a reverting `ExecBlock` remains reverting with any statement suffix.
theorem execBlockAppendReverted {cfg : Config} {solm : Frame} {evm : EVM.State}
    {pref suff : List Stmt}
    (hp : ExecBlock cfg solm evm pref .reverted) :
    ExecBlock cfg solm evm (pref ++ suff) .reverted := by
  induction pref generalizing solm evm with
  | nil =>
      cases hp
  | cons stmt rest ih =>
      cases hp with
      | consNormal hstmt hrest =>
          simpa using ExecBlock.consNormal hstmt (ih hrest)
      | consRevert hstmt =>
          exact ExecBlock.consRevert hstmt

theorem clipperTakeOweGtTabVatFluxNoCodeTailBlock (v : ClipperImmutables)
    (evmLoc evmRead : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hnoVatCode :
      (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          .ite
            (.binary .gt (.var "owe") (.var "tab"))
            [ .assign .localVar (varRef "owe") (.var "tab"),
              .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
            [ .ite
              (.binary .and (.binary .lt (.var "owe") (.var "tab"))
                (.binary .lt (.var "slice") (.var "lot")))
              ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
                wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
                [ .ite
                  (.binary .lt (.var "remainingTab") (.var "_chost"))
                  ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                    wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                    [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                      .assign .localVar (varRef "slice")
                        (.binary .div (.var "owe") (.var "price")) ])
                  [] ])
              [] ] ] ++
        wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let adjustedFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe0 slice')
  let postSubFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe0 slice'
        tabNew lotNew)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hite :
      ExecStmt (config v) oweFrame evmRead
        (.ite
          (.binary .gt (.var "owe") (.var "tab"))
          [ .assign .localVar (varRef "owe") (.var "tab"),
            .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
          [ .ite
            (.binary .and (.binary .lt (.var "owe") (.var "tab"))
              (.binary .lt (.var "slice") (.var "lot")))
            ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
              wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
              [ .ite
                (.binary .lt (.var "remainingTab") (.var "_chost"))
                ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                  wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                  [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                    .assign .localVar (varRef "slice")
                      (.binary .div (.var "owe") (.var "price")) ])
                [] ])
            [] ])
        (.ok adjustedFrame evmRead) := by
    simpa [oweFrame, adjustedFrame, owe0, slice'] using
      clipperTakeOweGtTabIte v evmLoc evmRead I price slice hgt
  have hsubBlock :
      ExecBlock (config v) adjustedFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [adjustedFrame, postSubFrame, slice', tabNew, lotNew] using
      clipperTakePostOweGtTabSubBlock v evmLoc evmRead I price slice owe0 hsliceLot
  have hvatRevert :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [postSubFrame] using
      clipperTakeVatFluxBuyerNoCodeBlock v evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew hnoVatCode
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (.ite
          (.binary .gt (.var "owe") (.var "tab"))
          [ .assign .localVar (varRef "owe") (.var "tab"),
            .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
          [ .ite
            (.binary .and (.binary .lt (.var "owe") (.var "tab"))
              (.binary .lt (.var "slice") (.var "lot")))
            ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
              wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
              [ .ite
                (.binary .lt (.var "remainingTab") (.var "_chost"))
                ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                  wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                  [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                    .assign .localVar (varRef "slice")
                      (.binary .div (.var "owe") (.var "price")) ])
                [] ])
            [] ] ::
          (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
            wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
            [ .assign .localVar (varRef "tab") (.var "tabNew"),
              .assign .localVar (varRef "lot") (.var "lotNew") ] ++
            checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
              [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet"))
        .reverted := by
    exact ExecBlock.consNormal hite (execBlockAppendRevert hsubBlock hvatRevert)
  simpa [sliceFrame, List.append_assoc] using execBlockAppendRevert hmulBlock hafterIte

theorem clipperTakeOweGtTabVatFluxNoCodeSourceReverts {cA gh bl σ σ₀ A I}
    {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 3)
    (husr :
      clipperTakeSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hmax : price.toNat ≤ (clipperTakeMaxWord I).toNat)
    (hmul :
      (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
        (clipperTakeAmtWord I)).toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmPrice I).toNat <
        (UInt256.mul
          (clipperMinWord (clipperTakeSalesLotEVMWord evmPrice I)
            (clipperTakeAmtWord I))
          price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmPrice I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmPrice I).toNat)
    (hnoVatCode :
      (UInt256.ofNat ((evmPrice.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
      ExecStmt (config v) { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
        evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
          evmPrice)) :
    let locals := clipperTakeStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (takeTransition v).body .reverted := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  let lot := clipperTakeSalesLotEVMWord evmPrice I
  let tab := clipperTakeSalesTabEVMWord evmPrice I
  let slice := clipperMinWord lot (clipperTakeAmtWord I)
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperTakeLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperTakeLocalsTic evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperTakeLocalsSt evmLock I false price }
  let doneFrame : Frame := { contract := contract v, locals := clipperTakeLocalsDone evmLock I false price }
  let priceFrame : Frame := { contract := contract v, locals := clipperTakeLocalsPrice evmLock I false price }
  let lotFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsLot evmLock evmPrice I false price }
  let tabFrame : Frame :=
    { contract := contract v, locals := clipperTakeLocalsTab evmLock evmPrice I false price }
  let sliceFrame : Frame :=
    { contract := contract v,
      locals := clipperTakeLocalsSlice evmLock evmPrice I false price slice }
  have hlockedEval :
      evalExpr? (config v) startFrame evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [startFrame, locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) startFrame evm0 (.intLit 1) = .ok (.int 1) := by
    simp [startFrame, evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) startFrame evm0 .storage lockedRef (.int 1) =
        .ok (startFrame, evmLock) := by
    simpa [startFrame, locals, evmLock] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 3)) = .ok (.bool true) := by
    apply evalExpr_clipperTakeStopped_lt_three_true
    · simp [locals]
    · simpa [evmLock, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using hstopped
  have husrLoad : clipperTakeSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperTakeSalesUsrEVMWord, clipperTakeSalesUsrWord, evmLock,
      evm0, initState, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperTakeLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalTakeSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperTakeLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperTakeSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalTakeSalesTicAfterUsr v evmLock I))
  have husrEval :
      evalExpr? (config v) ticFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [ticFrame] using clipperEvalTakeUsrNeZeroAfterTic_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) ticFrame evmLock
        (.internalCall "status" [.var "tic", .storage (salesF (.var "id") "top")] "st")
        (.ok stFrame evmPrice) := by
    simpa [ticFrame, stFrame, evmLock, evm0] using hstatus
  have hletDone :
      ExecStmt (config v) stFrame evmPrice
        (.letDecl "done" (some boolTy) (tuple0 (.var "st")))
        (.ok doneFrame evmPrice) := by
    simpa [stFrame, doneFrame, clipperTakeLocalsDone] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := stFrame) (evm := evmPrice) (name := "done")
        (ty := some boolTy) (expr := tuple0 (.var "st")) (value := .bool false)
        (by simpa [stFrame] using
          clipperEvalTakeDoneFromStatusAt v evmLock evmPrice I false price))
  have hletPrice :
      ExecStmt (config v) doneFrame evmPrice
        (.letDecl "price" (some uint256) (tuple1 (.var "st")))
        (.ok priceFrame evmPrice) := by
    simpa [doneFrame, priceFrame, clipperTakeLocalsPrice] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := doneFrame) (evm := evmPrice) (name := "price")
        (ty := some uint256) (expr := tuple1 (.var "st"))
        (value := .int (Int.ofNat price.toNat))
        (by simpa [doneFrame] using
          clipperEvalTakePriceFromStatusAt v evmLock evmPrice I false price))
  have hdoneEval :
      evalExpr? (config v) priceFrame evmPrice (.unary .not (.var "done")) =
        .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeNotDone_true v evmLock evmPrice I price
  have hmaxEval :
      evalExpr? (config v) priceFrame evmPrice
        (.binary .ge (.var "max") (.var "price")) = .ok (.bool true) := by
    simpa [priceFrame] using clipperEvalTakeMaxGePrice_true v evmLock evmPrice I price hmax
  have hletLot :
      ExecStmt (config v) priceFrame evmPrice
        (.letDecl "lot" (some uint256) (.storage (salesF (.var "id") "lot")))
        (.ok lotFrame evmPrice) := by
    simpa [priceFrame, lotFrame, lot, clipperTakeLocalsLot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := priceFrame) (evm := evmPrice) (name := "lot")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "lot"))
        (value := .int (Int.ofNat lot.toNat))
        (by simpa [priceFrame, lot] using
          clipperEvalTakeSalesLotAtPrice v evmLock evmPrice I false price))
  have hletTab :
      ExecStmt (config v) lotFrame evmPrice
        (.letDecl "tab" (some uint256) (.storage (salesF (.var "id") "tab")))
        (.ok tabFrame evmPrice) := by
    simpa [lotFrame, tabFrame, tab, clipperTakeLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := lotFrame) (evm := evmPrice) (name := "tab")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "tab"))
        (value := .int (Int.ofNat tab.toNat))
        (by simpa [lotFrame, tab] using
          clipperEvalTakeSalesTabAfterLot v evmLock evmPrice I false price))
  have hminCall :
      ExecStmt (config v) tabFrame evmPrice
        (.internalCall "min" [.var "lot", .var "amt"] "slice")
        (.ok sliceFrame evmPrice) := by
    simpa [tabFrame, sliceFrame, slice, lot, resumeAfterInternalCall,
      clipperTakeLocalsSlice] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := tabFrame) (evm := evmPrice) (calleeEvm := evmPrice)
        (name := "min") (retVar := "slice")
        (args := [.var "lot", .var "amt"])
        (argVals := [.int (Int.ofNat lot.toNat),
          .int (Int.ofNat (clipperTakeAmtWord I).toNat)])
        (callee := minFunction)
        (locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I))
        (calleeSolm :=
          { contract := contract v, locals := clipperUintBinaryLocals lot (clipperTakeAmtWord I) })
        (value := some [.int (Int.ofNat (clipperMinWord lot (clipperTakeAmtWord I)).toNat)])
        (by simpa [tabFrame, lot] using
          clipperEvalTakeMinArgsAtTab v evmLock evmPrice I false price)
        (clipperLookupMinFunction v)
        (clipperBindParamsMin lot (clipperTakeAmtWord I))
        (by simpa [tabFrame] using
          clipperMinFunctionReturns v evmPrice lot (clipperTakeAmtWord I)))
  have htail :
      ExecBlock (config v) sliceFrame evmPrice
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [ .letDecl "owe" (some uint256) (.var "owe0"),
            .ite
              (.binary .gt (.var "owe") (.var "tab"))
              [ .assign .localVar (varRef "owe") (.var "tab"),
                .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
              [ .ite
                (.binary .and (.binary .lt (.var "owe") (.var "tab"))
                  (.binary .lt (.var "slice") (.var "lot")))
                ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
                  wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
                  [ .ite
                    (.binary .lt (.var "remainingTab") (.var "_chost"))
                    ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                      wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                      [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                        .assign .localVar (varRef "slice")
                          (.binary .div (.var "owe") (.var "price")) ])
                    [] ])
                [] ] ] ++
          wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ] ++
          checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [sliceFrame, slice, lot, tab] using
      clipperTakeOweGtTabVatFluxNoCodeTailBlock v evmLock evmPrice I price slice
        hmul hgt hsliceLot hnoVatCode
  have hblock :
      ExecBlock (config v) startFrame evm0 (takeTransition v).body .reverted := by
    simpa [takeTransition, nonpayable, lockPrefix, isStopped, startFrame,
      checkedMulUintInto, List.append_assoc] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        refine ExecBlock.consNormal hletDone ?_
        refine ExecBlock.consNormal hletPrice ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdoneEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hmaxEval) ?_
        refine ExecBlock.consNormal hletLot ?_
        refine ExecBlock.consNormal hletTab ?_
        refine ExecBlock.consNormal hminCall ?_
        exact execBlockAppendReverted htail)
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperTakeVatFluxBuyerCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outVat : ByteArray}
    {argVals : List Value}
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0 argVals
        (false, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
          tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) := by
    exact clipperEvalTakeVatCodeGuard_true v evmRead
      (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
        tabNew lotNew) hvatCode
  simpa [checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      (ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (clipperEvalVat v evmRead
            (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe
              slice' tabNew lotNew))
          (by simp [evalExpr?, pure]) hargs hcallVat)))

theorem clipperTakeOweGtTabVatFluxCallFailureTailBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv) (price slice : UInt256)
    {outVat : ByteArray}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt :
      (clipperTakeSalesTabEVMWord evmRead I).toNat <
        (UInt256.mul slice price).toNat)
    (hsliceLot :
      (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat ≤
        (clipperTakeSalesLotEVMWord evmRead I).toNat)
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmRead.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price).toNat)]
        (false, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsSlice evmLoc evmRead I false price slice))
      evmRead
      (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
        [ .letDecl "owe" (some uint256) (.var "owe0"),
          .ite
            (.binary .gt (.var "owe") (.var "tab"))
            [ .assign .localVar (varRef "owe") (.var "tab"),
              .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
            [ .ite
              (.binary .and (.binary .lt (.var "owe") (.var "tab"))
                (.binary .lt (.var "slice") (.var "lot")))
              ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
                wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
                [ .ite
                  (.binary .lt (.var "remainingTab") (.var "_chost"))
                  ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                    wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                    [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                      .assign .localVar (varRef "slice")
                        (.binary .div (.var "owe") (.var "price")) ])
                  [] ])
              [] ] ] ++
        wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
        wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
        [ .assign .localVar (varRef "tab") (.var "tabNew"),
          .assign .localVar (varRef "lot") (.var "lotNew") ] ++
        checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      .reverted := by
  let owe0 := UInt256.mul slice price
  let slice' := UInt256.div (clipperTakeSalesTabEVMWord evmRead I) price
  let tabNew := UInt256.sub (clipperTakeSalesTabEVMWord evmRead I)
    (clipperTakeSalesTabEVMWord evmRead I)
  let lotNew := UInt256.sub (clipperTakeSalesLotEVMWord evmRead I) slice'
  let sliceFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsSlice evmLoc evmRead I false price slice)
  let oweFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOwe evmLoc evmRead I false price slice owe0 owe0)
  let adjustedFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsOweTabSlice evmLoc evmRead I false price slice owe0 owe0 slice')
  let postSubFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe0 slice'
        tabNew lotNew)
  have hmulBlock :
      ExecBlock (config v) sliceFrame evmRead
        (checkedMulUintInto "owe0" (.var "slice") (.var "price") ++
          [.letDecl "owe" (some uint256) (.var "owe0")])
        (.ok oweFrame evmRead) := by
    simpa [sliceFrame, oweFrame, owe0] using
      clipperTakeOwe0MulSuccessBlock v evmLoc evmRead I price slice hmul
  have hite :
      ExecStmt (config v) oweFrame evmRead
        (.ite
          (.binary .gt (.var "owe") (.var "tab"))
          [ .assign .localVar (varRef "owe") (.var "tab"),
            .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
          [ .ite
            (.binary .and (.binary .lt (.var "owe") (.var "tab"))
              (.binary .lt (.var "slice") (.var "lot")))
            ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
              wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
              [ .ite
                (.binary .lt (.var "remainingTab") (.var "_chost"))
                ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                  wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                  [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                    .assign .localVar (varRef "slice")
                      (.binary .div (.var "owe") (.var "price")) ])
                [] ])
            [] ])
        (.ok adjustedFrame evmRead) := by
    simpa [oweFrame, adjustedFrame, owe0, slice'] using
      clipperTakeOweGtTabIte v evmLoc evmRead I price slice hgt
  have hsubBlock :
      ExecBlock (config v) adjustedFrame evmRead
        (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
          wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
          [ .assign .localVar (varRef "tab") (.var "tabNew"),
            .assign .localVar (varRef "lot") (.var "lotNew") ])
        (.ok postSubFrame evmRead) := by
    simpa [adjustedFrame, postSubFrame, slice', tabNew, lotNew] using
      clipperTakePostOweGtTabSubBlock v evmLoc evmRead I price slice owe0 hsliceLot
  have hargs :
      evalExprs? (config v) postSubFrame evmRead
        [ilkExpr v, thisAddr, .var "who", .var "slice"] =
          .ok
            [v.ilk, .address evmRead.executionEnv.codeOwner,
              .address (AccountAddress.ofNat
                (UInt256.land (clipperTakeWhoWord I) solcAddrMask).toNat),
              .int (Int.ofNat slice'.toNat)] := by
    simpa [postSubFrame, slice'] using
      clipperEvalTakeVatFluxBuyerArgs v evmLoc evmRead I price slice owe0 owe0 slice'
        tabNew lotNew
  have hvatRevert :
      ExecBlock (config v) postSubFrame evmRead
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
        .reverted := by
    simpa [postSubFrame, slice'] using
      clipperTakeVatFluxBuyerCallFailureBlock v evmLoc evmRead evmVat I price slice owe0
        owe0 slice' tabNew lotNew hvatCode hargs hcallVat
  have hafterIte :
      ExecBlock (config v) oweFrame evmRead
        (.ite
          (.binary .gt (.var "owe") (.var "tab"))
          [ .assign .localVar (varRef "owe") (.var "tab"),
            .assign .localVar (varRef "slice") (.binary .div (.var "owe") (.var "price")) ]
          [ .ite
            (.binary .and (.binary .lt (.var "owe") (.var "tab"))
              (.binary .lt (.var "slice") (.var "lot")))
            ([ .letDecl "_chost" (some uint256) (.storage chostRef) ] ++
              wrappingSubInto "remainingTab" (.var "tab") (.var "owe") ++
              [ .ite
                (.binary .lt (.var "remainingTab") (.var "_chost"))
                ([ .require (.binary .gt (.var "tab") (.var "_chost")) ] ++
                  wrappingSubInto "oweAdjusted" (.var "tab") (.var "_chost") ++
                  [ .assign .localVar (varRef "owe") (.var "oweAdjusted"),
                    .assign .localVar (varRef "slice")
                      (.binary .div (.var "owe") (.var "price")) ])
                [] ])
            [] ] ::
          (wrappingSubInto "tabNew" (.var "tab") (.var "owe") ++
            wrappingSubInto "lotNew" (.var "lot") (.var "slice") ++
            [ .assign .localVar (varRef "tab") (.var "tabNew"),
              .assign .localVar (varRef "lot") (.var "lotNew") ] ++
            checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
              [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet"))
        .reverted := by
    exact ExecBlock.consNormal hite (execBlockAppendRevert hsubBlock hvatRevert)
  simpa [sliceFrame, List.append_assoc] using execBlockAppendRevert hmulBlock hafterIte

theorem clipperTakeVatFluxBuyerCallSuccessBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outVat : ByteArray}
    {argVals : List Value}
    (hvatCode :
      0 <
        (UInt256.ofNat ((evmRead.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hargs :
      evalExprs? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead [ilkExpr v, thisAddr, .var "who", .var "slice"] = .ok argVals)
    (hcallVat :
      typedCallViaEVM (config v) evmRead (EVM.address v.vat) "flux" 0 argVals
        (true, evmVat, outVat) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
          tabNew lotNew))
      evmRead
      (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
        [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet")
      (.ok
        (Frame.mk (contract v)
          (clipperTakeLocalsFluxBuyerRet evmLoc evmRead I price slice owe0 owe slice'
            tabNew lotNew))
        evmVat) := by
  have hguard :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
            tabNew lotNew))
        evmRead (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) := by
    exact clipperEvalTakeVatCodeGuard_true v evmRead
      (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe slice'
        tabNew lotNew) hvatCode
  simpa [checkedExternalCallStmts, clipperTakeLocalsFluxBuyerRet, collapseReturns] using
    (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalVat v evmRead
            (clipperTakeLocalsLotAssigned evmLoc evmRead I false price slice owe0 owe
              slice' tabNew lotNew))
          (by simp [evalExpr?, pure]) hargs hcallVat
          (clipperTakeDecodeFluxVoid v outVat))
        ExecBlock.nil))

end Benchmarks.Dss.Clipper
