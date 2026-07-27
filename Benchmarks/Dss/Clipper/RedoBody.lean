import Benchmarks.Dss.Clipper.Redo
import Benchmarks.Dss.Clipper.RedoDoneSource
import Benchmarks.Dss.Clipper.GetStatus
import Benchmarks.Dss.Clipper.GetFeedPrice
import Benchmarks.Dss.Clipper.StatusPriceCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperRedoBodyJumpDest7575 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7575⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 8000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperRedoBodyJumpDest7651 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7651⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 8000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperRedoBodyJumpDest8728 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8728⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperRedoStatusCallRevertsAgeForDone (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256)
    {out : ByteArray}
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hltDone : (clipperTimestampWord evmPrice).toNat <
      (clipperRedoSalesTicEVMWord evm I).toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .var "top"])
    (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperEvalRedoStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsAgeForDone v
      (clipperRedoSalesTicEVMWord evm I) (clipperRedoSalesTopEVMWord evm I) price
      hlePrice hcode hcall hdec hltDone)

theorem clipperRedoStatusCallRevertsRdivMul (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256)
    {out : ByteArray}
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperRedoSalesTicEVMWord evm I).toNat ≤
      (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperRedoSalesTicEVMWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hover : UInt256.size ≤ price.toNat * clipperRayWord.toNat) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .var "top"])
    (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperEvalRedoStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsRdivMul v
      (clipperRedoSalesTicEVMWord evm I) (clipperRedoSalesTopEVMWord evm I) price
      hlePrice hcode hcall hdec hleDone htail hover)

theorem clipperRedoStatusCallRevertsRdivDivZero (v : ClipperImmutables)
    {evm evmPrice : EVM.State} (I : ExecutionEnv) (price : UInt256)
    {out : ByteArray}
    (hlePrice : (clipperRedoSalesTicEVMWord evm I).toNat ≤ (clipperTimestampWord evm).toNat)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount (clipperStatusCalcAddress evm)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) evm (EVM.address (clipperStatusCalcAddress evm))
        "price" 0
        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat),
          .int (Int.ofNat
            (UInt256.sub (clipperTimestampWord evm) (clipperRedoSalesTicEVMWord evm I)).toNat)]
        (true, evmPrice, out) false)
    (hdec : (config v).externalABI.decode? "price" out =
      some [.int (Int.ofNat price.toNat)])
    (hleDone : (clipperRedoSalesTicEVMWord evm I).toNat ≤
      (clipperTimestampWord evmPrice).toNat)
    (htail :
      (UInt256.sub (clipperTimestampWord evmPrice) (clipperRedoSalesTicEVMWord evm I)).toNat ≤
        (clipperStatusTailWord evmPrice).toNat)
    (hmul : price.toNat * clipperRayWord.toNat < UInt256.size)
    (htop : clipperRedoSalesTopEVMWord evm I = ⟨0⟩) :
    ExecStmt (config v)
      { contract := contract v, locals := clipperRedoLocalsTop evm I } evm
      (.internalCall "status" [.var "tic", .var "top"] "st")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config v)
    (caller := { contract := contract v, locals := clipperRedoLocalsTop evm I })
    (evm := evm)
    (name := "status") (retVar := "st")
    (args := [.var "tic", .var "top"])
    (argVals := [.int (Int.ofNat (clipperRedoSalesTicEVMWord evm I).toNat),
      .int (Int.ofNat (clipperRedoSalesTopEVMWord evm I).toNat)])
    (callee := statusFunction)
    (locals := clipperStatusLocals (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperEvalRedoStatusArgs v evm I)
    (clipperLookupStatusFunction v)
    (clipperBindParamsStatus (clipperRedoSalesTicEVMWord evm I)
      (clipperRedoSalesTopEVMWord evm I))
    (clipperStatusFunctionRevertsRdivDivZero v
      (clipperRedoSalesTicEVMWord evm I) (clipperRedoSalesTopEVMWord evm I) price
      hlePrice hcode hcall hdec hleDone htail hmul htop)

theorem clipperRedoStatusSourceRevertsOfStatus {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st") .reverted) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  intro locals evm0
  let evmLock := clipperRedoLockedState evm0
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperRedoLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTic evmLock I }
  let topFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
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
    simpa [startFrame, locals, evmLock, clipperRedoLockedState] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool true) := by
    apply evalExpr_clipperRedoStopped_lt_two_true
    · simp [locals]
    · simpa [evmLock, clipperRedoLockedState, evm0, initState, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
        storageStore_executionEnv] using hstopped
  have husrLoad : clipperRedoSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperRedoSalesUsrEVMWord, clipperRedoSalesUsrWord, evmLock,
      clipperRedoLockedState, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperRedoLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalRedoSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperRedoLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperRedoSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalRedoSalesTicAfterUsr v evmLock I))
  have hletTop :
      ExecStmt (config v) ticFrame evmLock
        (.letDecl "top" (some uint256) (.storage (salesF (.var "id") "top")))
        (.ok topFrame evmLock) := by
    simpa [ticFrame, topFrame, clipperRedoLocalsTop] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := ticFrame) (evm := evmLock) (name := "top")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "top"))
        (value := .int (Int.ofNat (clipperRedoSalesTopEVMWord evmLock I).toNat))
        (by simpa [ticFrame] using clipperEvalRedoSalesTopAfterTic v evmLock I))
  have husrEval :
      evalExpr? (config v) topFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [topFrame] using clipperEvalRedoUsrNeZeroAfterTop_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) topFrame evmLock
        (.internalCall "status" [.var "tic", .var "top"] "st") .reverted := by
    simpa [topFrame, evmLock, evm0] using hstatus
  have hblock :
      ExecBlock (config v) startFrame evm0 (redoTransition v).body .reverted := by
    simpa [redoTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal hletTop ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        exact ExecBlock.consRevert hstatus')
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem clipperRedoStatusFalseSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hstopped :
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 2)
    (husr :
      clipperRedoSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    {evmPrice : EVM.State} (price : UInt256)
    (hstatus :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      let evmLock := clipperRedoLockedState evm0
      ExecStmt (config v) { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok { contract := contract v, locals := clipperRedoLocalsSt evmLock I false price }
          evmPrice)) :
    let locals := clipperRedoStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (redoTransition v).body .reverted := by
  intro locals evm0
  let evmLock := clipperRedoLockedState evm0
  let startFrame : Frame := { contract := contract v, locals := locals }
  let usrFrame : Frame := { contract := contract v, locals := clipperRedoLocalsUsr evmLock I }
  let ticFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTic evmLock I }
  let topFrame : Frame := { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
  let stFrame : Frame := { contract := contract v, locals := clipperRedoLocalsSt evmLock I false price }
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
    simpa [startFrame, locals, evmLock, clipperRedoLockedState] using
      assign_clipperLocked v evm0 locals (by simp [locals]) ⟨1⟩
  have hstoppedEval :
      evalExpr? (config v) startFrame evmLock
        (.binary .lt (.storage stoppedRef) (.intLit 2)) = .ok (.bool true) := by
    apply evalExpr_clipperRedoStopped_lt_two_true
    · simp [locals]
    · simpa [evmLock, clipperRedoLockedState, evm0, initState, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, storageStore_accountMap,
        storageStore_executionEnv] using hstopped
  have husrLoad : clipperRedoSalesUsrEVMWord evmLock I ≠ ⟨0⟩ := by
    simpa [clipperRedoSalesUsrEVMWord, clipperRedoSalesUsrWord, evmLock,
      clipperRedoLockedState, evm0, initState, solcSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, storageStore_accountMap, storageStore_executionEnv] using husr
  have hletUsr :
      ExecStmt (config v) startFrame evmLock
        (.letDecl "usr" (some addr) (.storage (salesF (.var "id") "usr")))
        (.ok usrFrame evmLock) := by
    simpa [startFrame, usrFrame, locals, clipperRedoLocalsUsr] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := startFrame) (evm := evmLock) (name := "usr")
        (ty := some addr) (expr := .storage (salesF (.var "id") "usr"))
        (value := .address (AccountAddress.ofNat (clipperRedoSalesUsrEVMWord evmLock I).toNat))
        (by simpa [startFrame, locals] using clipperEvalRedoSalesUsr v evmLock I))
  have hletTic :
      ExecStmt (config v) usrFrame evmLock
        (.letDecl "tic" (some uint96) (.storage (salesF (.var "id") "tic")))
        (.ok ticFrame evmLock) := by
    simpa [usrFrame, ticFrame, clipperRedoLocalsTic] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := usrFrame) (evm := evmLock) (name := "tic")
        (ty := some uint96) (expr := .storage (salesF (.var "id") "tic"))
        (value := .int (Int.ofNat (clipperRedoSalesTicEVMWord evmLock I).toNat))
        (by simpa [usrFrame] using clipperEvalRedoSalesTicAfterUsr v evmLock I))
  have hletTop :
      ExecStmt (config v) ticFrame evmLock
        (.letDecl "top" (some uint256) (.storage (salesF (.var "id") "top")))
        (.ok topFrame evmLock) := by
    simpa [ticFrame, topFrame, clipperRedoLocalsTop] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := ticFrame) (evm := evmLock) (name := "top")
        (ty := some uint256) (expr := .storage (salesF (.var "id") "top"))
        (value := .int (Int.ofNat (clipperRedoSalesTopEVMWord evmLock I).toNat))
        (by simpa [ticFrame] using clipperEvalRedoSalesTopAfterTic v evmLock I))
  have husrEval :
      evalExpr? (config v) topFrame evmLock (.binary .ne (.var "usr") zeroAddr) =
        .ok (.bool true) := by
    simpa [topFrame] using clipperEvalRedoUsrNeZeroAfterTop_true v evmLock I husrLoad
  have hstatus' :
      ExecStmt (config v) topFrame evmLock
        (.internalCall "status" [.var "tic", .var "top"] "st")
        (.ok stFrame evmPrice) := by
    simpa [topFrame, stFrame, evmLock, evm0] using hstatus
  have hdoneEval :
      evalExpr? (config v) stFrame evmPrice (tuple0 (.var "st")) = .ok (.bool false) := by
    simpa [stFrame] using clipperEvalRedoDoneFromStatusAt v evmLock evmPrice I false price
  have hblock :
      ExecBlock (config v) startFrame evm0 (redoTransition v).body .reverted := by
    simpa [redoTransition, nonpayable, lockPrefix, isStopped, startFrame] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hstoppedEval) ?_
        refine ExecBlock.consNormal hletUsr ?_
        refine ExecBlock.consNormal hletTic ?_
        refine ExecBlock.consNormal hletTop ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal hstatus' ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse hdoneEval))
  simpa [ExecTransitionBody, startFrame, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

abbrev clipperRedoNotFinishedRawWord : UInt256 :=
  ⟨96230011794421689713427538471044131063057930589⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperRedoStatusFalseReverts {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price top tic usr kpr id sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨7575⟩
      (price :: ⟨0⟩ :: ⟨0⟩ :: top :: tic :: usr :: ⟨2⟩ :: kpr :: id :: ⟨502⟩ :: [sel])
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev code g s0 := by
  have rd7584 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7651⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiNT (by clipper_runtime_decode) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by evm_ov)]
  have rdMload := evm_run rd7584 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨20⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨20⟩ mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst clipperRedoNotFinishedRawWord
    (width := 20) (op := .PUSH20) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨98⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨20⟩ (UInt256.shiftLeft clipperRedoNotFinishedRawWord ⟨98⟩)
        mem)
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (solcErrorStringMem3_mload64_of_size196 ⟨20⟩
        (UInt256.shiftLeft clipperRedoNotFinishedRawWord ⟨98⟩) hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

theorem RD.clipperRedoStatusTrueToDoneBranch {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price top tic usr kpr id sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨7575⟩
      (price :: ⟨1⟩ :: ⟨0⟩ :: top :: tic :: usr :: ⟨2⟩ :: kpr :: id :: ⟨502⟩ :: [sel])
      mem (UInt256.ofNat 7) rdata (cA, σ) k C) :
    ∃ k' C', RD code ee g s0 ⟨7651⟩
      (⟨1⟩ :: top :: tic :: usr :: ⟨2⟩ :: kpr :: id :: ⟨502⟩ :: [sel])
      mem (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  have hdone : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by decide
  exact ⟨_, _, by
    simpa using
      (evm_run h with [
        raw jumpdest (by clipper_runtime_decode) (by evm_ov),
        raw pop (by clipper_runtime_decode) (by evm_ov),
        raw swap1 (by clipper_runtime_decode) (by evm_ov),
        raw pop (by clipper_runtime_decode) (by evm_ov),
        raw dup1 (by clipper_runtime_decode) (by evm_ov),
        raw push2 ⟨7651⟩ (by clipper_runtime_decode) (by evm_ov),
        raw jumpiT (by clipper_runtime_decode) hdone
          (clipperRedoBodyJumpDest7651 v hpatch) (by evm_ov)])⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperRedoDoneBranchToGetFeedPrice {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {top tic usr kpr id sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨7651⟩
      (⟨1⟩ :: top :: tic :: usr :: ⟨2⟩ :: kpr :: id :: ⟨502⟩ :: [sel])
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hmem : 64 ≤ mem.size) :
    let base : UInt256 := solcMappingSlot ⟨12⟩ id
    let packedSlot : UInt256 := base + ⟨3⟩
    let updatedPacked : UInt256 :=
      UInt256.lor
        (UInt256.mul
          (UInt256.land clipperSalesUint96Mask (UInt256.ofNat ee.header.timestamp))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
        (UInt256.land solcAddrMask (solcSlotWord σ ee packedSlot))
    ∃ k' C', RD code ee g s0 ⟨8728⟩
      (⟨7719⟩ :: ⟨0⟩ :: solcSlotWord σ ee (base + ⟨2⟩) ::
        solcSlotWord σ ee (base + ⟨1⟩) :: ⟨1⟩ :: top :: tic :: usr :: ⟨2⟩ ::
        kpr :: id :: ⟨502⟩ :: [sel])
      (twoWordHashMem id ⟨12⟩ mem) (UInt256.ofNat 7) rdata
      (cA, sstoreAccountMap ee.codeOwner σ packedSlot updatedPacked) k' C' := by
  intro base packedSlot updatedPacked
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem id (⟨12⟩ : UInt256) mem).readWithPadding 0 64))) =
        base := by
    simpa [base] using twoWordHashMem_solcMappingSlot_of_ge (⟨12⟩ : UInt256) id hmem
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hmask96 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩ =
        clipperSalesUint96Mask := by
    native_decide
  have rdHash := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (twoWordHashMem id (⟨12⟩ : UInt256) mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
      hslot (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdTab⟩ := rdHash.sload (by clipper_runtime_decode) (by evm_ov)
  have rdLotSlot := evm_run rdTab with [
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdLot⟩ := rdLotSlot.sload (by clipper_runtime_decode) (by evm_ov)
  have rdPackedSlot := evm_run rdLot with [
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show base + ⟨3⟩ = packedSlot from rfl] at rdPackedSlot
  obtain ⟨_, _, rdPacked⟩ := rdPackedSlot.sload (by clipper_runtime_decode) (by evm_ov)
  have rdUpdate := evm_run rdPacked with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw mul (by clipper_runtime_decode) (by evm_ov),
    raw lor (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [haddrMask, hmask96] at rdUpdate
  obtain ⟨_, _, rdStore⟩ := rdUpdate.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  have rdJump := evm_run rdStore with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨7719⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8728⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperRedoBodyJumpDest8728 v hpatch) (by evm_ov)]
  exact ⟨_, _, by
    simpa [base, packedSlot, updatedPacked, solcSlotWord, u256_add_comm] using rdJump⟩

theorem clipperRedoBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 16))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 16) (by native_decide) hsel
  have hdispatch := clipperDispatch_redo v hsel
  have hreachEntry := clipperReachRedoBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · obtain ⟨_, _, hreachBody⟩ := clipperRedoX_decoded
      (v := v) (g := Sat256.ofUInt256 g) hpatch hsz68 hsize hreachEntry
    by_cases hlockedEvm : solcSlotWord σ_evm I ⟨13⟩ = ⟨0⟩
    · obtain ⟨_, _, hreachOpen⟩ := clipperRedoX_lockOpen
        (v := v) hpatch hlockedEvm hreachBody
      obtain ⟨_, _, hreachLocked⟩ := clipperRedoX_lockStore
        (v := v) hpatch hperm hreachOpen
      have hlockWord : solcSlotWord σ_evm I ⟨13⟩ = solcSlotWord σ_solm I ⟨13⟩ := by
        simpa [solcSlotWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner (⟨13⟩ : UInt256) ⟨0⟩
      have hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩ := by
        rw [← hlockWord]
        exact hlockedEvm
      let σLockEvm := sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩
      let σLockSolm := sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩
      have hAccountsLock : accountMapEquiv σLockEvm σLockSolm := by
        simpa [σLockEvm, σLockSolm] using
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts
      have hstoppedWord :
          solcSlotWord σLockEvm I ⟨14⟩ = solcSlotWord σLockSolm I ⟨14⟩ := by
        simpa [solcSlotWord] using
          accountMapEquiv_storage_findD hAccountsLock I.codeOwner (⟨14⟩ : UInt256) ⟨0⟩
      by_cases hstoppedLt : (solcSlotWord σLockEvm I ⟨14⟩).toNat < 2
      · have hstoppedSolmLt : (solcSlotWord σLockSolm I ⟨14⟩).toNat < 2 := by
          rw [← hstoppedWord]
          exact hstoppedLt
        obtain ⟨_, _, _hreachStopped⟩ := clipperRedoX_stoppedOpen (v := v)
          (σ := σLockEvm) hpatch (by simpa [σLockEvm] using hstoppedLt)
          (by simpa [σLockEvm] using hreachLocked)
        have husrWord :
            clipperRedoSalesUsrWord σLockEvm I = clipperRedoSalesUsrWord σLockSolm I := by
          unfold clipperRedoSalesUsrWord solcSlotWord
          rw [accountMapEquiv_storage_findD hAccountsLock I.codeOwner
            (clipperRedoSalesPackedSlot I) ⟨0⟩]
        by_cases husrEvm : clipperRedoSalesUsrWord σLockEvm I = ⟨0⟩
        · have husrSolm : clipperRedoSalesUsrWord σLockSolm I = ⟨0⟩ := by
            rw [← husrWord]
            exact husrEvm
          let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hbody :
              ExecTransitionBody (config v) (contract v) evmSolm (clipperRedoStore I)
                (redoTransition v).body .reverted := by
            simpa [evmSolm, σLockSolm] using
              (clipperRedoInactiveSourceReverts (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                hlockedSolm hstoppedSolmLt husrSolm)
          have hrev := clipperRedoX_usrZero (v := v) (σ := σLockEvm)
            hpatch husrEvm (by simpa [σLockEvm] using _hreachStopped)
          exact hrev.reEquivExecutionRevert hcode hdispatch (clipperDecode_redo_ok v hsz68)
            hbody
        · have husrSolm : clipperRedoSalesUsrWord σLockSolm I ≠ ⟨0⟩ := by
            intro hzero
            exact husrEvm (by rw [husrWord, hzero])
          obtain ⟨_, _, _hreachUsr⟩ := clipperRedoX_usrNonzero (v := v)
            (σ := σLockEvm) hpatch husrEvm (by simpa [σLockEvm] using _hreachStopped)
          obtain ⟨_, _, _hreachStatus⟩ := clipperRedoX_enterStatus (v := v)
            (σ := σLockEvm) hpatch _hreachUsr
          have hpackedWord :
              solcSlotWord σLockEvm I (clipperRedoSalesPackedSlot I) =
                solcSlotWord σLockSolm I (clipperRedoSalesPackedSlot I) := by
            simpa [solcSlotWord] using
              accountMapEquiv_storage_findD hAccountsLock I.codeOwner
                (clipperRedoSalesPackedSlot I) ⟨0⟩
          have hticWord :
              clipperRedoSalesTicWord σLockEvm I = clipperRedoSalesTicWord σLockSolm I := by
            simpa [clipperRedoSalesTicWord] using congrArg
              (fun w =>
                UInt256.land
                  (UInt256.div w (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
                  (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩))
              hpackedWord
          have hmask96 : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by
            native_decide
          have hticLt : (clipperRedoSalesTicWord σLockEvm I).toNat < EVM.twoPow 96 := by
            simpa [clipperRedoSalesTicWord, clipperSalesUint96Mask] using
              u256LandMaskToNatLtOfToNat
                (UInt256.div (solcSlotWord σLockEvm I (clipperRedoSalesPackedSlot I))
                  (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
                clipperSalesUint96Mask hmask96
          have hticClean :
              UInt256.land (clipperRedoSalesTicWord σLockEvm I) clipperSalesUint96Mask =
                clipperRedoSalesTicWord σLockEvm I := by
            exact u256LandMaskCleanOfToNat
              (clipperRedoSalesTicWord σLockEvm I) clipperSalesUint96Mask hmask96 hticLt
          have hticCleanSolm :
              UInt256.land (clipperRedoSalesTicWord σLockSolm I) clipperSalesUint96Mask =
                clipperRedoSalesTicWord σLockSolm I := by
            rw [← hticWord]
            exact hticClean
          by_cases hlePrice :
              (clipperRedoSalesTicWord σLockEvm I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat
          · let calcAddr : UInt256 := UInt256.land (solcSlotWord σLockEvm I ⟨4⟩) solcAddrMask
            obtain ⟨_, _, rd8502⟩ :=
              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPrice
                (v := v) hpatch _hreachStatus
                (by simpa [hticClean] using hlePrice)
                (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨_, _, rd8549⟩ :=
              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceExtcodesizeGuard
                (v := v) hpatch (by simpa [calcAddr] using rd8502)
                (mloadFreePtrValue (by rw [clipperRedoSalesHashMem_size I]; decide)
                  (by decide) (clipperRedoSalesHashMem_read64 I))
                (clipperRedoSalesHashMem_size I)
                (clipperRedoSalesHashMem_read64 I)
                (by simp only [List.length_cons, List.length_nil]; omega)
            let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            let evmLockSolm := clipperRedoLockedState evmSolm
            have hcalcSlotSolm :
                solcSlotWord σLockEvm I ⟨4⟩ = solcSlotWord σLockSolm I ⟨4⟩ := by
              exact accountMapEquiv_storage_findD (σ := σLockEvm) (τ := σLockSolm)
                hAccountsLock I.codeOwner ⟨4⟩ (⟨0⟩ : UInt256)
            have hticSolmLoad :
                clipperRedoSalesTicEVMWord evmLockSolm I =
                  clipperRedoSalesTicWord σLockSolm I := by
              simp [σLockSolm, evmLockSolm, evmSolm, clipperRedoLockedState, initState,
                clipperRedoSalesTicEVMWord, clipperRedoSalesTicWord, Solm.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage, solcSlotWord,
                storageStore_accountMap, storageStore_executionEnv]
            have htimestampSolm :
                clipperTimestampWord evmLockSolm = UInt256.ofNat I.header.timestamp := by
              simp [evmLockSolm, evmSolm, clipperRedoLockedState, initState,
                clipperTimestampWord, storageStore_executionEnv]
            have hlePriceSolm :
                (clipperRedoSalesTicEVMWord evmLockSolm I).toNat ≤
                  (clipperTimestampWord evmLockSolm).toNat := by
              simpa [hticSolmLoad, htimestampSolm, hticWord] using hlePrice
            by_cases hcalcCode :
                Reasoning.Theory.uniswapExtCodeSizeWord σLockEvm calcAddr ≠ ⟨0⟩
            · have htopWord :
                  clipperRedoSalesTopWord σLockEvm I =
                    clipperRedoSalesTopWord σLockSolm I := by
                simpa [clipperRedoSalesTopWord, solcSlotWord] using
                  accountMapEquiv_storage_findD hAccountsLock I.codeOwner
                    (clipperRedoSalesTopSlot I) (⟨0⟩ : UInt256)
              have htopSolmLoad :
                  clipperRedoSalesTopEVMWord evmLockSolm I =
                    clipperRedoSalesTopWord σLockSolm I := by
                simp [σLockSolm, evmLockSolm, evmSolm, clipperRedoLockedState, initState,
                  clipperRedoSalesTopEVMWord, clipperRedoSalesTopWord, Solm.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage, solcSlotWord,
                  storageStore_accountMap, storageStore_executionEnv]
              have hcalcAddrSolm :
                  clipperStatusCalcAddress evmLockSolm = AccountAddress.ofUInt256 calcAddr := by
                simp [σLockSolm, evmLockSolm, evmSolm, clipperRedoLockedState,
                  clipperStatusCalcAddress, clipperStatusCalcWord, calcAddr, initState,
                  Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                  solcSlotWord, storageStore_accountMap, storageStore_executionEnv,
                  hcalcSlotSolm]
              have hcalcCodeSolmNE :
                  Reasoning.Theory.uniswapExtCodeSizeWord σLockSolm calcAddr ≠ ⟨0⟩ := by
                intro hzero
                exact hcalcCode (by
                  rw [Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv
                    hAccountsLock calcAddr]
                  exact hzero)
              have hcalcCodeSolm :
                  0 < (UInt256.ofNat
                    ((evmLockSolm.lookupAccount (clipperStatusCalcAddress evmLockSolm)).option 0
                      (fun acc => acc.code.size))).toNat := by
                simpa [σLockSolm, evmLockSolm, evmSolm, clipperRedoLockedState,
                  State.lookupAccount, initState, storageStore_accountMap] using
                  clipperGetStatusExtCodeSizeWord_ne_zero_lookup_code_pos
                    (σ := σLockSolm) (target := calcAddr)
                    (addr := clipperStatusCalcAddress evmLockSolm)
                    hcalcAddrSolm hcalcCodeSolmNE
              by_cases hdepth : I.depth.val < 1024
              · obtain ⟨cA', σ', z, o, A', k8565, C8565, rd8565, hcallPrice, hout⟩ :=
                  RD.clipperStatusPricePostStaticcallFromCurrent
                    (v := v) (cA := cA) (gh := gh) (bl := bl)
                    (σ := σLockEvm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hpatch rd8549
                    (by simp [initState])
                    (by simp [initState])
                    (by simp [initState])
                    (by simpa [calcAddr] using hcalcCode)
                    hdepth
                    (clipperRedoSalesHashMem_size I)
                    (by simp only [List.length_cons, List.length_nil]; omega)
                cases z
                · have hrev :=
                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallFailure
                      (v := v) hpatch (by simpa using rd8565) hout
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  obtain ⟨σ'_solm, A'_solm, hcallPriceSolmRaw, _hPostAccounts⟩ :=
                    typedCallViaEVM_initState_accountMapEquiv hcallPrice hAccountsLock
                  let evmPriceSolm : EVM.State :=
                    { evmLockSolm with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' }
                  have hlockStateSolm :
                      evmLockSolm =
                        initState cA gh bl σLockSolm σ₀ (Sat256.ofUInt256 g) A I := by
                    unfold evmLockSolm evmSolm clipperRedoLockedState σLockSolm
                    have hOne : ({ val := 1 } : UInt256) ≠ default := by native_decide
                    cases hacc : Batteries.RBMap.find? σ_solm I.codeOwner <;>
                      simp [initState, Solm.EVM.storageStore, State.lookupAccount,
                        State.setAccount, sstoreAccountMap, Account.updateStorage,
                        Option.option, hOne, hacc]
                  have hcallPriceSolm :
                      typedCallViaEVM (config v) evmLockSolm
                        (EVM.address (clipperStatusCalcAddress evmLockSolm)) "price" 0
                        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evmLockSolm I).toNat),
                          .int (Int.ofNat
                            (UInt256.sub (clipperTimestampWord evmLockSolm)
                              (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat)]
                        (false, evmPriceSolm, o) false := by
                    simpa [evmPriceSolm, hlockStateSolm,
                      σLockSolm, initState, clipperStatusCalcAddress, clipperStatusCalcWord,
                      clipperRedoSalesTopEVMWord, clipperRedoSalesTopWord,
                      clipperRedoSalesTicEVMWord, clipperRedoSalesTicWord, clipperTimestampWord,
                      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                      solcSlotWord,
                      hcalcSlotSolm, hcalcAddrSolm, htopSolmLoad, htopWord, hticSolmLoad,
                      hticWord, htimestampSolm, hticClean, hticCleanSolm, calcAddr]
                      using hcallPriceSolmRaw
                  have hstatus :
                      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                      let evmLock := clipperRedoLockedState evm0
                      ExecStmt (config v)
                        { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
                        evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
                        .reverted := by
                    simpa [evmSolm, evmLockSolm] using
                      clipperRedoStatusCallRevertsPriceCallFailure v
                        (evm := evmLockSolm) (evmPrice := evmPriceSolm) I hlePriceSolm
                        hcalcCodeSolm hcallPriceSolm
                  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                  have hbody :
                      ExecTransitionBody (config v) (contract v) evmSolm0 (clipperRedoStore I)
                        (redoTransition v).body .reverted := by
                    simpa [evmSolm0, σLockSolm] using
                      (clipperRedoStatusSourceRevertsOfStatus
                        (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                        hlockedSolm hstoppedSolmLt husrSolm hstatus)
                  exact hrev.reEquivExecutionRevert hcode hdispatch
                    (clipperDecode_redo_ok v hsz68) hbody
                · obtain ⟨_, _, rd8583⟩ :=
                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallSuccessToDecode
                      (v := v) hpatch (by simpa using rd8565)
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  by_cases hshortOut : o.size < 32
                  · have hrev :=
                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceReturnDecodeShortReverts
                      (v := v) hpatch (by simpa using rd8583)
                      (clipperRedoSalesHashMem_size I)
                      (clipperRedoSalesHashMem_read64 I)
                      hshortOut hout
                      (by simp only [List.length_cons, List.length_nil]; omega)
                    have hpriceDecode :
                        (config v).externalABI.decode? "price" o = none :=
                      clipperStatusPriceDecode_none_short hshortOut
                    obtain ⟨σ'_solm, A'_solm, hcallPriceSolmRaw, _hPostAccounts⟩ :=
                      typedCallViaEVM_initState_accountMapEquiv hcallPrice hAccountsLock
                    let evmPriceSolm : EVM.State :=
                      { evmLockSolm with
                        accountMap := σ'_solm
                        substate := A'_solm
                        createdAccounts := cA' }
                    have hlockStateSolm :
                        evmLockSolm =
                          initState cA gh bl σLockSolm σ₀ (Sat256.ofUInt256 g) A I := by
                      unfold evmLockSolm evmSolm clipperRedoLockedState σLockSolm
                      have hOne : ({ val := 1 } : UInt256) ≠ default := by native_decide
                      cases hacc : Batteries.RBMap.find? σ_solm I.codeOwner <;>
                        simp [initState, Solm.EVM.storageStore, State.lookupAccount,
                          State.setAccount, sstoreAccountMap, Account.updateStorage,
                          Option.option, hOne, hacc]
                    have hcallPriceSolm :
                        typedCallViaEVM (config v) evmLockSolm
                          (EVM.address (clipperStatusCalcAddress evmLockSolm)) "price" 0
                          [.int (Int.ofNat (clipperRedoSalesTopEVMWord evmLockSolm I).toNat),
                            .int (Int.ofNat
                              (UInt256.sub (clipperTimestampWord evmLockSolm)
                                (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat)]
                          (true, evmPriceSolm, o) false := by
                      simpa [evmPriceSolm, hlockStateSolm,
                        σLockSolm, initState, clipperStatusCalcAddress, clipperStatusCalcWord,
                        clipperRedoSalesTopEVMWord, clipperRedoSalesTopWord,
                        clipperRedoSalesTicEVMWord, clipperRedoSalesTicWord, clipperTimestampWord,
                        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                        solcSlotWord,
                        hcalcSlotSolm, hcalcAddrSolm, htopSolmLoad, htopWord, hticSolmLoad,
                        hticWord, htimestampSolm, hticClean, hticCleanSolm, calcAddr]
                        using hcallPriceSolmRaw
                    have hstatus :
                        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                        let evmLock := clipperRedoLockedState evm0
                        ExecStmt (config v)
                          { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
                          evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
                          .reverted := by
                      simpa [evmSolm, evmLockSolm] using
                        clipperRedoStatusCallRevertsPriceDecode v
                          (evm := evmLockSolm) (evmPrice := evmPriceSolm) I hlePriceSolm
                          hcalcCodeSolm hcallPriceSolm hpriceDecode
                    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                    have hbody :
                        ExecTransitionBody (config v) (contract v) evmSolm0 (clipperRedoStore I)
                          (redoTransition v).body .reverted := by
                      simpa [evmSolm0, σLockSolm] using
                        (clipperRedoStatusSourceRevertsOfStatus
                          (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                          hlockedSolm hstoppedSolmLt husrSolm hstatus)
                    exact hrev.reEquivExecutionRevert hcode hdispatch
                      (clipperDecode_redo_ok v hsz68) hbody
                  · have hloOut : 32 ≤ o.size := by omega
                    obtain ⟨_, _, rd8606⟩ :=
                      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceReturnDecodeOk
                        (v := v) (hpatch := hpatch) rd8583
                        (clipperRedoSalesHashMem_size I)
                        (clipperRedoSalesHashMem_read64 I) hloOut hout
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    let priceWord : UInt256 := clipperStatusPriceWord o
                    have hdecPrice :
                        (config v).externalABI.decode? "price" o =
                          some [.int (Int.ofNat priceWord.toNat)] := by
                      simpa [priceWord, clipperStatusPriceValues] using
                        clipperStatusPriceDecode_ok hloOut
                    obtain ⟨σ'_solm, A'_solm, hcallPriceSolmRaw, hPostAccounts⟩ :=
                      typedCallViaEVM_initState_accountMapEquiv hcallPrice hAccountsLock
                    let evmPriceSolm : EVM.State :=
                      { evmLockSolm with
                        accountMap := σ'_solm
                        substate := A'_solm
                        createdAccounts := cA' }
                    have hlockStateSolm :
                        evmLockSolm =
                          initState cA gh bl σLockSolm σ₀ (Sat256.ofUInt256 g) A I := by
                      unfold evmLockSolm evmSolm clipperRedoLockedState σLockSolm
                      have hOne : ({ val := 1 } : UInt256) ≠ default := by native_decide
                      cases hacc : Batteries.RBMap.find? σ_solm I.codeOwner <;>
                        simp [initState, Solm.EVM.storageStore, State.lookupAccount,
                          State.setAccount, sstoreAccountMap, Account.updateStorage,
                          Option.option, hOne, hacc]
                    have hcallPriceSolm :
                        typedCallViaEVM (config v) evmLockSolm
                          (EVM.address (clipperStatusCalcAddress evmLockSolm)) "price" 0
                          [.int (Int.ofNat (clipperRedoSalesTopEVMWord evmLockSolm I).toNat),
                            .int (Int.ofNat
                              (UInt256.sub (clipperTimestampWord evmLockSolm)
                                (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat)]
                          (true, evmPriceSolm, o) false := by
                      simpa [evmPriceSolm, hlockStateSolm,
                        σLockSolm, initState, clipperStatusCalcAddress, clipperStatusCalcWord,
                        clipperRedoSalesTopEVMWord, clipperRedoSalesTopWord,
                        clipperRedoSalesTicEVMWord, clipperRedoSalesTicWord, clipperTimestampWord,
                        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                        solcSlotWord,
                        hcalcSlotSolm, hcalcAddrSolm, htopSolmLoad, htopWord, hticSolmLoad,
                        hticWord, htimestampSolm, hticClean, hticCleanSolm, calcAddr]
                        using hcallPriceSolmRaw
                    let updatedTicPacked : UInt256 :=
                      UInt256.lor
                        (UInt256.mul
                          (UInt256.land clipperSalesUint96Mask
                            (UInt256.ofNat I.header.timestamp))
                          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
                        (UInt256.land solcAddrMask
                          (solcSlotWord σ' I (clipperRedoSalesPackedSlot I)))
                    let σTicEvm : AccountMap :=
                      sstoreAccountMap I.codeOwner σ' (clipperRedoSalesPackedSlot I)
                        updatedTicPacked
                    have hPostAccountsPlain : accountMapEquiv σ' σ'_solm := by
                      simpa [initState] using hPostAccounts
                    have hredoDoneTrueNoCodeRuntime
                        (hstatus :
                          let evm0 := initState cA gh bl σ_solm σ₀
                            (Sat256.ofUInt256 g) A I
                          let evmLock := clipperRedoLockedState evm0
                          ExecStmt (config v)
                            { contract := contract v,
                              locals := clipperRedoLocalsTop evmLock I }
                            evmLock
                            (.internalCall "status" [.var "tic", .var "top"] "st")
                            (.ok
                              { contract := contract v,
                                locals := clipperRedoLocalsSt evmLock I true priceWord }
                              evmPriceSolm))
                        (hspotterZero :
                          Reasoning.Theory.uniswapExtCodeSizeWord σTicEvm
                            (clipperSpotterTarget σTicEvm I) = ⟨0⟩)
                        {krd Crd : ℕ}
                        (rd8728 :
                          RD code I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨8728⟩
                            [⟨7719⟩, ⟨0⟩,
                              solcSlotWord σ' I
                                (solcMappingSlot ⟨12⟩ (clipperRedoIdWord I) + ⟨2⟩),
                              solcSlotWord σ' I
                                (solcMappingSlot ⟨12⟩ (clipperRedoIdWord I) + ⟨1⟩),
                              ⟨1⟩, clipperRedoSalesTopWord σLockEvm I,
                              clipperRedoSalesTicWord σLockEvm I,
                              clipperRedoSalesUsrWord σLockEvm I, ⟨2⟩,
                              clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩,
                              clipperSelWord I]
                            (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                              (clipperStatusPricePostCallMem
                                (clipperRedoSalesTopWord σLockEvm I)
                                (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                  (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                    clipperSalesUint96Mask))
                                (clipperRedoSalesHashMem I) o))
                            (UInt256.ofNat 7) o (cA', σTicEvm) krd Crd) :
                        runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm
                          σ₀ g A I := by
                      have hrev :=
                        RD.clipperGetFeedPriceSpotterIlksNoCode
                          (v := v) (hpatch := hpatch) rd8728 hspotterZero
                          (clipperGetFeedPriceHashPostMem_size_ge_164
                            (clipperRedoIdWord I)
                            (clipperRedoSalesTopWord σLockEvm I)
                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                              (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                clipperSalesUint96Mask))
                            (clipperRedoSalesHashMem_size I) hout)
                          (clipperGetFeedPriceHashPostMem_read64
                            (clipperRedoIdWord I)
                            (clipperRedoSalesTopWord σLockEvm I)
                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                              (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                clipperSalesUint96Mask))
                            (clipperRedoSalesHashMem_size I)
                            (clipperRedoSalesHashMem_read64 I) hout)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      have hnoCodeSolm :
                          (UInt256.ofNat
                            (((clipperRedoPostTicState evmPriceSolm I).lookupAccount
                              (clipperGetFeedPriceSpotterAddress
                                (clipperRedoPostTicState evmPriceSolm I))).option 0
                                (fun acc => acc.code.size))).toNat = 0 := by
                        exact
                          clipperRedoPostTicNoCode_of_accountMapEquiv
                            (σ := σ') (τ := σ'_solm) (I := I)
                            (evm := evmPriceSolm)
                            (by simp [evmPriceSolm])
                            (by simp [evmPriceSolm, hlockStateSolm, initState])
                            hPostAccountsPlain
                            (by
                              simpa [σTicEvm, updatedTicPacked] using hspotterZero)
                      let evmSolm0 :=
                        initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                      have hbody :
                          ExecTransitionBody (config v) (contract v) evmSolm0
                            (clipperRedoStore I) (redoTransition v).body .reverted := by
                        simpa [evmSolm0, σLockSolm] using
                          (clipperRedoDoneTrueGetFeedPriceNoCodeSourceReverts
                            (cA := cA) (gh := gh) (bl := bl)
                            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                            (g := g) (evmPrice := evmPriceSolm) v hwv
                            hlockedSolm hstoppedSolmLt husrSolm priceWord hstatus
                            hnoCodeSolm)
                      exact hrev.reEquivExecutionRevert hcode hdispatch
                        (clipperDecode_redo_ok v hsz68) hbody
                    have hredoDoneTrueCodeRuntime
                        (hstatus :
                          let evm0 := initState cA gh bl σ_solm σ₀
                            (Sat256.ofUInt256 g) A I
                          let evmLock := clipperRedoLockedState evm0
                          ExecStmt (config v)
                            { contract := contract v,
                              locals := clipperRedoLocalsTop evmLock I }
                            evmLock
                            (.internalCall "status" [.var "tic", .var "top"] "st")
                            (.ok
                              { contract := contract v,
                                locals := clipperRedoLocalsSt evmLock I true priceWord }
                              evmPriceSolm))
                        (hspotterCode :
                          Reasoning.Theory.uniswapExtCodeSizeWord σTicEvm
                            (clipperSpotterTarget σTicEvm I) ≠ ⟨0⟩)
                        {krd Crd : ℕ}
                        (rd8728 :
                          RD code I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨8728⟩
                            [⟨7719⟩, ⟨0⟩,
                              solcSlotWord σ' I
                                (solcMappingSlot ⟨12⟩ (clipperRedoIdWord I) + ⟨2⟩),
                              solcSlotWord σ' I
                                (solcMappingSlot ⟨12⟩ (clipperRedoIdWord I) + ⟨1⟩),
                              ⟨1⟩, clipperRedoSalesTopWord σLockEvm I,
                              clipperRedoSalesTicWord σLockEvm I,
                              clipperRedoSalesUsrWord σLockEvm I, ⟨2⟩,
                              clipperRedoKprMaskedWord I, clipperRedoIdWord I, ⟨502⟩,
                              clipperSelWord I]
                            (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                              (clipperStatusPricePostCallMem
                                (clipperRedoSalesTopWord σLockEvm I)
                                (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                  (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                    clipperSalesUint96Mask))
                                (clipperRedoSalesHashMem I) o))
                            (UInt256.ofNat 7) o (cA', σTicEvm) krd Crd) :
                        runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm
                          σ₀ g A I := by
                      obtain ⟨cAIlks, σIlks, zIlks, outIlks, AIlks, k8840, C8840,
                          rd8840, hcallIlks, houtIlks⟩ :=
                        RD.clipperGetFeedPriceSpotterIlksPostCall
                          (v := v) (hpatch := hpatch) rd8728 hspotterCode hdepth hperm
                          (clipperGetFeedPriceHashPostMem_size_ge_164
                            (clipperRedoIdWord I)
                            (clipperRedoSalesTopWord σLockEvm I)
                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                              (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                clipperSalesUint96Mask))
                            (clipperRedoSalesHashMem_size I) hout)
                          (clipperGetFeedPriceHashPostMem_read64
                            (clipperRedoIdWord I)
                            (clipperRedoSalesTopWord σLockEvm I)
                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                              (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                clipperSalesUint96Mask))
                            (clipperRedoSalesHashMem_size I)
                            (clipperRedoSalesHashMem_read64 I) hout)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      cases zIlks
                      · have hrev :=
                          RD.clipperGetFeedPriceSpotterIlksCallFailure
                            (v := v) (hpatch := hpatch)
                            (by simpa using rd8840) houtIlks
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        have hPostTicAccounts :
                            accountMapEquiv σTicEvm
                              (clipperRedoPostTicState evmPriceSolm I).accountMap := by
                          simpa [σTicEvm, updatedTicPacked] using
                            clipperRedoPostTicAccountMapEquiv
                              (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                              (by simp [evmPriceSolm])
                              (by simp [evmPriceSolm, hlockStateSolm, initState])
                              hPostAccountsPlain
                        have htargetSolm :
                            clipperGetFeedPriceSpotterAddress
                                (clipperRedoPostTicState evmPriceSolm I) =
                              AccountAddress.ofUInt256
                                (clipperSpotterTarget σTicEvm I) := by
                          simpa [σTicEvm, updatedTicPacked] using
                            clipperRedoPostTicSpotterAddress_eq_of_accountMapEquiv
                              (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                              (by simp [evmPriceSolm])
                              (by simp [evmPriceSolm, hlockStateSolm, initState])
                              hPostAccountsPlain
                        obtain ⟨σIlksSolm, AIlksSolm, hcallIlksSolmRaw, _hIlksAccounts⟩ :=
                          typedCallViaEVM_accountMapEquiv_noSubstate
                            (cfg := config v) hcallIlks hPostTicAccounts
                            (by simp [clipperRedoPostTicState, clipperStorageStore_σ₀,
                              evmPriceSolm, hlockStateSolm, initState])
                            (by simp [clipperRedoPostTicState,
                              clipperStorageStore_createdAccounts, evmPriceSolm,
                              hlockStateSolm, initState])
                            (by simp [clipperRedoPostTicState,
                              clipperStorageStore_genesisBlockHeader, evmPriceSolm,
                              hlockStateSolm, initState])
                            (by simp [clipperRedoPostTicState, clipperStorageStore_blocks,
                              evmPriceSolm, hlockStateSolm, initState])
                            (by simp [clipperRedoPostTicState,
                              clipperStorageStore_executionEnv, evmPriceSolm, hlockStateSolm,
                              initState])
                        have hcallIlksSolm :
                            typedCallViaEVM (config v) (clipperRedoPostTicState evmPriceSolm I)
                              (EVM.address
                                (clipperGetFeedPriceSpotterAddress
                                  (clipperRedoPostTicState evmPriceSolm I)))
                              "spotterIlks" 0 [v.ilk]
                              (false,
                                { clipperRedoPostTicState evmPriceSolm I with
                                  accountMap := σIlksSolm
                                  substate := AIlksSolm
                                  createdAccounts := cAIlks },
                                outIlks) true := by
                          simpa [htargetSolm, initState] using hcallIlksSolmRaw
                        have hcodeSolm :
                            0 < (UInt256.ofNat
                              (((clipperRedoPostTicState evmPriceSolm I).lookupAccount
                                (clipperGetFeedPriceSpotterAddress
                                  (clipperRedoPostTicState evmPriceSolm I))).option 0
                                  (fun acc => acc.code.size))).toNat := by
                          exact
                            clipperRedoPostTicCode_of_accountMapEquiv
                              (σ := σ') (τ := σ'_solm) (I := I)
                              (evm := evmPriceSolm)
                              (by simp [evmPriceSolm])
                              (by simp [evmPriceSolm, hlockStateSolm, initState])
                              hPostAccountsPlain
                              (by simpa [σTicEvm, updatedTicPacked] using hspotterCode)
                        let evmSolm0 :=
                          initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                        have hbody :
                            ExecTransitionBody (config v) (contract v) evmSolm0
                              (clipperRedoStore I) (redoTransition v).body .reverted := by
                          simpa [evmSolm0, σLockSolm] using
                            (clipperRedoDoneTrueGetFeedPriceCallFailureSourceReverts
                              (cA := cA) (gh := gh) (bl := bl)
                              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                              (g := g) (evmPrice := evmPriceSolm) v hwv
                              hlockedSolm hstoppedSolmLt husrSolm priceWord hstatus
                              hcodeSolm hcallIlksSolm)
                        exact hrev.reEquivExecutionRevert hcode hdispatch
                          (clipperDecode_redo_ok v hsz68) hbody
                      · obtain ⟨k8861, C8861, rd8861⟩ :=
                          RD.clipperGetFeedPriceSpotterIlksCallSuccessToDecode
                            (v := v) (hpatch := hpatch)
                            (by simpa using rd8840)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        by_cases hshortIlks : outIlks.size < 64
                        · have hbaseSize196 :
                              (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                (clipperStatusPricePostCallMem
                                  (clipperRedoSalesTopWord σLockEvm I)
                                  (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                    (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                      clipperSalesUint96Mask))
                                  (clipperRedoSalesHashMem I) o)).size = 196 := by
                            rw [twoWordHashMem_size_of_ge_64]
                            · rw [clipperStatusPricePostCallMem_size
                                (clipperRedoSalesTopWord σLockEvm I)
                                (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                  (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                    clipperSalesUint96Mask))
                                (clipperRedoSalesHashMem_size I) hout]
                            · rw [clipperStatusPricePostCallMem_size
                                (clipperRedoSalesTopWord σLockEvm I)
                                (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                  (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                    clipperSalesUint96Mask))
                                (clipperRedoSalesHashMem_size I) hout]
                              omega
                          have hbaseRead64 :
                              (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                (clipperStatusPricePostCallMem
                                  (clipperRedoSalesTopWord σLockEvm I)
                                  (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                    (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                      clipperSalesUint96Mask))
                                  (clipperRedoSalesHashMem I) o)).readWithPadding 64 32 =
                                UInt256.toByteArray ⟨128⟩ :=
                            clipperGetFeedPriceHashPostMem_read64
                              (clipperRedoIdWord I)
                              (clipperRedoSalesTopWord σLockEvm I)
                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                  clipperSalesUint96Mask))
                              (clipperRedoSalesHashMem_size I)
                              (clipperRedoSalesHashMem_read64 I) hout
                          have hrev :=
                            RD.clipperGetFeedPriceSpotterIlksDecodeShortReverts
                              (v := v) (hpatch := hpatch) rd8861 hbaseSize196 hbaseRead64
                              hshortIlks houtIlks
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          have hPostTicAccounts :
                              accountMapEquiv σTicEvm
                                (clipperRedoPostTicState evmPriceSolm I).accountMap := by
                            simpa [σTicEvm, updatedTicPacked] using
                              clipperRedoPostTicAccountMapEquiv
                                (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                                (by simp [evmPriceSolm])
                                (by simp [evmPriceSolm, hlockStateSolm, initState])
                                hPostAccountsPlain
                          have htargetSolm :
                              clipperGetFeedPriceSpotterAddress
                                  (clipperRedoPostTicState evmPriceSolm I) =
                                AccountAddress.ofUInt256
                                  (clipperSpotterTarget σTicEvm I) := by
                            simpa [σTicEvm, updatedTicPacked] using
                              clipperRedoPostTicSpotterAddress_eq_of_accountMapEquiv
                                (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                                (by simp [evmPriceSolm])
                                (by simp [evmPriceSolm, hlockStateSolm, initState])
                                hPostAccountsPlain
                          obtain ⟨σIlksSolm, AIlksSolm, hcallIlksSolmRaw,
                              _hIlksAccounts⟩ :=
                            typedCallViaEVM_accountMapEquiv_noSubstate
                              (cfg := config v) hcallIlks hPostTicAccounts
                              (by simp [clipperRedoPostTicState, clipperStorageStore_σ₀,
                                evmPriceSolm, hlockStateSolm, initState])
                              (by simp [clipperRedoPostTicState,
                                clipperStorageStore_createdAccounts, evmPriceSolm,
                                hlockStateSolm, initState])
                              (by simp [clipperRedoPostTicState,
                                clipperStorageStore_genesisBlockHeader, evmPriceSolm,
                                hlockStateSolm, initState])
                              (by simp [clipperRedoPostTicState, clipperStorageStore_blocks,
                                evmPriceSolm, hlockStateSolm, initState])
                              (by simp [clipperRedoPostTicState,
                                clipperStorageStore_executionEnv, evmPriceSolm, hlockStateSolm,
                                initState])
                          have hcallIlksSolm :
                              typedCallViaEVM (config v)
                                (clipperRedoPostTicState evmPriceSolm I)
                                (EVM.address
                                  (clipperGetFeedPriceSpotterAddress
                                    (clipperRedoPostTicState evmPriceSolm I)))
                                "spotterIlks" 0 [v.ilk]
                                (true,
                                  { clipperRedoPostTicState evmPriceSolm I with
                                    accountMap := σIlksSolm
                                    substate := AIlksSolm
                                    createdAccounts := cAIlks },
                                  outIlks) true := by
                            simpa [htargetSolm, initState] using hcallIlksSolmRaw
                          have hcodeSolm :
                              0 < (UInt256.ofNat
                                (((clipperRedoPostTicState evmPriceSolm I).lookupAccount
                                  (clipperGetFeedPriceSpotterAddress
                                    (clipperRedoPostTicState evmPriceSolm I))).option 0
                                    (fun acc => acc.code.size))).toNat := by
                            exact
                              clipperRedoPostTicCode_of_accountMapEquiv
                                (σ := σ') (τ := σ'_solm) (I := I)
                                (evm := evmPriceSolm)
                                (by simp [evmPriceSolm])
                                (by simp [evmPriceSolm, hlockStateSolm, initState])
                                hPostAccountsPlain
                                (by simpa [σTicEvm, updatedTicPacked] using hspotterCode)
                          have hdecIlks :
                              (config v).externalABI.decode? "spotterIlks" outIlks = none :=
                            clipperSpotterIlksDecode_none_short hshortIlks
                          let evmSolm0 :=
                            initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                          have hbody :
                              ExecTransitionBody (config v) (contract v) evmSolm0
                                (clipperRedoStore I) (redoTransition v).body .reverted := by
                            simpa [evmSolm0, σLockSolm] using
                              (clipperRedoDoneTrueGetFeedPriceDecodeSourceReverts
                                (cA := cA) (gh := gh) (bl := bl)
                                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                (g := g) (evmPrice := evmPriceSolm) v hwv
                                hlockedSolm hstoppedSolmLt husrSolm priceWord hstatus
                                hcodeSolm hcallIlksSolm hdecIlks)
                          exact hrev.reEquivExecutionRevert hcode hdispatch
                            (clipperDecode_redo_ok v hsz68) hbody
                        · have hloIlks : 64 ≤ outIlks.size := by omega
                          have hbaseSize196 :
                              (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                (clipperStatusPricePostCallMem
                                  (clipperRedoSalesTopWord σLockEvm I)
                                  (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                    (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                      clipperSalesUint96Mask))
                                  (clipperRedoSalesHashMem I) o)).size = 196 := by
                            rw [twoWordHashMem_size_of_ge_64]
                            · rw [clipperStatusPricePostCallMem_size
                                (clipperRedoSalesTopWord σLockEvm I)
                                (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                  (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                    clipperSalesUint96Mask))
                                (clipperRedoSalesHashMem_size I) hout]
                            · rw [clipperStatusPricePostCallMem_size
                                (clipperRedoSalesTopWord σLockEvm I)
                                (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                  (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                    clipperSalesUint96Mask))
                                (clipperRedoSalesHashMem_size I) hout]
                              omega
                          have hbaseRead64 :
                              (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                (clipperStatusPricePostCallMem
                                  (clipperRedoSalesTopWord σLockEvm I)
                                  (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                    (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                      clipperSalesUint96Mask))
                                  (clipperRedoSalesHashMem I) o)).readWithPadding 64 32 =
                                UInt256.toByteArray ⟨128⟩ :=
                            clipperGetFeedPriceHashPostMem_read64
                              (clipperRedoIdWord I)
                              (clipperRedoSalesTopWord σLockEvm I)
                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                  clipperSalesUint96Mask))
                              (clipperRedoSalesHashMem_size I)
                              (clipperRedoSalesHashMem_read64 I) hout
                          obtain ⟨k8937, C8937, rd8937⟩ :=
                            _root_.Benchmarks.Dss.Clipper.RD.clipperGetFeedPriceSpotterIlksDecodeOkToPipPeekExtcodesizeGuard
                              (v := v) (hpatch := hpatch) rd8861 hbaseSize196 hbaseRead64
                              hloIlks houtIlks
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          by_cases hpipNoCode :
                              uniswapExtCodeSizeWord σIlks
                                (clipperSpotterIlksPipTarget outIlks) = ⟨0⟩
                          · have hrev :=
                              _root_.Benchmarks.Dss.Clipper.RD.clipperGetFeedPricePipPeekNoCode
                                (v := v) (hpatch := hpatch) rd8937 hpipNoCode
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            have hPostTicAccounts :
                                accountMapEquiv σTicEvm
                                  (clipperRedoPostTicState evmPriceSolm I).accountMap := by
                              simpa [σTicEvm, updatedTicPacked] using
                                clipperRedoPostTicAccountMapEquiv
                                  (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                                  (by simp [evmPriceSolm])
                                  (by simp [evmPriceSolm, hlockStateSolm, initState])
                                  hPostAccountsPlain
                            have htargetSolm :
                                clipperGetFeedPriceSpotterAddress
                                    (clipperRedoPostTicState evmPriceSolm I) =
                                  AccountAddress.ofUInt256
                                    (clipperSpotterTarget σTicEvm I) := by
                              simpa [σTicEvm, updatedTicPacked] using
                                clipperRedoPostTicSpotterAddress_eq_of_accountMapEquiv
                                  (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                                  (by simp [evmPriceSolm])
                                  (by simp [evmPriceSolm, hlockStateSolm, initState])
                                  hPostAccountsPlain
                            obtain ⟨σIlksSolm, AIlksSolm, hcallIlksSolmRaw,
                                hIlksAccountsRaw⟩ :=
                              typedCallViaEVM_accountMapEquiv_noSubstate
                                (cfg := config v) hcallIlks hPostTicAccounts
                                (by simp [clipperRedoPostTicState, clipperStorageStore_σ₀,
                                  evmPriceSolm, hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState,
                                  clipperStorageStore_createdAccounts, evmPriceSolm,
                                  hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState,
                                  clipperStorageStore_genesisBlockHeader, evmPriceSolm,
                                  hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState, clipperStorageStore_blocks,
                                  evmPriceSolm, hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState,
                                  clipperStorageStore_executionEnv, evmPriceSolm,
                                  hlockStateSolm, initState])
                            have hIlksAccounts : accountMapEquiv σIlks σIlksSolm := by
                              simpa [initState] using hIlksAccountsRaw
                            have hcallIlksSolm :
                                typedCallViaEVM (config v)
                                  (clipperRedoPostTicState evmPriceSolm I)
                                  (EVM.address
                                    (clipperGetFeedPriceSpotterAddress
                                      (clipperRedoPostTicState evmPriceSolm I)))
                                  "spotterIlks" 0 [v.ilk]
                                  (true,
                                    { clipperRedoPostTicState evmPriceSolm I with
                                      accountMap := σIlksSolm
                                      substate := AIlksSolm
                                      createdAccounts := cAIlks },
                                    outIlks) true := by
                              simpa [htargetSolm, initState] using hcallIlksSolmRaw
                            have hcodeSolm :
                                0 < (UInt256.ofNat
                                  (((clipperRedoPostTicState evmPriceSolm I).lookupAccount
                                    (clipperGetFeedPriceSpotterAddress
                                      (clipperRedoPostTicState evmPriceSolm I))).option 0
                                      (fun acc => acc.code.size))).toNat := by
                              exact
                                clipperRedoPostTicCode_of_accountMapEquiv
                                  (σ := σ') (τ := σ'_solm) (I := I)
                                  (evm := evmPriceSolm)
                                  (by simp [evmPriceSolm])
                                  (by simp [evmPriceSolm, hlockStateSolm, initState])
                                  hPostAccountsPlain
                                  (by simpa [σTicEvm, updatedTicPacked] using hspotterCode)
                            have hdecIlks :
                                (config v).externalABI.decode? "spotterIlks" outIlks =
                                  some (clipperSpotterIlksValues outIlks) :=
                              clipperSpotterIlksDecode_ok (v := v) hloIlks
                            have hnoCodePipSolm :
                                (UInt256.ofNat
                                  ((σIlksSolm.find? (clipperSpotterIlksPipAddress outIlks))
                                    |>.option 0 (fun acc => acc.code.size))).toNat = 0 := by
                              exact
                                clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
                                  (σ := σIlks) (τ := σIlksSolm)
                                  (target := clipperSpotterIlksPipTarget outIlks)
                                  (addr := clipperSpotterIlksPipAddress outIlks)
                                  hIlksAccounts
                                  (clipperSpotterIlksPipAddress_eq_target outIlks)
                                  hpipNoCode
                            let evmSolm0 :=
                              initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                            have hbody :
                                ExecTransitionBody (config v) (contract v) evmSolm0
                                  (clipperRedoStore I) (redoTransition v).body .reverted := by
                              simpa [evmSolm0, σLockSolm] using
                                (clipperRedoDoneTrueGetFeedPricePipNoCodeSourceReverts
                                  (cA := cA) (gh := gh) (bl := bl)
                                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                  (g := g) (evmPrice := evmPriceSolm)
                                  (evmIlks :=
                                    { clipperRedoPostTicState evmPriceSolm I with
                                      accountMap := σIlksSolm
                                      substate := AIlksSolm
                                      createdAccounts := cAIlks })
                                  v hwv hlockedSolm hstoppedSolmLt husrSolm priceWord hstatus
                                  hcodeSolm hcallIlksSolm hdecIlks
                                  (by simpa using hnoCodePipSolm))
                            exact hrev.reEquivExecutionRevert hcode hdispatch
                              (clipperDecode_redo_ok v hsz68) hbody
                          · have hspotterPostSize :
                                (clipperSpotterIlksPostCallMem v
                                  (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                    (clipperStatusPricePostCallMem
                                      (clipperRedoSalesTopWord σLockEvm I)
                                      (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                          clipperSalesUint96Mask))
                                      (clipperRedoSalesHashMem I) o))
                                  outIlks).size = 196 :=
                              clipperSpotterIlksPostCallMem_size_long v hbaseSize196
                                hloIlks houtIlks
                            have hspotterPostRead64 :
                                (clipperSpotterIlksPostCallMem v
                                  (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                    (clipperStatusPricePostCallMem
                                      (clipperRedoSalesTopWord σLockEvm I)
                                      (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                          clipperSalesUint96Mask))
                                      (clipperRedoSalesHashMem I) o))
                                  outIlks).readWithPadding 64 32 =
                                  UInt256.toByteArray ⟨128⟩ :=
                              clipperSpotterIlksPostCallMem_read64_long v hbaseSize196
                                hbaseRead64 hloIlks houtIlks
                            have hselectorSize :
                                (clipperPipPeekSelectorMem
                                  (clipperSpotterIlksPostCallMem v
                                    (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                      (clipperStatusPricePostCallMem
                                        (clipperRedoSalesTopWord σLockEvm I)
                                        (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                          (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                            clipperSalesUint96Mask))
                                        (clipperRedoSalesHashMem I) o))
                                    outIlks)).size = 196 := by
                              rw [clipperPipPeekSelectorMem_size_of_ge
                                (by rw [hspotterPostSize]; omega), hspotterPostSize]
                            have hselectorRead64 :
                                (clipperPipPeekSelectorMem
                                  (clipperSpotterIlksPostCallMem v
                                    (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                      (clipperStatusPricePostCallMem
                                        (clipperRedoSalesTopWord σLockEvm I)
                                        (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                          (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                            clipperSalesUint96Mask))
                                        (clipperRedoSalesHashMem I) o))
                                    outIlks)).readWithPadding 64 32 =
                                  UInt256.toByteArray ⟨128⟩ :=
                              clipperPipPeekSelectorMem_read64
                                (by rw [hspotterPostSize]; omega) hspotterPostRead64
                            obtain ⟨cAPeek, σPeek, zPeek, outPeek, APeek, k8953,
                                C8953, rd8953, hcallPeek, houtPeek⟩ :=
                              _root_.Benchmarks.Dss.Clipper.RD.clipperGetFeedPricePipPeekPostCall
                                (v := v) (hpatch := hpatch) rd8937 hpipNoCode hdepth hperm
                                (by
                                  simpa using
                                    (clipperPipPeekEncode_eq v
                                      (mem := clipperSpotterIlksPostCallMem v
                                        (twoWordHashMem (clipperRedoIdWord I) ⟨12⟩
                                          (clipperStatusPricePostCallMem
                                            (clipperRedoSalesTopWord σLockEvm I)
                                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                              (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                                clipperSalesUint96Mask))
                                            (clipperRedoSalesHashMem I) o))
                                        outIlks)
                                      (by rw [hspotterPostSize]; omega)))
                                (clipperSpotterIlksPipAddress_eq_target outIlks).symm
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            have hPostTicAccounts :
                                accountMapEquiv σTicEvm
                                  (clipperRedoPostTicState evmPriceSolm I).accountMap := by
                              simpa [σTicEvm, updatedTicPacked] using
                                clipperRedoPostTicAccountMapEquiv
                                  (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                                  (by simp [evmPriceSolm])
                                  (by simp [evmPriceSolm, hlockStateSolm, initState])
                                  hPostAccountsPlain
                            have htargetSolm :
                                clipperGetFeedPriceSpotterAddress
                                    (clipperRedoPostTicState evmPriceSolm I) =
                                  AccountAddress.ofUInt256
                                    (clipperSpotterTarget σTicEvm I) := by
                              simpa [σTicEvm, updatedTicPacked] using
                                clipperRedoPostTicSpotterAddress_eq_of_accountMapEquiv
                                  (σ := σ') (τ := σ'_solm) (I := I) (evm := evmPriceSolm)
                                  (by simp [evmPriceSolm])
                                  (by simp [evmPriceSolm, hlockStateSolm, initState])
                                  hPostAccountsPlain
                            obtain ⟨σIlksSolm, AIlksSolm, hcallIlksSolmRaw,
                                hIlksAccountsRaw⟩ :=
                              typedCallViaEVM_accountMapEquiv_noSubstate
                                (cfg := config v) hcallIlks hPostTicAccounts
                                (by simp [clipperRedoPostTicState, clipperStorageStore_σ₀,
                                  evmPriceSolm, hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState,
                                  clipperStorageStore_createdAccounts, evmPriceSolm,
                                  hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState,
                                  clipperStorageStore_genesisBlockHeader, evmPriceSolm,
                                  hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState, clipperStorageStore_blocks,
                                  evmPriceSolm, hlockStateSolm, initState])
                                (by simp [clipperRedoPostTicState,
                                  clipperStorageStore_executionEnv, evmPriceSolm,
                                  hlockStateSolm, initState])
                            have hIlksAccounts : accountMapEquiv σIlks σIlksSolm := by
                              simpa [initState] using hIlksAccountsRaw
                            let evmIlksSolm :
                                EVM.State :=
                              { clipperRedoPostTicState evmPriceSolm I with
                                accountMap := σIlksSolm
                                substate := AIlksSolm
                                createdAccounts := cAIlks }
                            have hcallIlksSolm :
                                typedCallViaEVM (config v)
                                  (clipperRedoPostTicState evmPriceSolm I)
                                  (EVM.address
                                    (clipperGetFeedPriceSpotterAddress
                                      (clipperRedoPostTicState evmPriceSolm I)))
                                  "spotterIlks" 0 [v.ilk]
                                  (true, evmIlksSolm, outIlks) true := by
                              simpa [evmIlksSolm, htargetSolm, initState] using
                                hcallIlksSolmRaw
                            have hcodeSolm :
                                0 < (UInt256.ofNat
                                  (((clipperRedoPostTicState evmPriceSolm I).lookupAccount
                                    (clipperGetFeedPriceSpotterAddress
                                      (clipperRedoPostTicState evmPriceSolm I))).option 0
                                      (fun acc => acc.code.size))).toNat := by
                              exact
                                clipperRedoPostTicCode_of_accountMapEquiv
                                  (σ := σ') (τ := σ'_solm) (I := I)
                                  (evm := evmPriceSolm)
                                  (by simp [evmPriceSolm])
                                  (by simp [evmPriceSolm, hlockStateSolm, initState])
                                  hPostAccountsPlain
                                  (by simpa [σTicEvm, updatedTicPacked] using hspotterCode)
                            have hdecIlks :
                                (config v).externalABI.decode? "spotterIlks" outIlks =
                                  some (clipperSpotterIlksValues outIlks) :=
                              clipperSpotterIlksDecode_ok (v := v) hloIlks
                            have hcodePipSolm :
                                0 < (UInt256.ofNat
                                  ((evmIlksSolm.lookupAccount
                                    (clipperSpotterIlksPipAddress outIlks)).option 0
                                      (fun acc => acc.code.size))).toNat := by
                              simpa [evmIlksSolm, State.lookupAccount] using
                                clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
                                  (σ := σIlks) (τ := σIlksSolm)
                                  (target := clipperSpotterIlksPipTarget outIlks)
                                  (addr := clipperSpotterIlksPipAddress outIlks)
                                  hIlksAccounts
                                  (clipperSpotterIlksPipAddress_eq_target outIlks)
                                  hpipNoCode
                            cases zPeek
                            · have hrev :=
                                _root_.Benchmarks.Dss.Clipper.RD.clipperGetFeedPricePipPeekCallFailure
                                  (v := v) (hpatch := hpatch) (by simpa using rd8953)
                                  houtPeek
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              obtain ⟨σPeekSolm, APeekSolm, hcallPeekSolmRaw,
                                  _hPeekAccounts⟩ :=
                                typedCallViaEVM_accountMapEquiv_noSubstate
                                  (cfg := config v) (evm_solm := evmIlksSolm)
                                  hcallPeek hIlksAccounts
                                  (by simp [evmIlksSolm, clipperRedoPostTicState,
                                    clipperStorageStore_σ₀, evmPriceSolm, hlockStateSolm,
                                    initState])
                                  (by simp [evmIlksSolm])
                                  (by simp [evmIlksSolm, clipperRedoPostTicState,
                                    clipperStorageStore_genesisBlockHeader, evmPriceSolm,
                                    hlockStateSolm, initState])
                                  (by simp [evmIlksSolm, clipperRedoPostTicState,
                                    clipperStorageStore_blocks, evmPriceSolm, hlockStateSolm,
                                    initState])
                                  (by simp [evmIlksSolm, clipperRedoPostTicState,
                                    clipperStorageStore_executionEnv, evmPriceSolm,
                                    hlockStateSolm, initState])
                              have hcallPeekSolm :
                                  typedCallViaEVM (config v) evmIlksSolm
                                    (EVM.address (clipperSpotterIlksPipAddress outIlks))
                                    "peek" 0 []
                                    (false,
                                      { evmIlksSolm with
                                        accountMap := σPeekSolm
                                        substate := APeekSolm
                                        createdAccounts := cAPeek },
                                      outPeek) true := by
                                simpa [evmIlksSolm, initState] using hcallPeekSolmRaw
                              let evmSolm0 :=
                                initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                              have hbody :
                                  ExecTransitionBody (config v) (contract v) evmSolm0
                                    (clipperRedoStore I) (redoTransition v).body .reverted := by
                                simpa [evmSolm0, σLockSolm, evmIlksSolm] using
                                  (clipperRedoDoneTrueGetFeedPricePipCallFailureSourceReverts
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := g) (evmPrice := evmPriceSolm)
                                    (evmIlks := evmIlksSolm)
                                    (evmPeek :=
                                      { evmIlksSolm with
                                        accountMap := σPeekSolm
                                        substate := APeekSolm
                                        createdAccounts := cAPeek })
                                    v hwv hlockedSolm hstoppedSolmLt husrSolm priceWord hstatus
                                    hcodeSolm hcallIlksSolm hdecIlks hcodePipSolm
                                    hcallPeekSolm)
                              exact hrev.reEquivExecutionRevert hcode hdispatch
                                (clipperDecode_redo_ok v hsz68) hbody
                            · obtain ⟨k8974, C8974, rd8974⟩ :=
                                _root_.Benchmarks.Dss.Clipper.RD.clipperGetFeedPricePipPeekCallSuccessToDecode
                                  (v := v) (hpatch := hpatch) (by simpa using rd8953)
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              by_cases hshortPeek : outPeek.size < 64
                              · have hrev :=
                                  _root_.Benchmarks.Dss.Clipper.RD.clipperGetFeedPricePipPeekDecodeShortReverts
                                    (v := v) (hpatch := hpatch) rd8974
                                    (clipperPipPeekPostCallMem_size hselectorSize houtPeek)
                                    (clipperPipPeekPostCallMem_read64 hselectorSize
                                      hselectorRead64 houtPeek)
                                    hshortPeek houtPeek
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                obtain ⟨σPeekSolm, APeekSolm, hcallPeekSolmRaw,
                                    _hPeekAccounts⟩ :=
                                  typedCallViaEVM_accountMapEquiv_noSubstate
                                    (cfg := config v) (evm_solm := evmIlksSolm)
                                    hcallPeek hIlksAccounts
                                    (by simp [evmIlksSolm, clipperRedoPostTicState,
                                      clipperStorageStore_σ₀, evmPriceSolm, hlockStateSolm,
                                      initState])
                                    (by simp [evmIlksSolm])
                                    (by simp [evmIlksSolm, clipperRedoPostTicState,
                                      clipperStorageStore_genesisBlockHeader, evmPriceSolm,
                                      hlockStateSolm, initState])
                                    (by simp [evmIlksSolm, clipperRedoPostTicState,
                                      clipperStorageStore_blocks, evmPriceSolm, hlockStateSolm,
                                      initState])
                                    (by simp [evmIlksSolm, clipperRedoPostTicState,
                                      clipperStorageStore_executionEnv, evmPriceSolm,
                                      hlockStateSolm, initState])
                                have hcallPeekSolm :
                                    typedCallViaEVM (config v) evmIlksSolm
                                      (EVM.address (clipperSpotterIlksPipAddress outIlks))
                                      "peek" 0 []
                                      (true,
                                        { evmIlksSolm with
                                          accountMap := σPeekSolm
                                          substate := APeekSolm
                                          createdAccounts := cAPeek },
                                        outPeek) true := by
                                  simpa [evmIlksSolm, initState] using hcallPeekSolmRaw
                                have hdecPeek :
                                    (config v).externalABI.decode? "peek" outPeek = none :=
                                  clipperPipPeekDecode_none_short hshortPeek
                                let evmSolm0 :=
                                  initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                                have hbody :
                                    ExecTransitionBody (config v) (contract v) evmSolm0
                                      (clipperRedoStore I) (redoTransition v).body .reverted := by
                                  simpa [evmSolm0, σLockSolm, evmIlksSolm] using
                                    (clipperRedoDoneTrueGetFeedPricePipDecodeSourceReverts
                                      (cA := cA) (gh := gh) (bl := bl)
                                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                      (g := g) (evmPrice := evmPriceSolm)
                                      (evmIlks := evmIlksSolm)
                                      (evmPeek :=
                                        { evmIlksSolm with
                                          accountMap := σPeekSolm
                                          substate := APeekSolm
                                          createdAccounts := cAPeek })
                                      v hwv hlockedSolm hstoppedSolmLt husrSolm priceWord hstatus
                                      hcodeSolm hcallIlksSolm hdecIlks hcodePipSolm
                                      hcallPeekSolm hdecPeek)
                                exact hrev.reEquivExecutionRevert hcode hdispatch
                                  (clipperDecode_redo_ok v hsz68) hbody
                              · have hloPeek : 64 ≤ outPeek.size := by omega
                                by_cases hhasFalse : clipperPipPeekHasWord outPeek = ⟨0⟩
                                · have hrev :=
                                    _root_.Benchmarks.Dss.Clipper.RD.clipperGetFeedPricePipPeekHasFalseReverts
                                      (v := v) (hpatch := hpatch) rd8974
                                      (clipperPipPeekPostCallMem_size hselectorSize houtPeek)
                                      (clipperPipPeekPostCallMem_read64 hselectorSize
                                        hselectorRead64 houtPeek)
                                      (clipperPipPeekPostCallMem_read128_long hselectorSize
                                        hloPeek houtPeek)
                                      (clipperPipPeekPostCallMem_read160_long hselectorSize
                                        hloPeek houtPeek)
                                      hloPeek houtPeek hhasFalse
                                      (by simp only [List.length_cons, List.length_nil]; omega)
                                  obtain ⟨σPeekSolm, APeekSolm, hcallPeekSolmRaw,
                                      _hPeekAccounts⟩ :=
                                    typedCallViaEVM_accountMapEquiv_noSubstate
                                      (cfg := config v) (evm_solm := evmIlksSolm)
                                      hcallPeek hIlksAccounts
                                      (by simp [evmIlksSolm, clipperRedoPostTicState,
                                        clipperStorageStore_σ₀, evmPriceSolm, hlockStateSolm,
                                        initState])
                                      (by simp [evmIlksSolm])
                                      (by simp [evmIlksSolm, clipperRedoPostTicState,
                                        clipperStorageStore_genesisBlockHeader, evmPriceSolm,
                                        hlockStateSolm, initState])
                                      (by simp [evmIlksSolm, clipperRedoPostTicState,
                                        clipperStorageStore_blocks, evmPriceSolm, hlockStateSolm,
                                        initState])
                                      (by simp [evmIlksSolm, clipperRedoPostTicState,
                                        clipperStorageStore_executionEnv, evmPriceSolm,
                                        hlockStateSolm, initState])
                                  have hcallPeekSolm :
                                      typedCallViaEVM (config v) evmIlksSolm
                                        (EVM.address (clipperSpotterIlksPipAddress outIlks))
                                        "peek" 0 []
                                        (true,
                                          { evmIlksSolm with
                                            accountMap := σPeekSolm
                                            substate := APeekSolm
                                            createdAccounts := cAPeek },
                                          outPeek) true := by
                                    simpa [evmIlksSolm, initState] using hcallPeekSolmRaw
                                  have hdecPeek :
                                      (config v).externalABI.decode? "peek" outPeek =
                                        some (clipperPipPeekValues outPeek) :=
                                    clipperPipPeekDecode_ok hloPeek
                                  let evmSolm0 :=
                                    initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                                  have hbody :
                                      ExecTransitionBody (config v) (contract v) evmSolm0
                                        (clipperRedoStore I) (redoTransition v).body .reverted := by
                                    simpa [evmSolm0, σLockSolm, evmIlksSolm] using
                                      (clipperRedoDoneTrueGetFeedPricePipHasFalseSourceReverts
                                        (cA := cA) (gh := gh) (bl := bl)
                                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                        (g := g) (evmPrice := evmPriceSolm)
                                        (evmIlks := evmIlksSolm)
                                        (evmPeek :=
                                          { evmIlksSolm with
                                            accountMap := σPeekSolm
                                            substate := APeekSolm
                                            createdAccounts := cAPeek })
                                        v hwv hlockedSolm hstoppedSolmLt husrSolm priceWord hstatus
                                        hcodeSolm hcallIlksSolm hdecIlks hcodePipSolm
                                        hcallPeekSolm hdecPeek hhasFalse)
                                  exact hrev.reEquivExecutionRevert hcode hdispatch
                                    (clipperDecode_redo_ok v hsz68) hbody
                                · sorry
                    by_cases hleDone :
                        (clipperRedoSalesTicWord σLockEvm I).toNat ≤
                          (UInt256.ofNat I.header.timestamp).toNat
                    · have hleDoneSolm :
                        (clipperRedoSalesTicEVMWord evmLockSolm I).toNat ≤
                          (clipperTimestampWord evmPriceSolm).toNat := by
                        simpa [evmPriceSolm, htimestampSolm, hticSolmLoad, ← hticWord]
                          using hleDone
                      by_cases htailLt :
                          (solcSlotWord σ' I ⟨6⟩).toNat <
                            (UInt256.sub (UInt256.ofNat I.header.timestamp)
                              (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                clipperSalesUint96Mask)).toNat
                      · obtain ⟨_, _, rd7575⟩ :=
                          Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceDoneTailTrue
                            (v := v) (hpatch := hpatch) rd8606
                            (by simpa [hticClean] using hleDone) htailLt
                            (clipperRedoBodyJumpDest7575 v hpatch)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        obtain ⟨_, _, rd7651⟩ :=
                          RD.clipperRedoStatusTrueToDoneBranch (v := v) (hpatch := hpatch)
                            (by simpa [priceWord] using rd7575)
                        obtain ⟨_, _, rd8728⟩ :=
                          RD.clipperRedoDoneBranchToGetFeedPrice (v := v) (hpatch := hpatch)
                            rd7651 hperm
                            (by
                              rw [clipperStatusPricePostCallMem_size
                                (clipperRedoSalesTopWord σLockEvm I)
                                (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                  (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                    clipperSalesUint96Mask))
                                (clipperRedoSalesHashMem_size I) hout]
                              omega)
                        obtain ⟨_, _, _rd8824⟩ :=
                          RD.clipperGetFeedPriceToSpotterIlksExtcodesizeGuard
                            (v := v) (hpatch := hpatch) rd8728
                            (clipperGetFeedPriceHashPostMem_size_ge_164
                              (clipperRedoIdWord I)
                              (clipperRedoSalesTopWord σLockEvm I)
                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                  clipperSalesUint96Mask))
                              (clipperRedoSalesHashMem_size I) hout)
                            (clipperGetFeedPriceHashPostMem_read64
                              (clipperRedoIdWord I)
                              (clipperRedoSalesTopWord σLockEvm I)
                              (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                  clipperSalesUint96Mask))
                              (clipperRedoSalesHashMem_size I)
                              (clipperRedoSalesHashMem_read64 I) hout)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        have htailSlotSolm :
                            solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ'_solm I ⟨6⟩ := by
                          exact accountMapEquiv_storage_findD (σ := σ') (τ := σ'_solm)
                            hPostAccountsPlain I.codeOwner ⟨6⟩ (⟨0⟩ : UInt256)
                        have hpriceOwner : evmPriceSolm.executionEnv.codeOwner = I.codeOwner := by
                          simp [evmPriceSolm, hlockStateSolm, initState]
                        have hlockOwner : evmLockSolm.executionEnv.codeOwner = I.codeOwner := by
                          rw [hlockStateSolm]
                          simp [initState]
                        have htailSolmLt :
                            (clipperStatusTailWord evmPriceSolm).toNat <
                              (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat := by
                          simpa [evmPriceSolm, clipperStatusTailWord,
                            clipperTimestampWord, Solm.EVM.storageLoad, State.lookupAccount,
                            Account.lookupStorage, solcSlotWord, htailSlotSolm,
                            htimestampSolm, hticSolmLoad, ← hticWord, hticClean, hpriceOwner,
                            hlockOwner]
                            using htailLt
                        have hstatus :
                            let evm0 := initState cA gh bl σ_solm σ₀
                              (Sat256.ofUInt256 g) A I
                            let evmLock := clipperRedoLockedState evm0
                            ExecStmt (config v)
                              { contract := contract v,
                                locals := clipperRedoLocalsTop evmLock I }
                              evmLock
                              (.internalCall "status" [.var "tic", .var "top"] "st")
                              (.ok
                                { contract := contract v,
                                  locals := clipperRedoLocalsSt evmLock I true priceWord }
                                evmPriceSolm) := by
                          simpa [evmSolm, evmLockSolm] using
                            clipperRedoStatusCallReturnsDoneTailTrue v
                              (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                              I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                              hcallPriceSolm hdecPrice hleDoneSolm htailSolmLt
                        by_cases hspotterZero :
                            Reasoning.Theory.uniswapExtCodeSizeWord σTicEvm
                              (clipperSpotterTarget σTicEvm I) = ⟨0⟩
                        · exact hredoDoneTrueNoCodeRuntime hstatus hspotterZero
                            (by
                              simpa [σTicEvm, updatedTicPacked, clipperRedoSalesPackedSlot,
                                clipperRedoSalesBaseSlot_eq] using rd8728)
                        · exact hredoDoneTrueCodeRuntime hstatus hspotterZero
                            (by
                              simpa [σTicEvm, updatedTicPacked, clipperRedoSalesPackedSlot,
                                clipperRedoSalesBaseSlot_eq] using rd8728)
                      · have htailLe :
                          (UInt256.sub (UInt256.ofNat I.header.timestamp)
                              (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                clipperSalesUint96Mask)).toNat ≤
                            (solcSlotWord σ' I ⟨6⟩).toNat := by
                          exact Nat.le_of_not_gt htailLt
                        have htailSlotSolm :
                            solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ'_solm I ⟨6⟩ := by
                          exact accountMapEquiv_storage_findD (σ := σ') (τ := σ'_solm)
                            hPostAccounts I.codeOwner ⟨6⟩ (⟨0⟩ : UInt256)
                        have hlockOwner : evmLockSolm.executionEnv.codeOwner = I.codeOwner := by
                          rw [hlockStateSolm]
                          simp [initState]
                        have htailSolm :
                            (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat ≤
                              (clipperStatusTailWord evmPriceSolm).toNat := by
                          simpa [evmPriceSolm, clipperStatusTailWord,
                            clipperTimestampWord, Solm.EVM.storageLoad, State.lookupAccount,
                            Account.lookupStorage, solcSlotWord, htailSlotSolm,
                            htimestampSolm, hticSolmLoad, ← hticWord, hticClean, hlockOwner]
                            using htailLe
                        by_cases hmul : priceWord.toNat * clipperRayWord.toNat < UInt256.size
                        · by_cases htopZero : clipperRedoSalesTopWord σLockEvm I = ⟨0⟩
                          · have hinv :=
                              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivDivZeroInvalid
                                (v := v) (hpatch := hpatch) rd8606
                                (by simpa [hticClean] using hleDone) htailLe
                                (by simpa [priceWord] using hmul) htopZero
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            have htopSolmZero :
                                clipperRedoSalesTopEVMWord evmLockSolm I = ⟨0⟩ := by
                              simpa [htopSolmLoad, ← htopWord] using htopZero
                            have hstatus :
                                let evm0 := initState cA gh bl σ_solm σ₀
                                  (Sat256.ofUInt256 g) A I
                                let evmLock := clipperRedoLockedState evm0
                                ExecStmt (config v)
                                  { contract := contract v,
                                    locals := clipperRedoLocalsTop evmLock I }
                                  evmLock
                                  (.internalCall "status" [.var "tic", .var "top"] "st")
                                  .reverted := by
                              simpa [evmSolm, evmLockSolm] using
                                clipperRedoStatusCallRevertsRdivDivZero v
                                  (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                  I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                  hcallPriceSolm hdecPrice hleDoneSolm htailSolm hmul
                                  htopSolmZero
                            let evmSolm0 :=
                              initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                            have hbody :
                                ExecTransitionBody (config v) (contract v) evmSolm0
                                  (clipperRedoStore I) (redoTransition v).body .reverted := by
                              simpa [evmSolm0, σLockSolm] using
                                (clipperRedoStatusSourceRevertsOfStatus
                                  (cA := cA) (gh := gh) (bl := bl)
                                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                  (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                  hstatus)
                            exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch
                              (clipperDecode_redo_ok v hsz68) hbody
                          · obtain ⟨_, _, rd7575⟩ :=
                              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivBranch
                                (v := v) (hpatch := hpatch) rd8606
                                (by simpa [hticClean] using hleDone) htailLe
                                (by simpa [priceWord] using hmul) htopZero
                                (clipperRedoBodyJumpDest7575 v hpatch)
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            let ratioWord : UInt256 :=
                              UInt256.div (UInt256.mul priceWord clipperRayWord)
                                (clipperRedoSalesTopWord σLockEvm I)
                            let cuspWord : UInt256 := solcSlotWord σ' I ⟨7⟩
                            let doneWord : UInt256 := UInt256.lt ratioWord cuspWord
                            have hcuspWordSolm :
                                cuspWord = clipperStatusCuspWord evmPriceSolm := by
                              have hslot :=
                                accountMapEquiv_storage_findD (σ := σ') (τ := σ'_solm)
                                  hPostAccounts I.codeOwner ⟨7⟩ (⟨0⟩ : UInt256)
                              simpa [cuspWord, evmPriceSolm, hlockOwner,
                                clipperStatusCuspWord,
                                initState, Solm.EVM.storageLoad, State.lookupAccount,
                                Account.lookupStorage, solcSlotWord] using hslot
                            have hratioWordSolm :
                                ratioWord =
                                  UInt256.div (UInt256.mul priceWord clipperRayWord)
                                    (clipperRedoSalesTopEVMWord evmLockSolm I) := by
                              simp [ratioWord, htopSolmLoad, ← htopWord]
                            by_cases hratio :
                                ratioWord.toNat <
                                  (clipperStatusCuspWord evmPriceSolm).toNat
                            · have hdoneWordOne : doneWord = ⟨1⟩ := by
                                unfold doneWord
                                exact ult_one
                                  (by
                                    simpa [cuspWord, hcuspWordSolm] using hratio)
                              obtain ⟨_, _, rd7651⟩ :=
                                RD.clipperRedoStatusTrueToDoneBranch (v := v)
                                  (hpatch := hpatch)
                                  (by
                                    simpa [priceWord, ratioWord, cuspWord, doneWord,
                                      hdoneWordOne] using rd7575)
                              obtain ⟨_, _, rd8728⟩ :=
                                RD.clipperRedoDoneBranchToGetFeedPrice (v := v)
                                  (hpatch := hpatch) rd7651 hperm
                                  (by
                                    rw [clipperStatusPricePostCallMem_size
                                      (clipperRedoSalesTopWord σLockEvm I)
                                      (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                        (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                          clipperSalesUint96Mask))
                                      (clipperRedoSalesHashMem_size I) hout]
                                    omega)
                              obtain ⟨_, _, _rd8824⟩ :=
                                RD.clipperGetFeedPriceToSpotterIlksExtcodesizeGuard
                                  (v := v) (hpatch := hpatch) rd8728
                                  (clipperGetFeedPriceHashPostMem_size_ge_164
                                    (clipperRedoIdWord I)
                                    (clipperRedoSalesTopWord σLockEvm I)
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                      (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                        clipperSalesUint96Mask))
                                    (clipperRedoSalesHashMem_size I) hout)
                                  (clipperGetFeedPriceHashPostMem_read64
                                    (clipperRedoIdWord I)
                                    (clipperRedoSalesTopWord σLockEvm I)
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                      (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                        clipperSalesUint96Mask))
                                    (clipperRedoSalesHashMem_size I)
                                    (clipperRedoSalesHashMem_read64 I) hout)
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have hdoneEval :
                                  evalExpr? (config v)
                                    { contract := contract v,
                                      locals := clipperStatusRatioLocals
                                        (clipperRedoSalesTicEVMWord evmLockSolm I)
                                        (clipperRedoSalesTopEVMWord evmLockSolm I)
                                        (UInt256.sub (clipperTimestampWord evmLockSolm)
                                          (clipperRedoSalesTicEVMWord evmLockSolm I))
                                        priceWord
                                        (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                          (clipperRedoSalesTicEVMWord evmLockSolm I))
                                        (UInt256.div
                                          (UInt256.mul priceWord clipperRayWord)
                                          (clipperRedoSalesTopEVMWord evmLockSolm I)) }
                                    evmPriceSolm
                                      (.binary .lt (.var "ratio") (.storage cuspRef)) =
                                    .ok (.bool true) := by
                                rw [← hratioWordSolm]
                                exact clipperEvalStatusRatioCuspCond_true v evmPriceSolm
                                  (clipperRedoSalesTicEVMWord evmLockSolm I)
                                  (clipperRedoSalesTopEVMWord evmLockSolm I)
                                  (UInt256.sub (clipperTimestampWord evmLockSolm)
                                    (clipperRedoSalesTicEVMWord evmLockSolm I))
                                  priceWord
                                  (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                    (clipperRedoSalesTicEVMWord evmLockSolm I))
                                  ratioWord hratio
                              have hstatus :
                                  let evm0 := initState cA gh bl σ_solm σ₀
                                    (Sat256.ofUInt256 g) A I
                                  let evmLock := clipperRedoLockedState evm0
                                  ExecStmt (config v)
                                    { contract := contract v,
                                      locals := clipperRedoLocalsTop evmLock I }
                                    evmLock
                                    (.internalCall "status" [.var "tic", .var "top"] "st")
                                    (.ok
                                      { contract := contract v,
                                        locals :=
                                          clipperRedoLocalsSt evmLock I true priceWord }
                                      evmPriceSolm) := by
                                simpa [evmSolm, evmLockSolm] using
                                  clipperRedoStatusCallReturnsRdivBranch v
                                    (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                    I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                    hcallPriceSolm hdecPrice hleDoneSolm htailSolm hmul
                                    (by
                                      intro hzero
                                      exact htopZero
                                        (by
                                          simpa [htopSolmLoad, ← htopWord]
                                            using hzero))
                                    true hdoneEval
                              by_cases hspotterZero :
                                  Reasoning.Theory.uniswapExtCodeSizeWord σTicEvm
                                    (clipperSpotterTarget σTicEvm I) = ⟨0⟩
                              · exact hredoDoneTrueNoCodeRuntime hstatus hspotterZero
                                  (by
                                    simpa [σTicEvm, updatedTicPacked,
                                      clipperRedoSalesPackedSlot,
                                      clipperRedoSalesBaseSlot_eq] using rd8728)
                              · exact hredoDoneTrueCodeRuntime hstatus hspotterZero
                                  (by
                                    simpa [σTicEvm, updatedTicPacked,
                                      clipperRedoSalesPackedSlot,
                                      clipperRedoSalesBaseSlot_eq] using rd8728)
                            · have hratioLe :
                                  (clipperStatusCuspWord evmPriceSolm).toNat ≤
                                    ratioWord.toNat := by
                                exact Nat.le_of_not_gt hratio
                              have hdoneEval :
                                  evalExpr? (config v)
                                    { contract := contract v,
                                      locals := clipperStatusRatioLocals
                                        (clipperRedoSalesTicEVMWord evmLockSolm I)
                                        (clipperRedoSalesTopEVMWord evmLockSolm I)
                                        (UInt256.sub (clipperTimestampWord evmLockSolm)
                                          (clipperRedoSalesTicEVMWord evmLockSolm I))
                                        priceWord
                                        (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                          (clipperRedoSalesTicEVMWord evmLockSolm I))
                                        (UInt256.div
                                          (UInt256.mul priceWord clipperRayWord)
                                          (clipperRedoSalesTopEVMWord evmLockSolm I)) }
                                    evmPriceSolm
                                      (.binary .lt (.var "ratio") (.storage cuspRef)) =
                                    .ok (.bool false) := by
                                rw [← hratioWordSolm]
                                exact clipperEvalStatusRatioCuspCond_false v evmPriceSolm
                                  (clipperRedoSalesTicEVMWord evmLockSolm I)
                                  (clipperRedoSalesTopEVMWord evmLockSolm I)
                                  (UInt256.sub (clipperTimestampWord evmLockSolm)
                                    (clipperRedoSalesTicEVMWord evmLockSolm I))
                                  priceWord
                                  (UInt256.sub (clipperTimestampWord evmPriceSolm)
                                    (clipperRedoSalesTicEVMWord evmLockSolm I))
                                  ratioWord hratioLe
                              have hdoneWordZero : doneWord = ⟨0⟩ := by
                                unfold doneWord
                                exact ult_zero
                                  (by
                                    simpa [ratioWord, cuspWord, hcuspWordSolm]
                                      using hratioLe)
                              have hrev :=
                                RD.clipperRedoStatusFalseReverts (v := v)
                                  (hpatch := hpatch)
                                  (by
                                    simpa [priceWord, ratioWord, cuspWord, doneWord,
                                      hdoneWordZero] using rd7575)
                                  (clipperStatusPricePostCallMem_size
                                    (clipperRedoSalesTopWord σLockEvm I)
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                      (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                        clipperSalesUint96Mask))
                                    (clipperRedoSalesHashMem_size I) hout)
                                  (clipperStatusPricePostCallMem_read64
                                    (clipperRedoSalesTopWord σLockEvm I)
                                    (UInt256.sub (UInt256.ofNat I.header.timestamp)
                                      (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                                        clipperSalesUint96Mask))
                                    (clipperRedoSalesHashMem_size I)
                                    (clipperRedoSalesHashMem_read64 I) hout)
                              have hstatus :
                                  let evm0 := initState cA gh bl σ_solm σ₀
                                    (Sat256.ofUInt256 g) A I
                                  let evmLock := clipperRedoLockedState evm0
                                  ExecStmt (config v)
                                    { contract := contract v,
                                      locals := clipperRedoLocalsTop evmLock I }
                                    evmLock
                                    (.internalCall "status" [.var "tic", .var "top"] "st")
                                    (.ok
                                      { contract := contract v,
                                        locals :=
                                          clipperRedoLocalsSt evmLock I false priceWord }
                                      evmPriceSolm) := by
                                simpa [evmSolm, evmLockSolm] using
                                  clipperRedoStatusCallReturnsRdivBranch v
                                    (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                    I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                    hcallPriceSolm hdecPrice hleDoneSolm htailSolm hmul
                                    (by
                                      intro hzero
                                      exact htopZero
                                        (by
                                          simpa [htopSolmLoad, ← htopWord]
                                            using hzero))
                                    false hdoneEval
                              let evmSolm0 :=
                                initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                              have hbody :
                                  ExecTransitionBody (config v) (contract v) evmSolm0
                                    (clipperRedoStore I) (redoTransition v).body .reverted := by
                                simpa [evmSolm0, σLockSolm] using
                                  (clipperRedoStatusFalseSourceReverts
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                    priceWord hstatus)
                              exact hrev.reEquivExecutionRevert hcode hdispatch
                                (clipperDecode_redo_ok v hsz68) hbody
                        · have hover :
                              UInt256.size ≤ priceWord.toNat * clipperRayWord.toNat := by
                            exact Nat.le_of_not_gt hmul
                          have hrev :=
                            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivMulRevert
                              (v := v) (hpatch := hpatch) rd8606
                              (by simpa [hticClean] using hleDone) htailLe
                              (by simpa [priceWord] using hover)
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          have hstatus :
                              let evm0 := initState cA gh bl σ_solm σ₀
                                (Sat256.ofUInt256 g) A I
                              let evmLock := clipperRedoLockedState evm0
                              ExecStmt (config v)
                                { contract := contract v,
                                  locals := clipperRedoLocalsTop evmLock I }
                                evmLock
                                (.internalCall "status" [.var "tic", .var "top"] "st")
                                .reverted := by
                            simpa [evmSolm, evmLockSolm] using
                              clipperRedoStatusCallRevertsRdivMul v
                                (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                                I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                                hcallPriceSolm hdecPrice hleDoneSolm htailSolm hover
                          let evmSolm0 :=
                            initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                          have hbody :
                              ExecTransitionBody (config v) (contract v) evmSolm0
                                (clipperRedoStore I) (redoTransition v).body .reverted := by
                            simpa [evmSolm0, σLockSolm] using
                              (clipperRedoStatusSourceRevertsOfStatus
                                (cA := cA) (gh := gh) (bl := bl)
                                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                                (g := g) v hwv hlockedSolm hstoppedSolmLt husrSolm
                                hstatus)
                          exact hrev.reEquivExecutionRevert hcode hdispatch
                            (clipperDecode_redo_ok v hsz68) hbody
                    · have hltDone :
                          (UInt256.ofNat I.header.timestamp).toNat <
                            (UInt256.land (clipperRedoSalesTicWord σLockEvm I)
                              clipperSalesUint96Mask).toNat := by
                        simpa [hticClean] using Nat.lt_of_not_ge hleDone
                      have hrev :=
                        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForDoneRevert
                          (v := v) (hpatch := hpatch) rd8606 hltDone
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      have hltDoneSolm :
                          (clipperTimestampWord evmPriceSolm).toNat <
                            (clipperRedoSalesTicEVMWord evmLockSolm I).toNat := by
                        simpa [evmPriceSolm, htimestampSolm, hticSolmLoad, ← hticWord]
                          using Nat.lt_of_not_ge hleDone
                      have hstatus :
                          let evm0 := initState cA gh bl σ_solm σ₀
                            (Sat256.ofUInt256 g) A I
                          let evmLock := clipperRedoLockedState evm0
                          ExecStmt (config v)
                            { contract := contract v,
                              locals := clipperRedoLocalsTop evmLock I }
                            evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
                            .reverted := by
                        simpa [evmSolm, evmLockSolm] using
                          clipperRedoStatusCallRevertsAgeForDone v
                            (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                            I priceWord (out := o) hlePriceSolm hcalcCodeSolm
                            hcallPriceSolm hdecPrice hltDoneSolm
                      let evmSolm0 :=
                        initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                      have hbody :
                          ExecTransitionBody (config v) (contract v) evmSolm0
                            (clipperRedoStore I) (redoTransition v).body .reverted := by
                        simpa [evmSolm0, σLockSolm] using
                          (clipperRedoStatusSourceRevertsOfStatus
                            (cA := cA) (gh := gh) (bl := bl)
                            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                            hlockedSolm hstoppedSolmLt husrSolm hstatus)
                      exact hrev.reEquivExecutionRevert hcode hdispatch
                        (clipperDecode_redo_ok v hsz68) hbody
              · have hdepthEq : I.depth = (1024 : Fin 1025) := by
                  have hval : I.depth.val = 1024 := by
                    have hleDepth : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                    have hgeDepth : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
                    exact Nat.le_antisymm hleDepth hgeDepth
                  apply Fin.ext
                  simpa using hval
                obtain ⟨_, _, rd8565⟩ :=
                  RD.clipperStatusPriceCallDepthLimitFromCurrent
                    (v := v) hpatch rd8549
                    (by simpa [calcAddr] using hcalcCode)
                    hdepthEq
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hrev :=
                  Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallFailure
                    (v := v) hpatch (by simpa using rd8565) (by native_decide)
                    (by simp only [List.length_cons, List.length_nil]; omega)
                let ageForPrice : UInt256 :=
                  UInt256.sub (UInt256.ofNat I.header.timestamp)
                    (UInt256.land (clipperRedoSalesTicWord σLockEvm I) clipperSalesUint96Mask)
                have hdepthInit : evmLockSolm.executionEnv.depth = 1024 := by
                  simpa [evmLockSolm, evmSolm, clipperRedoLockedState, initState,
                    storageStore_executionEnv] using hdepthEq
                let evmPriceSolm : EVM.State :=
                  { evmLockSolm with
                    substate :=
                      (evmLockSolm.addAccessedAccount
                        (EVM.address (clipperStatusCalcAddress evmLockSolm))).substate }
                have hcd :
                    (config v).externalABI.encode? "price"
                      [.int (Int.ofNat (clipperRedoSalesTopEVMWord evmLockSolm I).toNat),
                        .int (Int.ofNat
                          (UInt256.sub (clipperTimestampWord evmLockSolm)
                            (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat)] =
                      some ((clipperStatusPriceCalldataMem
                        (clipperRedoSalesTopWord σLockEvm I) ageForPrice
                        (clipperRedoSalesHashMem I)).readWithPadding 128 68) := by
                  have hcdRaw :
                      (config v).externalABI.encode? "price"
                        [.int (Int.ofNat (clipperRedoSalesTopWord σLockEvm I).toNat),
                          .int (Int.ofNat ageForPrice.toNat)] =
                        some ((clipperStatusPriceCalldataMem
                          (clipperRedoSalesTopWord σLockEvm I) ageForPrice
                          (clipperRedoSalesHashMem I)).readWithPadding 128 68) := by
                    simpa using
                      clipperStatusPriceEncode_eq v
                        (clipperRedoSalesTopWord σLockEvm I) ageForPrice
                        (clipperRedoSalesHashMem_size I)
                  have htopEvmSolm :
                      clipperRedoSalesTopEVMWord evmLockSolm I =
                        clipperRedoSalesTopWord σLockEvm I := by
                    rw [htopSolmLoad, ← htopWord]
                  have hageForPriceSolm :
                      UInt256.sub (clipperTimestampWord evmLockSolm)
                          (clipperRedoSalesTicEVMWord evmLockSolm I) =
                        ageForPrice := by
                    simp [ageForPrice, htimestampSolm, hticSolmLoad, ← hticWord, hticClean]
                  rw [htopEvmSolm, hageForPriceSolm]
                  exact hcdRaw
                have hcallPriceSolm :
                    typedCallViaEVM (config v) evmLockSolm
                      (EVM.address (clipperStatusCalcAddress evmLockSolm)) "price" 0
                      [.int (Int.ofNat (clipperRedoSalesTopEVMWord evmLockSolm I).toNat),
                        .int (Int.ofNat
                          (UInt256.sub (clipperTimestampWord evmLockSolm)
                            (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat)]
                      (false, evmPriceSolm, ByteArray.empty) false := by
                  simpa [evmPriceSolm] using
                    (callNotMade_depthLimit (cfg := config v) (evm := evmLockSolm)
                      (tgt := EVM.address (clipperStatusCalcAddress evmLockSolm))
                      (name := "price")
                      (args :=
                        [.int (Int.ofNat (clipperRedoSalesTopEVMWord evmLockSolm I).toNat),
                          .int (Int.ofNat
                            (UInt256.sub (clipperTimestampWord evmLockSolm)
                              (clipperRedoSalesTicEVMWord evmLockSolm I)).toNat)])
                      (callPerm := false)
                      (calldata :=
                        (clipperStatusPriceCalldataMem
                          (clipperRedoSalesTopWord σLockEvm I) ageForPrice
                          (clipperRedoSalesHashMem I)).readWithPadding 128 68)
                      hcd hdepthInit)
                have hstatus :
                    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                    let evmLock := clipperRedoLockedState evm0
                    ExecStmt (config v)
                      { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
                      evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
                      .reverted := by
                  simpa [evmSolm, evmLockSolm] using
                    clipperRedoStatusCallRevertsPriceCallFailure v
                      (evm := evmLockSolm) (evmPrice := evmPriceSolm)
                      I (out := ByteArray.empty) hlePriceSolm hcalcCodeSolm hcallPriceSolm
                let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm0 (clipperRedoStore I)
                      (redoTransition v).body .reverted := by
                  simpa [evmSolm0, σLockSolm] using
                    (clipperRedoStatusSourceRevertsOfStatus
                      (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                      hlockedSolm hstoppedSolmLt husrSolm hstatus)
                exact hrev.reEquivExecutionRevert hcode hdispatch
                  (clipperDecode_redo_ok v hsz68) hbody
            · have hcalcZero :
                  Reasoning.Theory.uniswapExtCodeSizeWord σLockEvm calcAddr = ⟨0⟩ :=
                not_ne_iff.mp hcalcCode
              have hrev :=
                Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceNoCode
                  (v := v) hpatch rd8549
                  (by simpa [calcAddr] using hcalcZero)
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hcalcAddrSolm :
                  clipperStatusCalcAddress evmLockSolm = AccountAddress.ofUInt256 calcAddr := by
                simp [σLockSolm, evmLockSolm, evmSolm, clipperRedoLockedState,
                  clipperStatusCalcAddress,
                  clipperStatusCalcWord, calcAddr, initState, Solm.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage, solcSlotWord,
                  storageStore_accountMap, storageStore_executionEnv, hcalcSlotSolm]
              have hcalcZeroSolm :
                  Reasoning.Theory.uniswapExtCodeSizeWord σLockSolm calcAddr = ⟨0⟩ := by
                rw [← Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv
                  hAccountsLock calcAddr]
                exact hcalcZero
              have hnoCodeSolm :
                  (UInt256.ofNat
                    ((evmLockSolm.lookupAccount (clipperStatusCalcAddress evmLockSolm)).option 0
                      (fun acc => acc.code.size))).toNat = 0 := by
                rw [hcalcAddrSolm]
                unfold Reasoning.Theory.uniswapExtCodeSizeWord at hcalcZeroSolm
                simp [evmLockSolm, evmSolm, clipperRedoLockedState, State.lookupAccount,
                  initState, storageStore_accountMap] at hcalcZeroSolm ⊢
                cases hacc : σLockSolm.find? (AccountAddress.ofUInt256 calcAddr) with
                | none =>
                    native_decide
                | some acc =>
                    simp [hacc] at hcalcZeroSolm ⊢
                    exact congrArg UInt256.toNat hcalcZeroSolm
              have hstatus :
                  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                  let evmLock := clipperRedoLockedState evm0
                  ExecStmt (config v)
                    { contract := contract v, locals := clipperRedoLocalsTop evmLock I }
                    evmLock (.internalCall "status" [.var "tic", .var "top"] "st")
                    .reverted := by
                simpa [evmSolm, evmLockSolm] using
                  clipperRedoStatusCallRevertsPriceNoCode v evmLockSolm I
                    hlePriceSolm hnoCodeSolm
              let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have hbody :
                  ExecTransitionBody (config v) (contract v) evmSolm0 (clipperRedoStore I)
                    (redoTransition v).body .reverted := by
                simpa [evmSolm0, σLockSolm] using
                  (clipperRedoStatusSourceRevertsOfStatus
                    (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                    hlockedSolm hstoppedSolmLt husrSolm hstatus)
              exact hrev.reEquivExecutionRevert hcode hdispatch
                (clipperDecode_redo_ok v hsz68) hbody
          · have hltEvm :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (clipperRedoSalesTicWord σLockEvm I).toNat := by
              omega
            have hltSolm :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (clipperRedoSalesTicWord σLockSolm I).toNat := by
              rw [← hticWord]
              exact hltEvm
            let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            have hbody :
                ExecTransitionBody (config v) (contract v) evmSolm (clipperRedoStore I)
                  (redoTransition v).body .reverted := by
              simpa [evmSolm, σLockSolm] using
                (clipperRedoStatusAgeForPriceSourceReverts
                  (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                  hlockedSolm hstoppedSolmLt husrSolm hltSolm)
            have hrev :=
              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPriceRevert
                (v := v) hpatch _hreachStatus
                (by simpa [hticClean] using hltEvm)
                (by simp only [List.length_cons, List.length_nil]; omega)
            exact hrev.reEquivExecutionRevert hcode hdispatch (clipperDecode_redo_ok v hsz68)
              hbody
      · have hstoppedEvmGe : 2 ≤ (solcSlotWord σLockEvm I ⟨14⟩).toNat := by
          omega
        have hstoppedSolmGe : 2 ≤ (solcSlotWord σLockSolm I ⟨14⟩).toNat := by
          rw [← hstoppedWord]
          exact hstoppedEvmGe
        let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody (config v) (contract v) evmSolm (clipperRedoStore I)
              (redoTransition v).body .reverted := by
          simpa [evmSolm, σLockSolm] using
            (clipperRedoStoppedSourceReverts (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
              hlockedSolm hstoppedSolmGe)
        have hrev := clipperRedoX_stoppedClosed (v := v) (σ := σLockEvm)
          hpatch (by simpa [σLockEvm] using hstoppedEvmGe)
          (by simpa [σLockEvm] using hreachLocked)
        exact hrev.reEquivExecutionRevert hcode hdispatch (clipperDecode_redo_ok v hsz68)
          hbody
    · have hlockWord : solcSlotWord σ_evm I ⟨13⟩ = solcSlotWord σ_solm I ⟨13⟩ := by
        simpa [solcSlotWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner (⟨13⟩ : UInt256) ⟨0⟩
      have hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ ≠ ⟨0⟩ := by
        intro hsolm
        exact hlockedEvm (by rw [hlockWord, hsolm])
      let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evmSolm (clipperRedoStore I)
            (redoTransition v).body .reverted := by
        simpa [evmSolm] using
          (clipperRedoLockedSourceReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv hlockedSolm)
      have hrev := clipperRedoX_locked (v := v) hpatch hlockedEvm hreachBody
      exact hrev.reEquivExecutionRevert hcode hdispatch (clipperDecode_redo_ok v hsz68)
        hbody
  · have hshort : I.calldata.size < 68 := by omega
    exact (clipperRedoX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
      hsize hshort hreachEntry).reEquivDecodingFailed hcode hdispatch
        (clipperDecode_redo_none_short v hsz4 hshort)

end Benchmarks.Dss.Clipper
