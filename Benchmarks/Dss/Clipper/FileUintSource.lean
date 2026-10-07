import Benchmarks.Dss.Clipper.FileUintBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperFileUintAuthSourceReverts {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted (immStore v) := by
  intro locals evm0
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_false v evm0 I (by simp [evm0, initState]) hauth
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body .reverted := by
    simpa [fileUintTransition, nonpayable, auth, lockPrefix] using
      nonpayableSecondRequireReverts
        (cfg := config)
        (solm := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := lockPrefix ++
          [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
            [.ite (.binary .eq (.var "what") tailParamLit)
              [.assign .storage tailRef (.var "data")]
              [.ite (.binary .eq (.var "what") cuspParamLit)
                [.assign .storage cuspRef (.var "data")]
                [.ite (.binary .eq (.var "what") chipParamLit)
                  [.assign .storage chipRef (wrap64 (.var "data"))]
                  [.ite (.binary .eq (.var "what") tipParamLit)
                    [.assign .storage tipRef (wrap192 (.var "data"))]
                    [.ite (.binary .eq (.var "what") stoppedParamLit)
                      [.assign .storage stoppedRef (.var "data")]
                      [.require (.boolLit false)]]]]]],
            .assign .storage lockedRef (.intLit 0)])
        (by simp [evm0, initState]; exact hwv)
        hauthEval
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperFileUintLockedSourceReverts {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted (immStore v) := by
  intro locals evm0
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_false v evm0 I hlocked
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hlockedEval)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileUintBufSourceBodySplit {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileUintWordPostState evm0 ⟨5⟩ (clipperFileUintData I)
    (clipperFileUintWhat I = clipperFileUintBufBytes →
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm2 none) (immStore v)) ∧
    (I.perm = false →
      ExecTransitionBody config contract evm0 locals
        fileUintTransition.body .staticViolation (immStore v)) := by
  intro locals evm0 evm2
  let evmLock := clipperFileUintLockedState evm0
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨5⟩ (clipperFileUintData I)
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmLock) := by
    simpa [locals, evmLock, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evm0 I ⟨1⟩
  have hprefix {result : ExecResult}
      (hrest : ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (fileUintTransition.body.drop 3) result) :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body result := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact hrest
  constructor
  · intro hwhat
    have hbufCond :
        evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
          (.binary .eq (.var "what") bufParamLit) = .ok (.bool true) := by
      simpa [bufParamLit, clipperFileUintBufBytes, locals] using
        evalExpr_clipperFileUint_what_eq_true (v := v) (evm := evmLock) (I := I)
          (locals := locals) (bs := clipperFileUintBufBytes)
          (by simpa [locals] using clipperFileUintLocals_get_what I) hwhat
    have hdata :
        evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock (.var "data") =
          .ok (.int (Int.ofNat (clipperFileUintData I).toNat)) := by
      simpa [locals] using
        evalExpr_clipperFileUint_data (v := v) (evm := evmLock) (I := I) (locals := locals)
          (by simp [locals])
    have hbufAssign :
        assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmLock
          .storage bufRef (.int (Int.ofNat (clipperFileUintData I).toNat)) =
            .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmStore) := by
      simpa only [locals, evmStore] using
        assign_clipperFileUint_buf v evmLock I (clipperFileUintData I)
    have hthen :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
          [.assign .storage bufRef (.var "data")]
          (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
      exact ExecBlock.consNormal (ExecStmt.assign hdata hbufAssign) ExecBlock.nil
    have hunlockRhs :
        evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmStore (.intLit 0) =
          .ok (.int 0) := by
      simp [evalExpr?, pure]
    have hunlockAssign :
        assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmStore
          .storage lockedRef (.int 0) =
            .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm2) := by
      simpa [locals, evm2, evmStore, evmLock, clipperFileUintWordPostState,
        storageStore_executionEnv,
        clipperFileUintLockedState] using
        assign_clipperFileUint_locked v evmStore I ⟨0⟩
    have hrest :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
          [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
            [.ite (.binary .eq (.var "what") tailParamLit)
              [.assign .storage tailRef (.var "data")]
              [.ite (.binary .eq (.var "what") cuspParamLit)
                [.assign .storage cuspRef (.var "data")]
                [.ite (.binary .eq (.var "what") chipParamLit)
                  [.assign .storage chipRef (wrap64 (.var "data"))]
                  [.ite (.binary .eq (.var "what") tipParamLit)
                    [.assign .storage tipRef (wrap192 (.var "data"))]
                    [.ite (.binary .eq (.var "what") stoppedParamLit)
                      [.assign .storage stoppedRef (.var "data")]
                      [.require (.boolLit false)]]]]]],
            .assign .storage lockedRef (.intLit 0)]
          (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
      exact ExecBlock.consNormal (ExecStmt.iteTrue hbufCond hthen)
        (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
    have hblock :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          fileUintTransition.body (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
      apply hprefix
      exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
    simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock
  · intro hperm
    exact ExecFuncBody.execBlockStatic (hprefix
      (ExecBlock.consStatic (ExecStmt.assignStatic hlockRhs hlockAssign
        (by simpa [evm0, initState] using hperm))))

theorem clipperFileUintBufSourceBody {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hwhat : clipperFileUintWhat I = clipperFileUintBufBytes) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileUintWordPostState evm0 ⟨5⟩ (clipperFileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm2 none) (immStore v) :=
  (clipperFileUintBufSourceBodySplit v hwv hauth hlocked).1 hwhat

set_option maxHeartbeats 1000000 in
theorem clipperFileUintTailSourceBody {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : clipperFileUintWhat I ≠ clipperFileUintBufBytes)
    (hwhat : clipperFileUintWhat I = clipperFileUintTailBytes) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileUintWordPostState evm0 ⟨6⟩ (clipperFileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm2 none) (immStore v) := by
  intro locals evm0 evm2
  let evmLock := clipperFileUintLockedState evm0
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨6⟩ (clipperFileUintData I)
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmLock) := by
    simpa [locals, evmLock, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evm0 I ⟨1⟩
  have hbufCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") bufParamLit) = .ok (.bool false) := by
    simpa [bufParamLit, clipperFileUintBufBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintBufBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotBuf
  have htailCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tailParamLit) = .ok (.bool true) := by
    simpa [tailParamLit, clipperFileUintTailBytes, locals] using
      evalExpr_clipperFileUint_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTailBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hwhat
  have hdata :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock (.var "data") =
        .ok (.int (Int.ofNat (clipperFileUintData I).toNat)) := by
    simpa [locals] using
      evalExpr_clipperFileUint_data (v := v) (evm := evmLock) (I := I) (locals := locals)
        (by simp [locals])
  have htailAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        .storage tailRef (.int (Int.ofNat (clipperFileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmStore) := by
    simpa only [locals, evmStore] using
      assign_clipperFileUint_tail v evmLock I (clipperFileUintData I)
  have hthen :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.assign .storage tailRef (.var "data")]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata htailAssign) ExecBlock.nil
  have helse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tailParamLit)
          [.assign .storage tailRef (.var "data")]
          [.ite (.binary .eq (.var "what") cuspParamLit)
            [.assign .storage cuspRef (.var "data")]
            [.ite (.binary .eq (.var "what") chipParamLit)
              [.assign .storage chipRef (wrap64 (.var "data"))]
              [.ite (.binary .eq (.var "what") tipParamLit)
                [.assign .storage tipRef (wrap192 (.var "data"))]
                [.ite (.binary .eq (.var "what") stoppedParamLit)
                  [.assign .storage stoppedRef (.var "data")]
                  [.require (.boolLit false)]]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue htailCond hthen) ExecBlock.nil
  have hunlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileUintWordPostState,
      storageStore_executionEnv, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
          [.ite (.binary .eq (.var "what") tailParamLit)
            [.assign .storage tailRef (.var "data")]
            [.ite (.binary .eq (.var "what") cuspParamLit)
              [.assign .storage cuspRef (.var "data")]
              [.ite (.binary .eq (.var "what") chipParamLit)
                [.assign .storage chipRef (wrap64 (.var "data"))]
                [.ite (.binary .eq (.var "what") tipParamLit)
                  [.assign .storage tipRef (wrap192 (.var "data"))]
                  [.ite (.binary .eq (.var "what") stoppedParamLit)
                    [.assign .storage stoppedRef (.var "data")]
                    [.require (.boolLit false)]]]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbufCond helse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileUintCuspSourceBody {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : clipperFileUintWhat I ≠ clipperFileUintBufBytes)
    (hnotTail : clipperFileUintWhat I ≠ clipperFileUintTailBytes)
    (hwhat : clipperFileUintWhat I = clipperFileUintCuspBytes) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileUintWordPostState evm0 ⟨7⟩ (clipperFileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm2 none) (immStore v) := by
  intro locals evm0 evm2
  let evmLock := clipperFileUintLockedState evm0
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨7⟩ (clipperFileUintData I)
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmLock) := by
    simpa [locals, evmLock, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evm0 I ⟨1⟩
  have hbufCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") bufParamLit) = .ok (.bool false) := by
    simpa [bufParamLit, clipperFileUintBufBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintBufBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotBuf
  have htailCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tailParamLit) = .ok (.bool false) := by
    simpa [tailParamLit, clipperFileUintTailBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTailBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotTail
  have hcuspCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") cuspParamLit) = .ok (.bool true) := by
    simpa [cuspParamLit, clipperFileUintCuspBytes, locals] using
      evalExpr_clipperFileUint_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintCuspBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hwhat
  have hdata :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock (.var "data") =
        .ok (.int (Int.ofNat (clipperFileUintData I).toNat)) := by
    simpa [locals] using
      evalExpr_clipperFileUint_data (v := v) (evm := evmLock) (I := I) (locals := locals)
        (by simp [locals])
  have hcuspAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        .storage cuspRef (.int (Int.ofNat (clipperFileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmStore) := by
    simpa only [locals, evmStore] using
      assign_clipperFileUint_cusp v evmLock I (clipperFileUintData I)
  have hthen :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.assign .storage cuspRef (.var "data")]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hcuspAssign) ExecBlock.nil
  have hcuspElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") cuspParamLit)
          [.assign .storage cuspRef (.var "data")]
          [.ite (.binary .eq (.var "what") chipParamLit)
            [.assign .storage chipRef (wrap64 (.var "data"))]
            [.ite (.binary .eq (.var "what") tipParamLit)
              [.assign .storage tipRef (wrap192 (.var "data"))]
              [.ite (.binary .eq (.var "what") stoppedParamLit)
                [.assign .storage stoppedRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcuspCond hthen) ExecBlock.nil
  have htailElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tailParamLit)
          [.assign .storage tailRef (.var "data")]
          [.ite (.binary .eq (.var "what") cuspParamLit)
            [.assign .storage cuspRef (.var "data")]
            [.ite (.binary .eq (.var "what") chipParamLit)
              [.assign .storage chipRef (wrap64 (.var "data"))]
              [.ite (.binary .eq (.var "what") tipParamLit)
                [.assign .storage tipRef (wrap192 (.var "data"))]
                [.ite (.binary .eq (.var "what") stoppedParamLit)
                  [.assign .storage stoppedRef (.var "data")]
                  [.require (.boolLit false)]]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse htailCond hcuspElse) ExecBlock.nil
  have hunlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileUintWordPostState,
      storageStore_executionEnv, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
          [.ite (.binary .eq (.var "what") tailParamLit)
            [.assign .storage tailRef (.var "data")]
            [.ite (.binary .eq (.var "what") cuspParamLit)
              [.assign .storage cuspRef (.var "data")]
              [.ite (.binary .eq (.var "what") chipParamLit)
                [.assign .storage chipRef (wrap64 (.var "data"))]
                [.ite (.binary .eq (.var "what") tipParamLit)
                  [.assign .storage tipRef (wrap192 (.var "data"))]
                  [.ite (.binary .eq (.var "what") stoppedParamLit)
                    [.assign .storage stoppedRef (.var "data")]
                    [.require (.boolLit false)]]]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbufCond htailElse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileUintChipSourceBody {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : clipperFileUintWhat I ≠ clipperFileUintBufBytes)
    (hnotTail : clipperFileUintWhat I ≠ clipperFileUintTailBytes)
    (hnotCusp : clipperFileUintWhat I ≠ clipperFileUintCuspBytes)
    (hwhat : clipperFileUintWhat I = clipperFileUintChipBytes) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileUintChipPostState evm0 (clipperFileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm2 none) (immStore v) := by
  intro locals evm0 evm2
  let evmLock := clipperFileUintLockedState evm0
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨8⟩
      (clipperFileUintChipWord
        (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨8⟩)
        (clipperFileUintData I))
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmLock) := by
    simpa [locals, evmLock, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evm0 I ⟨1⟩
  have hbufCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") bufParamLit) = .ok (.bool false) := by
    simpa [bufParamLit, clipperFileUintBufBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintBufBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotBuf
  have htailCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tailParamLit) = .ok (.bool false) := by
    simpa [tailParamLit, clipperFileUintTailBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTailBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotTail
  have hcuspCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") cuspParamLit) = .ok (.bool false) := by
    simpa [cuspParamLit, clipperFileUintCuspBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintCuspBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotCusp
  have hchipCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") chipParamLit) = .ok (.bool true) := by
    simpa [chipParamLit, clipperFileUintChipBytes, locals] using
      evalExpr_clipperFileUint_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintChipBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hwhat
  have hdata :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (wrap64 (.var "data")) = .ok (.int (Int.ofNat (clipperFileUintChipData I).toNat)) := by
    simpa [locals] using
      evalExpr_clipperFileUint_wrap64_data (v := v) (evm := evmLock) (I := I)
        (locals := locals) (by simp [locals])
  have hchipAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        .storage chipRef (.int (Int.ofNat (clipperFileUintChipData I).toNat)) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmStore) := by
    simpa only [locals, evmStore] using
      assign_clipperFileUint_chip v evmLock I
  have hthen :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.assign .storage chipRef (wrap64 (.var "data"))]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hchipAssign) ExecBlock.nil
  have hchipElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") chipParamLit)
          [.assign .storage chipRef (wrap64 (.var "data"))]
          [.ite (.binary .eq (.var "what") tipParamLit)
            [.assign .storage tipRef (wrap192 (.var "data"))]
            [.ite (.binary .eq (.var "what") stoppedParamLit)
              [.assign .storage stoppedRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hchipCond hthen) ExecBlock.nil
  have hcuspElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") cuspParamLit)
          [.assign .storage cuspRef (.var "data")]
          [.ite (.binary .eq (.var "what") chipParamLit)
            [.assign .storage chipRef (wrap64 (.var "data"))]
            [.ite (.binary .eq (.var "what") tipParamLit)
              [.assign .storage tipRef (wrap192 (.var "data"))]
              [.ite (.binary .eq (.var "what") stoppedParamLit)
                [.assign .storage stoppedRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcuspCond hchipElse) ExecBlock.nil
  have htailElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tailParamLit)
          [.assign .storage tailRef (.var "data")]
          [.ite (.binary .eq (.var "what") cuspParamLit)
            [.assign .storage cuspRef (.var "data")]
            [.ite (.binary .eq (.var "what") chipParamLit)
              [.assign .storage chipRef (wrap64 (.var "data"))]
              [.ite (.binary .eq (.var "what") tipParamLit)
                [.assign .storage tipRef (wrap192 (.var "data"))]
                [.ite (.binary .eq (.var "what") stoppedParamLit)
                  [.assign .storage stoppedRef (.var "data")]
                  [.require (.boolLit false)]]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse htailCond hcuspElse) ExecBlock.nil
  have hunlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileUintChipPostState,
      storageStore_executionEnv, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
          [.ite (.binary .eq (.var "what") tailParamLit)
            [.assign .storage tailRef (.var "data")]
            [.ite (.binary .eq (.var "what") cuspParamLit)
              [.assign .storage cuspRef (.var "data")]
              [.ite (.binary .eq (.var "what") chipParamLit)
                [.assign .storage chipRef (wrap64 (.var "data"))]
                [.ite (.binary .eq (.var "what") tipParamLit)
                  [.assign .storage tipRef (wrap192 (.var "data"))]
                  [.ite (.binary .eq (.var "what") stoppedParamLit)
                    [.assign .storage stoppedRef (.var "data")]
                    [.require (.boolLit false)]]]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbufCond htailElse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileUintTipSourceBody {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : clipperFileUintWhat I ≠ clipperFileUintBufBytes)
    (hnotTail : clipperFileUintWhat I ≠ clipperFileUintTailBytes)
    (hnotCusp : clipperFileUintWhat I ≠ clipperFileUintCuspBytes)
    (hnotChip : clipperFileUintWhat I ≠ clipperFileUintChipBytes)
    (hwhat : clipperFileUintWhat I = clipperFileUintTipBytes) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileUintTipPostState evm0 (clipperFileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm2 none) (immStore v) := by
  intro locals evm0 evm2
  let evmLock := clipperFileUintLockedState evm0
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨8⟩
      (clipperFileUintTipWord
        (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨8⟩)
        (clipperFileUintData I))
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmLock) := by
    simpa [locals, evmLock, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evm0 I ⟨1⟩
  have hbufCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") bufParamLit) = .ok (.bool false) := by
    simpa [bufParamLit, clipperFileUintBufBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintBufBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotBuf
  have htailCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tailParamLit) = .ok (.bool false) := by
    simpa [tailParamLit, clipperFileUintTailBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTailBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotTail
  have hcuspCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") cuspParamLit) = .ok (.bool false) := by
    simpa [cuspParamLit, clipperFileUintCuspBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintCuspBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotCusp
  have hchipCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") chipParamLit) = .ok (.bool false) := by
    simpa [chipParamLit, clipperFileUintChipBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintChipBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotChip
  have htipCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tipParamLit) = .ok (.bool true) := by
    simpa [tipParamLit, clipperFileUintTipBytes, locals] using
      evalExpr_clipperFileUint_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTipBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hwhat
  have hdata :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (wrap192 (.var "data")) = .ok (.int (Int.ofNat (clipperFileUintTipData I).toNat)) := by
    simpa [locals] using
      evalExpr_clipperFileUint_wrap192_data (v := v) (evm := evmLock) (I := I)
        (locals := locals) (by simp [locals])
  have htipAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        .storage tipRef (.int (Int.ofNat (clipperFileUintTipData I).toNat)) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmStore) := by
    simpa only [locals, evmStore] using
      assign_clipperFileUint_tip v evmLock I
  have hthen :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.assign .storage tipRef (wrap192 (.var "data"))]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata htipAssign) ExecBlock.nil
  have htipElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tipParamLit)
          [.assign .storage tipRef (wrap192 (.var "data"))]
          [.ite (.binary .eq (.var "what") stoppedParamLit)
            [.assign .storage stoppedRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue htipCond hthen) ExecBlock.nil
  have hchipElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") chipParamLit)
          [.assign .storage chipRef (wrap64 (.var "data"))]
          [.ite (.binary .eq (.var "what") tipParamLit)
            [.assign .storage tipRef (wrap192 (.var "data"))]
            [.ite (.binary .eq (.var "what") stoppedParamLit)
              [.assign .storage stoppedRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hchipCond htipElse) ExecBlock.nil
  have hcuspElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") cuspParamLit)
          [.assign .storage cuspRef (.var "data")]
          [.ite (.binary .eq (.var "what") chipParamLit)
            [.assign .storage chipRef (wrap64 (.var "data"))]
            [.ite (.binary .eq (.var "what") tipParamLit)
              [.assign .storage tipRef (wrap192 (.var "data"))]
              [.ite (.binary .eq (.var "what") stoppedParamLit)
                [.assign .storage stoppedRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcuspCond hchipElse) ExecBlock.nil
  have htailElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tailParamLit)
          [.assign .storage tailRef (.var "data")]
          [.ite (.binary .eq (.var "what") cuspParamLit)
            [.assign .storage cuspRef (.var "data")]
            [.ite (.binary .eq (.var "what") chipParamLit)
              [.assign .storage chipRef (wrap64 (.var "data"))]
              [.ite (.binary .eq (.var "what") tipParamLit)
                [.assign .storage tipRef (wrap192 (.var "data"))]
                [.ite (.binary .eq (.var "what") stoppedParamLit)
                  [.assign .storage stoppedRef (.var "data")]
                  [.require (.boolLit false)]]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse htailCond hcuspElse) ExecBlock.nil
  have hunlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileUintTipPostState,
      storageStore_executionEnv, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
          [.ite (.binary .eq (.var "what") tailParamLit)
            [.assign .storage tailRef (.var "data")]
            [.ite (.binary .eq (.var "what") cuspParamLit)
              [.assign .storage cuspRef (.var "data")]
              [.ite (.binary .eq (.var "what") chipParamLit)
                [.assign .storage chipRef (wrap64 (.var "data"))]
                [.ite (.binary .eq (.var "what") tipParamLit)
                  [.assign .storage tipRef (wrap192 (.var "data"))]
                  [.ite (.binary .eq (.var "what") stoppedParamLit)
                    [.assign .storage stoppedRef (.var "data")]
                    [.require (.boolLit false)]]]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbufCond htailElse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileUintStoppedSourceBody {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : clipperFileUintWhat I ≠ clipperFileUintBufBytes)
    (hnotTail : clipperFileUintWhat I ≠ clipperFileUintTailBytes)
    (hnotCusp : clipperFileUintWhat I ≠ clipperFileUintCuspBytes)
    (hnotChip : clipperFileUintWhat I ≠ clipperFileUintChipBytes)
    (hnotTip : clipperFileUintWhat I ≠ clipperFileUintTipBytes)
    (hwhat : clipperFileUintWhat I = clipperFileUintStoppedBytes) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileUintWordPostState evm0 ⟨14⟩ (clipperFileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm2 none) (immStore v) := by
  intro locals evm0 evm2
  let evmLock := clipperFileUintLockedState evm0
  let evmStore :=
    Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨14⟩ (clipperFileUintData I)
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmLock) := by
    simpa [locals, evmLock, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evm0 I ⟨1⟩
  have hbufCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") bufParamLit) = .ok (.bool false) := by
    simpa [bufParamLit, clipperFileUintBufBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintBufBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotBuf
  have htailCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tailParamLit) = .ok (.bool false) := by
    simpa [tailParamLit, clipperFileUintTailBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTailBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotTail
  have hcuspCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") cuspParamLit) = .ok (.bool false) := by
    simpa [cuspParamLit, clipperFileUintCuspBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintCuspBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotCusp
  have hchipCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") chipParamLit) = .ok (.bool false) := by
    simpa [chipParamLit, clipperFileUintChipBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintChipBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotChip
  have htipCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tipParamLit) = .ok (.bool false) := by
    simpa [tipParamLit, clipperFileUintTipBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTipBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotTip
  have hstoppedCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") stoppedParamLit) = .ok (.bool true) := by
    simpa [stoppedParamLit, clipperFileUintStoppedBytes, locals] using
      evalExpr_clipperFileUint_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintStoppedBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hwhat
  have hdata :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock (.var "data") =
        .ok (.int (Int.ofNat (clipperFileUintData I).toNat)) := by
    simpa [locals] using
      evalExpr_clipperFileUint_data (v := v) (evm := evmLock) (I := I) (locals := locals)
        (by simp [locals])
  have hstoppedAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        .storage stoppedRef (.int (Int.ofNat (clipperFileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmStore) := by
    simpa only [locals, evmStore] using
      assign_clipperFileUint_stopped v evmLock I (clipperFileUintData I)
  have hthen :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.assign .storage stoppedRef (.var "data")]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hstoppedAssign) ExecBlock.nil
  have hstoppedElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") stoppedParamLit)
          [.assign .storage stoppedRef (.var "data")]
          [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hstoppedCond hthen) ExecBlock.nil
  have htipElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tipParamLit)
          [.assign .storage tipRef (wrap192 (.var "data"))]
          [.ite (.binary .eq (.var "what") stoppedParamLit)
            [.assign .storage stoppedRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse htipCond hstoppedElse) ExecBlock.nil
  have hchipElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") chipParamLit)
          [.assign .storage chipRef (wrap64 (.var "data"))]
          [.ite (.binary .eq (.var "what") tipParamLit)
            [.assign .storage tipRef (wrap192 (.var "data"))]
            [.ite (.binary .eq (.var "what") stoppedParamLit)
              [.assign .storage stoppedRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hchipCond htipElse) ExecBlock.nil
  have hcuspElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") cuspParamLit)
          [.assign .storage cuspRef (.var "data")]
          [.ite (.binary .eq (.var "what") chipParamLit)
            [.assign .storage chipRef (wrap64 (.var "data"))]
            [.ite (.binary .eq (.var "what") tipParamLit)
              [.assign .storage tipRef (wrap192 (.var "data"))]
              [.ite (.binary .eq (.var "what") stoppedParamLit)
                [.assign .storage stoppedRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcuspCond hchipElse) ExecBlock.nil
  have htailElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tailParamLit)
          [.assign .storage tailRef (.var "data")]
          [.ite (.binary .eq (.var "what") cuspParamLit)
            [.assign .storage cuspRef (.var "data")]
            [.ite (.binary .eq (.var "what") chipParamLit)
              [.assign .storage chipRef (wrap64 (.var "data"))]
              [.ite (.binary .eq (.var "what") tipParamLit)
                [.assign .storage tipRef (wrap192 (.var "data"))]
                [.ite (.binary .eq (.var "what") stoppedParamLit)
                  [.assign .storage stoppedRef (.var "data")]
                  [.require (.boolLit false)]]]]]]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse htailCond hcuspElse) ExecBlock.nil
  have hunlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileUintWordPostState,
      storageStore_executionEnv, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
          [.ite (.binary .eq (.var "what") tailParamLit)
            [.assign .storage tailRef (.var "data")]
            [.ite (.binary .eq (.var "what") cuspParamLit)
              [.assign .storage cuspRef (.var "data")]
              [.ite (.binary .eq (.var "what") chipParamLit)
                [.assign .storage chipRef (wrap64 (.var "data"))]
                [.ite (.binary .eq (.var "what") tipParamLit)
                  [.assign .storage tipRef (wrap192 (.var "data"))]
                  [.ite (.binary .eq (.var "what") stoppedParamLit)
                    [.assign .storage stoppedRef (.var "data")]
                    [.require (.boolLit false)]]]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbufCond htailElse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals, immutables := immStore v } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileUintUnrecognizedSourceBody {σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : clipperFileUintWhat I ≠ clipperFileUintBufBytes)
    (hnotTail : clipperFileUintWhat I ≠ clipperFileUintTailBytes)
    (hnotCusp : clipperFileUintWhat I ≠ clipperFileUintCuspBytes)
    (hnotChip : clipperFileUintWhat I ≠ clipperFileUintChipBytes)
    (hnotTip : clipperFileUintWhat I ≠ clipperFileUintTipBytes)
    (hnotStopped : clipperFileUintWhat I ≠ clipperFileUintStoppedBytes) :
    let locals := clipperFileUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted (immStore v) := by
  intro locals evm0
  let evmLock := clipperFileUintLockedState evm0
  have hauthEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileUint_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileUint_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evmLock) := by
    simpa [locals, evmLock, clipperFileUintLockedState] using
      assign_clipperFileUint_locked v evm0 I ⟨1⟩
  have hbufCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") bufParamLit) = .ok (.bool false) := by
    simpa [bufParamLit, clipperFileUintBufBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintBufBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotBuf
  have htailCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tailParamLit) = .ok (.bool false) := by
    simpa [tailParamLit, clipperFileUintTailBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTailBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotTail
  have hcuspCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") cuspParamLit) = .ok (.bool false) := by
    simpa [cuspParamLit, clipperFileUintCuspBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintCuspBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotCusp
  have hchipCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") chipParamLit) = .ok (.bool false) := by
    simpa [chipParamLit, clipperFileUintChipBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintChipBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotChip
  have htipCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") tipParamLit) = .ok (.bool false) := by
    simpa [tipParamLit, clipperFileUintTipBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintTipBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotTip
  have hstoppedCond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.binary .eq (.var "what") stoppedParamLit) = .ok (.bool false) := by
    simpa [stoppedParamLit, clipperFileUintStoppedBytes, locals] using
      evalExpr_clipperFileUint_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileUintStoppedBytes)
        (by simpa [locals] using clipperFileUintLocals_get_what I) hnotStopped
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evmLock
        (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hstoppedElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") stoppedParamLit)
          [.assign .storage stoppedRef (.var "data")]
          [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hstoppedCond
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  have htipElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tipParamLit)
          [.assign .storage tipRef (wrap192 (.var "data"))]
          [.ite (.binary .eq (.var "what") stoppedParamLit)
            [.assign .storage stoppedRef (.var "data")]
            [.require (.boolLit false)]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse htipCond hstoppedElse)
  have hchipElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") chipParamLit)
          [.assign .storage chipRef (wrap64 (.var "data"))]
          [.ite (.binary .eq (.var "what") tipParamLit)
            [.assign .storage tipRef (wrap192 (.var "data"))]
            [.ite (.binary .eq (.var "what") stoppedParamLit)
              [.assign .storage stoppedRef (.var "data")]
              [.require (.boolLit false)]]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hchipCond htipElse)
  have hcuspElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") cuspParamLit)
          [.assign .storage cuspRef (.var "data")]
          [.ite (.binary .eq (.var "what") chipParamLit)
            [.assign .storage chipRef (wrap64 (.var "data"))]
            [.ite (.binary .eq (.var "what") tipParamLit)
              [.assign .storage tipRef (wrap192 (.var "data"))]
              [.ite (.binary .eq (.var "what") stoppedParamLit)
                [.assign .storage stoppedRef (.var "data")]
                [.require (.boolLit false)]]]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcuspCond hchipElse)
  have htailElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") tailParamLit)
          [.assign .storage tailRef (.var "data")]
          [.ite (.binary .eq (.var "what") cuspParamLit)
            [.assign .storage cuspRef (.var "data")]
            [.ite (.binary .eq (.var "what") chipParamLit)
              [.assign .storage chipRef (wrap64 (.var "data"))]
              [.ite (.binary .eq (.var "what") tipParamLit)
                [.assign .storage tipRef (wrap192 (.var "data"))]
                [.ite (.binary .eq (.var "what") stoppedParamLit)
                  [.assign .storage stoppedRef (.var "data")]
                  [.require (.boolLit false)]]]]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse htailCond hcuspElse)
  have hrest :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evmLock
        [.ite (.binary .eq (.var "what") bufParamLit) [.assign .storage bufRef (.var "data")]
          [.ite (.binary .eq (.var "what") tailParamLit)
            [.assign .storage tailRef (.var "data")]
            [.ite (.binary .eq (.var "what") cuspParamLit)
              [.assign .storage cuspRef (.var "data")]
              [.ite (.binary .eq (.var "what") chipParamLit)
                [.assign .storage chipRef (wrap64 (.var "data"))]
                [.ite (.binary .eq (.var "what") tipParamLit)
                  [.assign .storage tipRef (wrap192 (.var "data"))]
                  [.ite (.binary .eq (.var "what") stoppedParamLit)
                    [.assign .storage stoppedRef (.var "data")]
                    [.require (.boolLit false)]]]]]],
          .assign .storage lockedRef (.intLit 0)]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hbufCond htailElse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileUintTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Clipper
