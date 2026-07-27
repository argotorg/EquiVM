import Benchmarks.Dss.Clipper.FileAddressBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperFileAddressAuthSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩) :
    let locals := clipperFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      .reverted := by
  intro locals evm0
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileAddress_auth_false v evm0 I (by simp [evm0, initState]) hauth
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body .reverted := by
    simpa [fileAddressTransition, nonpayable, auth, lockPrefix] using
      nonpayableSecondRequireReverts
        (cfg := config v)
        (solm := { contract := contract v, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := lockPrefix ++
          [.ite (.binary .eq (.var "what") spotterParamLit)
            [.assign .storage spotterRef (.var "data")]
            [.ite (.binary .eq (.var "what") dogParamLit)
              [.assign .storage dogRef (.var "data")]
              [.ite (.binary .eq (.var "what") vowParamLit)
                [.assign .storage vowRef (.var "data")]
                [.ite (.binary .eq (.var "what") calcParamLit)
                  [.assign .storage calcRef (.var "data")]
                  [.require (.boolLit false)]]]],
            .assign .storage lockedRef (.intLit 0)])
        (by simp [evm0, initState]; exact hwv)
        hauthEval
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperFileAddressLockedSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩) :
    let locals := clipperFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      .reverted := by
  intro locals evm0
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileAddress_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileAddress_locked_zero_false v evm0 I hlocked
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hlockedEval)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressSpotterSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hwhat : clipperFileAddressWhat I = clipperFileAddressSpotterBytes) :
    let locals := clipperFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileAddressPostState evm0 ⟨3⟩ (clipperFileAddressDataMaskedWord I)
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      (.returned { contract := contract v, locals := locals } evm2 none) := by
  intro locals evm0 evm2
  let evmLock := clipperFileAddressLockedState evm0
  let evmStore := Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨3⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨3⟩)
      (clipperFileAddressDataMaskedWord I))
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileAddress_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileAddress_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evm0 I ⟨1⟩
  have hspotterCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") spotterParamLit) = .ok (.bool true) := by
    simpa [spotterParamLit, clipperFileAddressSpotterBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressSpotterBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hwhat
  have hdata :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock (.var "data") =
        .ok (.address (clipperFileAddressData I)) := by
    simpa [locals] using
      evalExpr_clipperFileAddress_data (v := v) (evm := evmLock) (I := I)
        (locals := locals) (by simp [locals])
  have hspotterAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmLock
        .storage spotterRef (.address (clipperFileAddressData I)) =
          .ok ({ contract := contract v, locals := locals }, evmStore) := by
    simpa [locals, evmStore] using assign_clipperFileAddress_spotter v evmLock I
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.assign .storage spotterRef (.var "data")]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hspotterAssign) ExecBlock.nil
  have hunlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract v, locals := locals }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileAddressPostState,
      storageStore_executionEnv, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") spotterParamLit)
          [.assign .storage spotterRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogParamLit)
            [.assign .storage dogRef (.var "data")]
            [.ite (.binary .eq (.var "what") vowParamLit)
              [.assign .storage vowRef (.var "data")]
              [.ite (.binary .eq (.var "what") calcParamLit)
                [.assign .storage calcRef (.var "data")]
                [.require (.boolLit false)]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract v, locals := locals } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hspotterCond hthen)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body (.ok { contract := contract v, locals := locals } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressDogSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotSpotter : clipperFileAddressWhat I ≠ clipperFileAddressSpotterBytes)
    (hwhat : clipperFileAddressWhat I = clipperFileAddressDogBytes) :
    let locals := clipperFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileAddressPostState evm0 ⟨1⟩ (clipperFileAddressDataMaskedWord I)
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      (.returned { contract := contract v, locals := locals } evm2 none) := by
  intro locals evm0 evm2
  let evmLock := clipperFileAddressLockedState evm0
  let evmStore := Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨1⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨1⟩)
      (clipperFileAddressDataMaskedWord I))
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileAddress_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileAddress_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evm0 I ⟨1⟩
  have hspotterCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") spotterParamLit) = .ok (.bool false) := by
    simpa [spotterParamLit, clipperFileAddressSpotterBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressSpotterBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotSpotter
  have hdogCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") dogParamLit) = .ok (.bool true) := by
    simpa [dogParamLit, clipperFileAddressDogBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressDogBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hwhat
  have hdata :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock (.var "data") =
        .ok (.address (clipperFileAddressData I)) := by
    simpa [locals] using
      evalExpr_clipperFileAddress_data (v := v) (evm := evmLock) (I := I)
        (locals := locals) (by simp [locals])
  have hdogAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmLock
        .storage dogRef (.address (clipperFileAddressData I)) =
          .ok ({ contract := contract v, locals := locals }, evmStore) := by
    simpa [locals, evmStore] using assign_clipperFileAddress_dog v evmLock I
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.assign .storage dogRef (.var "data")]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hdogAssign) ExecBlock.nil
  have hdogElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") dogParamLit)
          [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowParamLit)
            [.assign .storage vowRef (.var "data")]
            [.ite (.binary .eq (.var "what") calcParamLit)
              [.assign .storage calcRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hdogCond hthen) ExecBlock.nil
  have hunlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract v, locals := locals }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileAddressPostState,
      storageStore_executionEnv, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") spotterParamLit)
          [.assign .storage spotterRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogParamLit)
            [.assign .storage dogRef (.var "data")]
            [.ite (.binary .eq (.var "what") vowParamLit)
              [.assign .storage vowRef (.var "data")]
              [.ite (.binary .eq (.var "what") calcParamLit)
                [.assign .storage calcRef (.var "data")]
                [.require (.boolLit false)]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract v, locals := locals } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hspotterCond hdogElse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body (.ok { contract := contract v, locals := locals } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressVowSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotSpotter : clipperFileAddressWhat I ≠ clipperFileAddressSpotterBytes)
    (hnotDog : clipperFileAddressWhat I ≠ clipperFileAddressDogBytes)
    (hwhat : clipperFileAddressWhat I = clipperFileAddressVowBytes) :
    let locals := clipperFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileAddressPostState evm0 ⟨2⟩ (clipperFileAddressDataMaskedWord I)
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      (.returned { contract := contract v, locals := locals } evm2 none) := by
  intro locals evm0 evm2
  let evmLock := clipperFileAddressLockedState evm0
  let evmStore := Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨2⟩)
      (clipperFileAddressDataMaskedWord I))
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileAddress_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileAddress_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evm0 I ⟨1⟩
  have hspotterCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") spotterParamLit) = .ok (.bool false) := by
    simpa [spotterParamLit, clipperFileAddressSpotterBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressSpotterBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotSpotter
  have hdogCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") dogParamLit) = .ok (.bool false) := by
    simpa [dogParamLit, clipperFileAddressDogBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressDogBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotDog
  have hvowCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool true) := by
    simpa [vowParamLit, clipperFileAddressVowBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressVowBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hwhat
  have hdata :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock (.var "data") =
        .ok (.address (clipperFileAddressData I)) := by
    simpa [locals] using
      evalExpr_clipperFileAddress_data (v := v) (evm := evmLock) (I := I)
        (locals := locals) (by simp [locals])
  have hvowAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmLock
        .storage vowRef (.address (clipperFileAddressData I)) =
          .ok ({ contract := contract v, locals := locals }, evmStore) := by
    simpa [locals, evmStore] using assign_clipperFileAddress_vow v evmLock I
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.assign .storage vowRef (.var "data")]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hvowAssign) ExecBlock.nil
  have hvowElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") vowParamLit)
          [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") calcParamLit)
            [.assign .storage calcRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hvowCond hthen) ExecBlock.nil
  have hdogElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") dogParamLit)
          [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowParamLit)
            [.assign .storage vowRef (.var "data")]
            [.ite (.binary .eq (.var "what") calcParamLit)
              [.assign .storage calcRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdogCond hvowElse) ExecBlock.nil
  have hunlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract v, locals := locals }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileAddressPostState,
      storageStore_executionEnv, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") spotterParamLit)
          [.assign .storage spotterRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogParamLit)
            [.assign .storage dogRef (.var "data")]
            [.ite (.binary .eq (.var "what") vowParamLit)
              [.assign .storage vowRef (.var "data")]
              [.ite (.binary .eq (.var "what") calcParamLit)
                [.assign .storage calcRef (.var "data")]
                [.require (.boolLit false)]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract v, locals := locals } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hspotterCond hdogElse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body (.ok { contract := contract v, locals := locals } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressCalcSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotSpotter : clipperFileAddressWhat I ≠ clipperFileAddressSpotterBytes)
    (hnotDog : clipperFileAddressWhat I ≠ clipperFileAddressDogBytes)
    (hnotVow : clipperFileAddressWhat I ≠ clipperFileAddressVowBytes)
    (hwhat : clipperFileAddressWhat I = clipperFileAddressCalcBytes) :
    let locals := clipperFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm2 := clipperFileAddressPostState evm0 ⟨4⟩ (clipperFileAddressDataMaskedWord I)
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      (.returned { contract := contract v, locals := locals } evm2 none) := by
  intro locals evm0 evm2
  let evmLock := clipperFileAddressLockedState evm0
  let evmStore := Solm.EVM.storageStore evmLock evmLock.executionEnv.codeOwner ⟨4⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner ⟨4⟩)
      (clipperFileAddressDataMaskedWord I))
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileAddress_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileAddress_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evm0 I ⟨1⟩
  have hspotterCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") spotterParamLit) = .ok (.bool false) := by
    simpa [spotterParamLit, clipperFileAddressSpotterBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressSpotterBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotSpotter
  have hdogCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") dogParamLit) = .ok (.bool false) := by
    simpa [dogParamLit, clipperFileAddressDogBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressDogBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotDog
  have hvowCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool false) := by
    simpa [vowParamLit, clipperFileAddressVowBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressVowBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotVow
  have hcalcCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") calcParamLit) = .ok (.bool true) := by
    simpa [calcParamLit, clipperFileAddressCalcBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_true (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressCalcBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hwhat
  have hdata :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock (.var "data") =
        .ok (.address (clipperFileAddressData I)) := by
    simpa [locals] using
      evalExpr_clipperFileAddress_data (v := v) (evm := evmLock) (I := I)
        (locals := locals) (by simp [locals])
  have hcalcAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmLock
        .storage calcRef (.address (clipperFileAddressData I)) =
          .ok ({ contract := contract v, locals := locals }, evmStore) := by
    simpa [locals, evmStore] using assign_clipperFileAddress_calc v evmLock I
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.assign .storage calcRef (.var "data")]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hcalcAssign) ExecBlock.nil
  have hcalcElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") calcParamLit)
          [.assign .storage calcRef (.var "data")]
          [.require (.boolLit false)]]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcalcCond hthen) ExecBlock.nil
  have hvowElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") vowParamLit)
          [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") calcParamLit)
            [.assign .storage calcRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvowCond hcalcElse) ExecBlock.nil
  have hdogElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") dogParamLit)
          [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowParamLit)
            [.assign .storage vowRef (.var "data")]
            [.ite (.binary .eq (.var "what") calcParamLit)
              [.assign .storage calcRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract v, locals := locals } evmStore) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdogCond hvowElse) ExecBlock.nil
  have hunlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evmStore (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hunlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evmStore
        .storage lockedRef (.int 0) =
          .ok ({ contract := contract v, locals := locals }, evm2) := by
    simpa [locals, evm2, evmStore, evmLock, clipperFileAddressPostState,
      storageStore_executionEnv, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evmStore I ⟨0⟩
  have hrest :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") spotterParamLit)
          [.assign .storage spotterRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogParamLit)
            [.assign .storage dogRef (.var "data")]
            [.ite (.binary .eq (.var "what") vowParamLit)
              [.assign .storage vowRef (.var "data")]
              [.ite (.binary .eq (.var "what") calcParamLit)
                [.assign .storage calcRef (.var "data")]
                [.require (.boolLit false)]]]],
          .assign .storage lockedRef (.intLit 0)]
        (.ok { contract := contract v, locals := locals } evm2) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hspotterCond hdogElse)
      (ExecBlock.consNormal (ExecStmt.assign hunlockRhs hunlockAssign) ExecBlock.nil)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body (.ok { contract := contract v, locals := locals } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0, evm2] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressUnrecognizedSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotSpotter : clipperFileAddressWhat I ≠ clipperFileAddressSpotterBytes)
    (hnotDog : clipperFileAddressWhat I ≠ clipperFileAddressDogBytes)
    (hnotVow : clipperFileAddressWhat I ≠ clipperFileAddressVowBytes)
    (hnotCalc : clipperFileAddressWhat I ≠ clipperFileAddressCalcBytes) :
    let locals := clipperFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      .reverted := by
  intro locals evm0
  let evmLock := clipperFileAddressLockedState evm0
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperFileAddress_auth_true v evm0 I (by simp [evm0, initState]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperFileAddress_locked_zero_true v evm0 I hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock, clipperFileAddressLockedState] using
      assign_clipperFileAddress_locked v evm0 I ⟨1⟩
  have hspotterCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") spotterParamLit) = .ok (.bool false) := by
    simpa [spotterParamLit, clipperFileAddressSpotterBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressSpotterBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotSpotter
  have hdogCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") dogParamLit) = .ok (.bool false) := by
    simpa [dogParamLit, clipperFileAddressDogBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressDogBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotDog
  have hvowCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool false) := by
    simpa [vowParamLit, clipperFileAddressVowBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressVowBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotVow
  have hcalcCond :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .eq (.var "what") calcParamLit) = .ok (.bool false) := by
    simpa [calcParamLit, clipperFileAddressCalcBytes, locals] using
      evalExpr_clipperFileAddress_what_eq_false (v := v) (evm := evmLock) (I := I)
        (locals := locals) (bs := clipperFileAddressCalcBytes)
        (by simpa [locals] using clipperFileAddressLocals_get_what I) hnotCalc
  have hreqFalse :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hcalcElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") calcParamLit)
          [.assign .storage calcRef (.var "data")]
          [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcalcCond
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  have hvowElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") vowParamLit)
          [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") calcParamLit)
            [.assign .storage calcRef (.var "data")]
            [.require (.boolLit false)]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hvowCond hcalcElse)
  have hdogElse :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") dogParamLit)
          [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowParamLit)
            [.assign .storage vowRef (.var "data")]
            [.ite (.binary .eq (.var "what") calcParamLit)
              [.assign .storage calcRef (.var "data")]
              [.require (.boolLit false)]]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hdogCond hvowElse)
  have hrest :
      ExecBlock (config v) { contract := contract v, locals := locals } evmLock
        [.ite (.binary .eq (.var "what") spotterParamLit)
          [.assign .storage spotterRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogParamLit)
            [.assign .storage dogRef (.var "data")]
            [.ite (.binary .eq (.var "what") vowParamLit)
              [.assign .storage vowRef (.var "data")]
              [.ite (.binary .eq (.var "what") calcParamLit)
                [.assign .storage calcRef (.var "data")]
                [.require (.boolLit false)]]]],
          .assign .storage lockedRef (.intLit 0)]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hspotterCond hdogElse)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) hrest
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Clipper
