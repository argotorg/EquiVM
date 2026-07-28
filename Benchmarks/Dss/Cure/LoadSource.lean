import Benchmarks.Dss.Cure.LoadBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cure

theorem cureLoadSourceBodyStillLiveRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I ≠ ⟨0⟩) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (loadLocals I)
      loadTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hguard := evalExpr_loadLiveEqZero_false evm0 I hliveLoad
  have hblock := nonpayableSecondRequireReverts
    (cfg := config) (solm := { contract := contract, locals := loadLocals I })
    (evm := evm0)
    (guard := .binary .eq (.storage liveRef) (.intLit 0))
    (rest :=
      .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
      .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
      checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
      [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
        .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
        .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
        .assign .storage sayRef (.var "sayNew"),
        .ite
          (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
          [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
            .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
          [] ])
    (by simp [evm0, initState]; exact hwv)
    hguard
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureLoadSourceBodyPosZeroRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I = ⟨0⟩) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (loadLocals I)
      loadTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_false evm0 I hposLoad
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPos)
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureLoadSourceBodyNoCodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I ≠ ⟨0⟩)
    (hnoCode : extCodeSizeWord σ (loadKey I) = ⟨0⟩) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (loadLocals I)
      loadTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_true evm0 I hposLoad
  have holdAmt := evalExpr_loadAmtStorage evm0 I
  let oldAmtVal : Value :=
    .int (Int.ofNat
      (Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)).toNat)
  let localsOld : Store := (loadLocals I).insert "oldAmt_" oldAmtVal
  have hguardCall :
      evalExpr? config { contract := contract, locals := localsOld } evm0
        (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool false) := by
    have hsrc : localsOld.get? "src" = some (.address (loadSrc I)) := by
      change ((loadLocals I).insert "oldAmt_" oldAmtVal).get? "src" =
        some (.address (loadSrc I))
      rw [store_get_ne (loadLocals I) (k := "oldAmt_") (a := "src") oldAmtVal (by native_decide)]
      simp [loadLocals]
    simpa [evm0, localsOld] using
      evalExpr_loadExtCodeSizeGtZero_false_of_src
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (locals := localsOld) hsrc hnoCode
  have hcall :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false))
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallVarNoCode
        (cfg := config) (C := contract) (evm := evm0) (locals := localsOld)
        (receiver := "src") (retVar := "newAmt_") (name := "cure") (sendVal := 0)
        (args := []) (perm := false) hguardCall
  have hcallTail :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    exact Reasoning.Refinement.execBlock_append_term hcall (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := oldAmtVal) ?_) ?_
    · simpa [oldAmtVal] using holdAmt
    simpa [localsOld, oldAmtVal] using hcallTail
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureLoadSourceBodyCallFailureRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I ≠ ⟨0⟩)
    (hcode : extCodeSizeWord σ (loadKey I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (loadSrc I)) "cure" 0 []
        (false, evmCall, out) false) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (loadLocals I)
      loadTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_true evm0 I hposLoad
  have holdAmt := evalExpr_loadAmtStorage evm0 I
  let oldAmtVal : Value :=
    .int (Int.ofNat
      (Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)).toNat)
  let localsOld : Store := (loadLocals I).insert "oldAmt_" oldAmtVal
  have hsrc : localsOld.get? "src" = some (.address (loadSrc I)) := by
    change ((loadLocals I).insert "oldAmt_" oldAmtVal).get? "src" =
      some (.address (loadSrc I))
    rw [store_get_ne (loadLocals I) (k := "oldAmt_") (a := "src") oldAmtVal
      (by native_decide)]
    simp [loadLocals]
  have hguardCall :
      evalExpr? config { contract := contract, locals := localsOld } evm0
        (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, localsOld] using
      evalExpr_loadExtCodeSizeGtZero_true_of_src
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (locals := localsOld) hsrc hcode
  have hcallBlock :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false))
        .reverted := by
    simpa [checkedExternalCallStmts, evm0] using
      checkedExternalCallVarFailure
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmCall)
        (locals := localsOld) (receiver := "src") (retVar := "newAmt_")
        (name := "cure") (target := loadSrc I) (sendVal := 0) (args := [])
        (argVals := []) (out := out) (perm := false) hguardCall hsrc
        (by rfl) hcall
  have hcallTail :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    exact Reasoning.Refinement.execBlock_append_term hcallBlock (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := oldAmtVal) ?_) ?_
    · simpa [oldAmtVal] using holdAmt
    simpa [localsOld, oldAmtVal] using hcallTail
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureLoadSourceBodyReturnDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I ≠ ⟨0⟩)
    (hcode : extCodeSizeWord σ (loadKey I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (loadSrc I)) "cure" 0 []
        (true, evmCall, out) false)
    (hdec : config.externalABI.decode? "cure" out = none) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (loadLocals I)
      loadTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_true evm0 I hposLoad
  have holdAmt := evalExpr_loadAmtStorage evm0 I
  let oldAmtVal : Value :=
    .int (Int.ofNat
      (Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)).toNat)
  let localsOld : Store := (loadLocals I).insert "oldAmt_" oldAmtVal
  have hsrc : localsOld.get? "src" = some (.address (loadSrc I)) := by
    change ((loadLocals I).insert "oldAmt_" oldAmtVal).get? "src" =
      some (.address (loadSrc I))
    rw [store_get_ne (loadLocals I) (k := "oldAmt_") (a := "src") oldAmtVal
      (by native_decide)]
    simp [loadLocals]
  have hguardCall :
      evalExpr? config { contract := contract, locals := localsOld } evm0
        (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, localsOld] using
      evalExpr_loadExtCodeSizeGtZero_true_of_src
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (locals := localsOld) hsrc hcode
  have hargs :
      evalExprs? config { contract := contract, locals := localsOld } evm0 [] = .ok [] := by
    rfl
  have hcallBlock :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false))
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallVarDecodeRevert
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmCall)
        (locals := localsOld) (receiver := "src") (retVar := "newAmt_")
        (name := "cure") (target := loadSrc I) (sendVal := 0) (args := [])
        (argVals := []) (out := out) (perm := false) hguardCall hsrc hargs hcall hdec
  have hcallTail :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    exact Reasoning.Refinement.execBlock_append_term hcallBlock (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := oldAmtVal) ?_) ?_
    · simpa [oldAmtVal] using holdAmt
    simpa [localsOld, oldAmtVal] using hcallTail
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureLoadSourceBodySubRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCall : EVM.State} {out : ByteArray} {newAmt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I ≠ ⟨0⟩)
    (hcode : extCodeSizeWord σ (loadKey I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (loadSrc I)) "cure" 0 []
        (true, evmCall, out) false)
    (hdec :
      config.externalABI.decode? "cure" out =
        some [.int (Int.ofNat newAmt.toNat)])
    (hunder :
      (Solm.EVM.storageLoad
        (Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner (loadAmtSlotFor I)
          newAmt)
        evmCall.executionEnv.codeOwner ⟨9⟩).toNat <
        (Solm.EVM.storageLoad
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner (loadAmtSlotFor I)).toNat) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (loadLocals I)
      loadTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_true evm0 I hposLoad
  have holdAmt := evalExpr_loadAmtStorage evm0 I
  let oldAmt :=
    Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)
  let oldAmtVal : Value := .int (Int.ofNat oldAmt.toNat)
  let localsOld : Store := (loadLocals I).insert "oldAmt_" oldAmtVal
  let localsNew : Store := localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))
  let evmAmt := Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
    (loadAmtSlotFor I) newAmt
  have hsrc : localsOld.get? "src" = some (.address (loadSrc I)) := by
    change ((loadLocals I).insert "oldAmt_" oldAmtVal).get? "src" =
      some (.address (loadSrc I))
    rw [store_get_ne (loadLocals I) (k := "oldAmt_") (a := "src") oldAmtVal
      (by native_decide)]
    simp [loadLocals]
  have hguardCall :
      evalExpr? config { contract := contract, locals := localsOld } evm0
        (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, localsOld] using
      evalExpr_loadExtCodeSizeGtZero_true_of_src
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (locals := localsOld) hsrc hcode
  have hargs :
      evalExprs? config { contract := contract, locals := localsOld } evm0 [] = .ok [] := by
    rfl
  have hcallBlock :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false))
        (.ok { contract := contract, locals := localsNew } evmCall) := by
    simpa [checkedExternalCallStmts, localsNew] using
      checkedExternalCallVarSuccess
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmCall)
        (locals := localsOld) (receiver := "src") (retVar := "newAmt_")
        (name := "cure") (target := loadSrc I) (sendVal := 0) (args := [])
        (argVals := []) (out := out) (perm := false)
        (value := [.int (Int.ofNat newAmt.toNat)])
        hguardCall hsrc hargs hcall hdec
  have hnewVar :
      evalExpr? config { contract := contract, locals := localsNew } evmCall (.var "newAmt_") =
        .ok (.int (Int.ofNat newAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmCall) (locals := localsNew)
      (name := "newAmt_") (value := newAmt)
      (by
        change (localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))).get? "newAmt_" =
          some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_self])
  have hassignAmt :
      assignStorageRef? config { contract := contract, locals := localsNew } evmCall
        .storage (amtRef (.var "src")) (.int (Int.ofNat newAmt.toNat)) =
          .ok ({ contract := contract, locals := localsNew }, evmAmt) := by
    have hbase : localsNew.get? "amt" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "amt" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    have hsrcNew : localsNew.get? "src" = some (.address (loadSrc I)) := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "src" = some (.address (loadSrc I))
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt] using assign_loadAmtStorage (evm := evmCall) (locals := localsNew)
      I newAmt hbase hsrcNew
  have holdVar :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.var "oldAmt_") =
        .ok (.int (Int.ofNat oldAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsNew)
      (name := "oldAmt_") (value := oldAmt)
      (by
        change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
          (.int (Int.ofNat newAmt.toNat))).get? "oldAmt_" =
            some (.int (Int.ofNat oldAmt.toNat))
        rw [store_get_ne _ _ (by native_decide), store_get_self])
  have hsay :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.storage sayRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩).toNat)) := by
    have hbase : localsNew.get? "say" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "say" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt] using evalExpr_loadSayStorage (evm := evmAmt)
      (locals := localsNew) hbase
  have hargsSub :
      evalExprs? config { contract := contract, locals := localsNew } evmAmt
        [.storage sayRef, .var "oldAmt_"] =
          .ok
            [.int (Int.ofNat
              (Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩).toNat),
             .int (Int.ofNat oldAmt.toNat)] := by
    simp [evalExprs?, hsay, holdVar, EvalResult.bind, bind, pure]
  have hbindSub :
      bindParams? subFunction.params
          [.int (Int.ofNat
            (Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩).toNat),
           .int (Int.ofNat oldAmt.toNat)] =
        some
          (uintBinaryLocals
            (Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩)
            oldAmt) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := localsNew } evmAmt
        (.internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld") .reverted := by
    have hownerAmt : evmAmt.executionEnv.codeOwner = evmCall.executionEnv.codeOwner := by
      dsimp [evmAmt]
      simp only [Solm.EVM.storageStore, State.lookupAccount]
      cases evmCall.accountMap.find? evmCall.executionEnv.codeOwner <;>
        simp only [Option.option, State.setAccount]
    have hbody := execSubFunctionRevert (evm := evmAmt)
      (x := Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩)
      (y := oldAmt)
      (by simpa [evmAmt, oldAmt, evm0, hownerAmt] using hunder)
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := localsNew })
      (evm := evmAmt) (name := "_sub") (retVar := "withoutOld")
      (args := [.storage sayRef, .var "oldAmt_"])
      (argVals :=
        [.int (Int.ofNat
          (Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩).toNat),
         .int (Int.ofNat oldAmt.toNat)])
      (callee := subFunction)
      (locals :=
        uintBinaryLocals
          (Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩)
          oldAmt)
      hargsSub (by rfl) hbindSub hbody
  have hcallTail :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    have hrest :
        ExecBlock config { contract := contract, locals := localsNew } evmCall
          [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
            .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
            .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
            .assign .storage sayRef (.var "sayNew"),
            .ite
              (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
              [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
                .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
              [] ]
          .reverted := by
      refine ExecBlock.consNormal (ExecStmt.assign hnewVar hassignAmt) ?_
      exact ExecBlock.consRevert hsubStmt
    exact Reasoning.Refinement.execBlock_append hcallBlock hrest
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := oldAmtVal) ?_) ?_
    · simpa [oldAmt, oldAmtVal, evm0] using holdAmt
    simpa [localsOld, oldAmtVal] using hcallTail
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureLoadSourceBodyAddRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCall : EVM.State} {out : ByteArray} {newAmt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I ≠ ⟨0⟩)
    (hcode : extCodeSizeWord σ (loadKey I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (loadSrc I)) "cure" 0 []
        (true, evmCall, out) false)
    (hdec :
      config.externalABI.decode? "cure" out =
        some [.int (Int.ofNat newAmt.toNat)])
    (hsubOk :
      (Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (loadAmtSlotFor I)).toNat ≤
        (Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
            (loadAmtSlotFor I) newAmt)
          evmCall.executionEnv.codeOwner ⟨9⟩).toNat)
    (hover :
      UInt256.size ≤
        (UInt256.sub
          (Solm.EVM.storageLoad
            (Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
              (loadAmtSlotFor I) newAmt)
            evmCall.executionEnv.codeOwner ⟨9⟩)
          (Solm.EVM.storageLoad
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
            I.codeOwner (loadAmtSlotFor I))).toNat + newAmt.toNat) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (loadLocals I)
      loadTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_true evm0 I hposLoad
  have holdAmt := evalExpr_loadAmtStorage evm0 I
  let oldAmt :=
    Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)
  let oldAmtVal : Value := .int (Int.ofNat oldAmt.toNat)
  let localsOld : Store := (loadLocals I).insert "oldAmt_" oldAmtVal
  let localsNew : Store := localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))
  let evmAmt := Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
    (loadAmtSlotFor I) newAmt
  let sayAfter := Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩
  let withoutOld := UInt256.sub sayAfter oldAmt
  let localsWithout : Store :=
    localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))
  have hsrc : localsOld.get? "src" = some (.address (loadSrc I)) := by
    change ((loadLocals I).insert "oldAmt_" oldAmtVal).get? "src" =
      some (.address (loadSrc I))
    rw [store_get_ne (loadLocals I) (k := "oldAmt_") (a := "src") oldAmtVal
      (by native_decide)]
    simp [loadLocals]
  have hguardCall :
      evalExpr? config { contract := contract, locals := localsOld } evm0
        (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, localsOld] using
      evalExpr_loadExtCodeSizeGtZero_true_of_src
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (locals := localsOld) hsrc hcode
  have hargs :
      evalExprs? config { contract := contract, locals := localsOld } evm0 [] = .ok [] := by
    rfl
  have hcallBlock :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false))
        (.ok { contract := contract, locals := localsNew } evmCall) := by
    simpa [checkedExternalCallStmts, localsNew] using
      checkedExternalCallVarSuccess
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmCall)
        (locals := localsOld) (receiver := "src") (retVar := "newAmt_")
        (name := "cure") (target := loadSrc I) (sendVal := 0) (args := [])
        (argVals := []) (out := out) (perm := false)
        (value := [.int (Int.ofNat newAmt.toNat)])
        hguardCall hsrc hargs hcall hdec
  have hnewVar :
      evalExpr? config { contract := contract, locals := localsNew } evmCall (.var "newAmt_") =
        .ok (.int (Int.ofNat newAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmCall) (locals := localsNew)
      (name := "newAmt_") (value := newAmt)
      (by
        change (localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))).get? "newAmt_" =
          some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_self])
  have hassignAmt :
      assignStorageRef? config { contract := contract, locals := localsNew } evmCall
        .storage (amtRef (.var "src")) (.int (Int.ofNat newAmt.toNat)) =
          .ok ({ contract := contract, locals := localsNew }, evmAmt) := by
    have hbase : localsNew.get? "amt" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "amt" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    have hsrcNew : localsNew.get? "src" = some (.address (loadSrc I)) := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "src" = some (.address (loadSrc I))
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt] using assign_loadAmtStorage (evm := evmCall) (locals := localsNew)
      I newAmt hbase hsrcNew
  have holdVar :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.var "oldAmt_") =
        .ok (.int (Int.ofNat oldAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsNew)
      (name := "oldAmt_") (value := oldAmt)
      (by
        change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
          (.int (Int.ofNat newAmt.toNat))).get? "oldAmt_" =
            some (.int (Int.ofNat oldAmt.toNat))
        rw [store_get_ne _ _ (by native_decide), store_get_self])
  have hsay :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.storage sayRef) =
        .ok (.int (Int.ofNat sayAfter.toNat)) := by
    have hbase : localsNew.get? "say" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "say" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt, sayAfter] using evalExpr_loadSayStorage (evm := evmAmt)
      (locals := localsNew) hbase
  have hargsSub :
      evalExprs? config { contract := contract, locals := localsNew } evmAmt
        [.storage sayRef, .var "oldAmt_"] =
          .ok [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)] := by
    simp [evalExprs?, hsay, holdVar, EvalResult.bind, bind, pure]
  have hbindSub :
      bindParams? subFunction.params
          [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)] =
        some (uintBinaryLocals sayAfter oldAmt) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := localsNew } evmAmt
        (.internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld")
        (.ok { contract := contract, locals := localsWithout } evmAmt) := by
    have hownerAmt : evmAmt.executionEnv.codeOwner = evmCall.executionEnv.codeOwner := by
      dsimp [evmAmt]
      simp only [Solm.EVM.storageStore, State.lookupAccount]
      cases evmCall.accountMap.find? evmCall.executionEnv.codeOwner <;>
        simp only [Option.option, State.setAccount]
    have hle : oldAmt.toNat ≤ sayAfter.toNat := by
      simpa [evmAmt, oldAmt, evm0, sayAfter, hownerAmt] using hsubOk
    have hbody := execSubFunctionReturn (evm := evmAmt)
      (x := sayAfter) (y := oldAmt) (diff := withoutOld)
      (by simp [withoutOld]) hle
    simpa [localsWithout, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsNew })
        (evm := evmAmt) (calleeEvm := evmAmt) (name := "_sub") (retVar := "withoutOld")
        (args := [.storage sayRef, .var "oldAmt_"])
        (argVals := [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)])
        (callee := subFunction)
        (locals := uintBinaryLocals sayAfter oldAmt)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ sayAfter oldAmt withoutOld })
        (value := some [.int (Int.ofNat withoutOld.toNat)])
        hargsSub (by rfl) hbindSub hbody)
  have hwithoutVar :
      evalExpr? config { contract := contract, locals := localsWithout } evmAmt
        (.var "withoutOld") =
        .ok (.int (Int.ofNat withoutOld.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsWithout)
      (name := "withoutOld") (value := withoutOld)
      (by
        change (localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))).get?
            "withoutOld" = some (.int (Int.ofNat withoutOld.toNat))
        rw [store_get_self])
  have hnewVarWithout :
      evalExpr? config { contract := contract, locals := localsWithout } evmAmt
        (.var "newAmt_") =
        .ok (.int (Int.ofNat newAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsWithout)
      (name := "newAmt_") (value := newAmt)
      (by
        change (localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))).get?
            "newAmt_" = some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_ne _ _ (by native_decide)]
        change localsNew.get? "newAmt_" = some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_self])
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsWithout } evmAmt
        [.var "withoutOld", .var "newAmt_"] =
          .ok [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)] := by
    simp [evalExprs?, hwithoutVar, hnewVarWithout, EvalResult.bind, bind, pure]
  have hbindAdd :
      bindParams? addFunction.params
          [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)] =
        some (uintBinaryLocals withoutOld newAmt) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hownerAmtLocal : evmAmt.executionEnv.codeOwner = evmCall.executionEnv.codeOwner := by
    dsimp [evmAmt]
    simp only [Solm.EVM.storageStore, State.lookupAccount]
    cases evmCall.accountMap.find? evmCall.executionEnv.codeOwner <;>
      simp only [Option.option, State.setAccount]
  have howner0Local : evm0.executionEnv.codeOwner = I.codeOwner := by
    simp [evm0, initState]
  have hoverLocal : UInt256.size ≤ withoutOld.toNat + newAmt.toNat := by
    simpa [withoutOld, sayAfter, evmAmt, oldAmt, evm0, hownerAmtLocal, howner0Local] using hover
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsWithout } evmAmt
        (.internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew") .reverted := by
    have hbody := execAddFunctionRevert (evm := evmAmt)
      (x := withoutOld) (y := newAmt) hoverLocal
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := localsWithout })
      (evm := evmAmt) (name := "_add") (retVar := "sayNew")
      (args := [.var "withoutOld", .var "newAmt_"])
      (argVals := [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)])
      (callee := addFunction)
      (locals := uintBinaryLocals withoutOld newAmt)
      hargsAdd (by rfl) hbindAdd hbody
  have hcallTail :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    have hrest :
        ExecBlock config { contract := contract, locals := localsNew } evmCall
          [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
            .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
            .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
            .assign .storage sayRef (.var "sayNew"),
            .ite
              (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
              [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
                .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
              [] ]
          .reverted := by
      refine ExecBlock.consNormal (ExecStmt.assign hnewVar hassignAmt) ?_
      refine ExecBlock.consNormal hsubStmt ?_
      exact ExecBlock.consRevert haddStmt
    exact Reasoning.Refinement.execBlock_append hcallBlock hrest
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := oldAmtVal) ?_) ?_
    · simpa [oldAmt, oldAmtVal, evm0] using holdAmt
    simpa [localsOld, oldAmtVal] using hcallTail
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureLoadSourceBodyOkLoadedNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCall : EVM.State} {out : ByteArray} {newAmt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I ≠ ⟨0⟩)
    (hcode : extCodeSizeWord σ (loadKey I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (loadSrc I)) "cure" 0 []
        (true, evmCall, out) false)
    (hdec :
      config.externalABI.decode? "cure" out =
        some [.int (Int.ofNat newAmt.toNat)])
    (hsubOk :
      (Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (loadAmtSlotFor I)).toNat ≤
        (Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
            (loadAmtSlotFor I) newAmt)
          evmCall.executionEnv.codeOwner ⟨9⟩).toNat)
    (haddOk :
      (UInt256.sub
        (Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
            (loadAmtSlotFor I) newAmt)
          evmCall.executionEnv.codeOwner ⟨9⟩)
        (Solm.EVM.storageLoad
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner (loadAmtSlotFor I))).toNat + newAmt.toNat < UInt256.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let oldAmt := Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)
    let oldAmtVal : Value := .int (Int.ofNat oldAmt.toNat)
    let localsOld : Store := (loadLocals I).insert "oldAmt_" oldAmtVal
    let localsNew : Store := localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))
    let evmAmt := Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
      (loadAmtSlotFor I) newAmt
    let sayAfter := Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩
    let withoutOld := UInt256.sub sayAfter oldAmt
    let localsWithout : Store :=
      localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))
    let sayNew := withoutOld + newAmt
    let localsSay : Store := localsWithout.insert "sayNew" (.int (Int.ofNat sayNew.toNat))
    let evmSay := Solm.EVM.storageStore evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩ sayNew
    Solm.EVM.storageLoad evmSay evmSay.executionEnv.codeOwner (loadLoadedSlotFor I) ≠ ⟨0⟩ →
    ExecTransitionBody config contract evm0 (loadLocals I) loadTransition.body
      (.returned { contract := contract, locals := localsSay } evmSay none) := by
  intro evm0 oldAmt oldAmtVal localsOld localsNew evmAmt sayAfter withoutOld localsWithout
    sayNew localsSay evmSay hloaded
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_true evm0 I hposLoad
  have holdAmt := evalExpr_loadAmtStorage evm0 I
  have hsrc : localsOld.get? "src" = some (.address (loadSrc I)) := by
    change ((loadLocals I).insert "oldAmt_" oldAmtVal).get? "src" =
      some (.address (loadSrc I))
    rw [store_get_ne (loadLocals I) (k := "oldAmt_") (a := "src") oldAmtVal
      (by native_decide)]
    simp [loadLocals]
  have hguardCall :
      evalExpr? config { contract := contract, locals := localsOld } evm0
        (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, localsOld] using
      evalExpr_loadExtCodeSizeGtZero_true_of_src
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (locals := localsOld) hsrc hcode
  have hargs :
      evalExprs? config { contract := contract, locals := localsOld } evm0 [] = .ok [] := by
    rfl
  have hcallBlock :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false))
        (.ok { contract := contract, locals := localsNew } evmCall) := by
    simpa [checkedExternalCallStmts, localsNew] using
      checkedExternalCallVarSuccess
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmCall)
        (locals := localsOld) (receiver := "src") (retVar := "newAmt_")
        (name := "cure") (target := loadSrc I) (sendVal := 0) (args := [])
        (argVals := []) (out := out) (perm := false)
        (value := [.int (Int.ofNat newAmt.toNat)])
        hguardCall hsrc hargs hcall hdec
  have hnewVar :
      evalExpr? config { contract := contract, locals := localsNew } evmCall (.var "newAmt_") =
        .ok (.int (Int.ofNat newAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmCall) (locals := localsNew)
      (name := "newAmt_") (value := newAmt)
      (by
        change (localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))).get? "newAmt_" =
          some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_self])
  have hassignAmt :
      assignStorageRef? config { contract := contract, locals := localsNew } evmCall
        .storage (amtRef (.var "src")) (.int (Int.ofNat newAmt.toNat)) =
          .ok ({ contract := contract, locals := localsNew }, evmAmt) := by
    have hbase : localsNew.get? "amt" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "amt" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    have hsrcNew : localsNew.get? "src" = some (.address (loadSrc I)) := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "src" = some (.address (loadSrc I))
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt] using assign_loadAmtStorage (evm := evmCall) (locals := localsNew)
      I newAmt hbase hsrcNew
  have holdVar :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.var "oldAmt_") =
        .ok (.int (Int.ofNat oldAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsNew)
      (name := "oldAmt_") (value := oldAmt)
      (by
        change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
          (.int (Int.ofNat newAmt.toNat))).get? "oldAmt_" =
            some (.int (Int.ofNat oldAmt.toNat))
        rw [store_get_ne _ _ (by native_decide), store_get_self])
  have hsay :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.storage sayRef) =
        .ok (.int (Int.ofNat sayAfter.toNat)) := by
    have hbase : localsNew.get? "say" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "say" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt, sayAfter] using evalExpr_loadSayStorage (evm := evmAmt)
      (locals := localsNew) hbase
  have hargsSub :
      evalExprs? config { contract := contract, locals := localsNew } evmAmt
        [.storage sayRef, .var "oldAmt_"] =
          .ok [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)] := by
    simp [evalExprs?, hsay, holdVar, EvalResult.bind, bind, pure]
  have hbindSub :
      bindParams? subFunction.params
          [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)] =
        some (uintBinaryLocals sayAfter oldAmt) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := localsNew } evmAmt
        (.internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld")
        (.ok { contract := contract, locals := localsWithout } evmAmt) := by
    have hownerAmt : evmAmt.executionEnv.codeOwner = evmCall.executionEnv.codeOwner := by
      dsimp [evmAmt]
      simp only [Solm.EVM.storageStore, State.lookupAccount]
      cases evmCall.accountMap.find? evmCall.executionEnv.codeOwner <;>
        simp only [Option.option, State.setAccount]
    have hle : oldAmt.toNat ≤ sayAfter.toNat := by
      simpa [evmAmt, oldAmt, evm0, sayAfter, hownerAmt] using hsubOk
    have hbody := execSubFunctionReturn (evm := evmAmt)
      (x := sayAfter) (y := oldAmt) (diff := withoutOld)
      (by simp [withoutOld]) hle
    simpa [localsWithout, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsNew })
        (evm := evmAmt) (calleeEvm := evmAmt) (name := "_sub") (retVar := "withoutOld")
        (args := [.storage sayRef, .var "oldAmt_"])
        (argVals := [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)])
        (callee := subFunction)
        (locals := uintBinaryLocals sayAfter oldAmt)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ sayAfter oldAmt withoutOld })
        (value := some [.int (Int.ofNat withoutOld.toNat)])
        hargsSub (by rfl) hbindSub hbody)
  have hwithoutVar :
      evalExpr? config { contract := contract, locals := localsWithout } evmAmt
        (.var "withoutOld") =
        .ok (.int (Int.ofNat withoutOld.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsWithout)
      (name := "withoutOld") (value := withoutOld)
      (by
        change (localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))).get?
            "withoutOld" = some (.int (Int.ofNat withoutOld.toNat))
        rw [store_get_self])
  have hnewVarWithout :
      evalExpr? config { contract := contract, locals := localsWithout } evmAmt
        (.var "newAmt_") =
        .ok (.int (Int.ofNat newAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsWithout)
      (name := "newAmt_") (value := newAmt)
      (by
        change (localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))).get?
            "newAmt_" = some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_self])
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsWithout } evmAmt
        [.var "withoutOld", .var "newAmt_"] =
          .ok [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)] := by
    simp [evalExprs?, hwithoutVar, hnewVarWithout, EvalResult.bind, bind, pure]
  have hbindAdd :
      bindParams? addFunction.params
          [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)] =
        some (uintBinaryLocals withoutOld newAmt) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hownerAmtLocal : evmAmt.executionEnv.codeOwner = evmCall.executionEnv.codeOwner := by
    dsimp [evmAmt]
    simp only [Solm.EVM.storageStore, State.lookupAccount]
    cases evmCall.accountMap.find? evmCall.executionEnv.codeOwner <;>
      simp only [Option.option, State.setAccount]
  have howner0Local : evm0.executionEnv.codeOwner = I.codeOwner := by
    simp [evm0, initState]
  have haddOkLocal : withoutOld.toNat + newAmt.toNat < UInt256.size := by
    simpa [withoutOld, sayAfter, evmAmt, oldAmt, evm0, hownerAmtLocal, howner0Local] using haddOk
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsWithout } evmAmt
        (.internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew")
        (.ok { contract := contract, locals := localsSay } evmAmt) := by
    have hbody := execAddFunctionReturn (evm := evmAmt)
      (x := withoutOld) (y := newAmt) (sum := sayNew) (by simp [sayNew]) haddOkLocal
    simpa [localsSay, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsWithout })
        (evm := evmAmt) (calleeEvm := evmAmt) (name := "_add") (retVar := "sayNew")
        (args := [.var "withoutOld", .var "newAmt_"])
        (argVals := [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)])
        (callee := addFunction)
        (locals := uintBinaryLocals withoutOld newAmt)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ withoutOld newAmt sayNew })
        (value := some [.int (Int.ofNat sayNew.toNat)])
        hargsAdd (by rfl) hbindAdd hbody)
  have hsayNewVar :
      evalExpr? config { contract := contract, locals := localsSay } evmAmt (.var "sayNew") =
        .ok (.int (Int.ofNat sayNew.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsSay)
      (name := "sayNew") (value := sayNew)
      (by
        change (localsWithout.insert "sayNew" (.int (Int.ofNat sayNew.toNat))).get?
            "sayNew" = some (.int (Int.ofNat sayNew.toNat))
        rw [store_get_self])
  have hassignSay :
      assignStorageRef? config { contract := contract, locals := localsSay } evmAmt
        .storage sayRef (.int (Int.ofNat sayNew.toNat)) =
          .ok ({ contract := contract, locals := localsSay }, evmSay) := by
    have hbase : localsSay.get? "say" = none := by
      change (((((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).insert "withoutOld"
          (.int (Int.ofNat withoutOld.toNat))).insert "sayNew"
          (.int (Int.ofNat sayNew.toNat))).get? "say" = none
      rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmSay] using assign_loadSayStorage (evm := evmAmt) (locals := localsSay)
      sayNew hbase
  have hcond :
      evalExpr? config { contract := contract, locals := localsSay } evmSay
        (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0)) =
          .ok (.bool false) := by
    have hbase : localsSay.get? "loaded" = none := by
      change (((((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).insert "withoutOld"
          (.int (Int.ofNat withoutOld.toNat))).insert "sayNew"
          (.int (Int.ofNat sayNew.toNat))).get? "loaded" = none
      rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    have hsrcSay : localsSay.get? "src" = some (.address (loadSrc I)) := by
      change (((((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).insert "withoutOld"
          (.int (Int.ofNat withoutOld.toNat))).insert "sayNew"
          (.int (Int.ofNat sayNew.toNat))).get? "src" = some (.address (loadSrc I))
      rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    exact evalExpr_loadLoadedEqZero_false (evm := evmSay) (locals := localsSay) I
      hbase hsrcSay hloaded
  have hcallTail :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        (.ok { contract := contract, locals := localsSay } evmSay) := by
    have hrest :
        ExecBlock config { contract := contract, locals := localsNew } evmCall
          [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
            .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
            .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
            .assign .storage sayRef (.var "sayNew"),
            .ite
              (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
              [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
                .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
              [] ]
          (.ok { contract := contract, locals := localsSay } evmSay) := by
      refine ExecBlock.consNormal (ExecStmt.assign hnewVar hassignAmt) ?_
      refine ExecBlock.consNormal hsubStmt ?_
      refine ExecBlock.consNormal haddStmt ?_
      refine ExecBlock.consNormal (ExecStmt.assign hsayNewVar hassignSay) ?_
      exact ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ExecBlock.nil
    exact Reasoning.Refinement.execBlock_append hcallBlock hrest
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        (.ok { contract := contract, locals := localsSay } evmSay) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := oldAmtVal) ?_) ?_
    · simpa [oldAmt, oldAmtVal, evm0] using holdAmt
    simpa [localsOld, oldAmtVal] using hcallTail
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockOK hblock

theorem cureLoadSourceBodyOkLoadedZero {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCall : EVM.State} {out : ByteArray} {newAmt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨0⟩)
    (hpos : cureSlotWord (loadPosSlotFor I) σ I ≠ ⟨0⟩)
    (hcode : extCodeSizeWord σ (loadKey I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (loadSrc I)) "cure" 0 []
        (true, evmCall, out) false)
    (hdec :
      config.externalABI.decode? "cure" out =
        some [.int (Int.ofNat newAmt.toNat)])
    (hsubOk :
      (Solm.EVM.storageLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner (loadAmtSlotFor I)).toNat ≤
        (Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
            (loadAmtSlotFor I) newAmt)
          evmCall.executionEnv.codeOwner ⟨9⟩).toNat)
    (haddOk :
      (UInt256.sub
        (Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
            (loadAmtSlotFor I) newAmt)
          evmCall.executionEnv.codeOwner ⟨9⟩)
        (Solm.EVM.storageLoad
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner (loadAmtSlotFor I))).toNat + newAmt.toNat < UInt256.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let oldAmt := Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadAmtSlotFor I)
    let oldAmtVal : Value := .int (Int.ofNat oldAmt.toNat)
    let localsOld : Store := (loadLocals I).insert "oldAmt_" oldAmtVal
    let localsNew : Store := localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))
    let evmAmt := Solm.EVM.storageStore evmCall evmCall.executionEnv.codeOwner
      (loadAmtSlotFor I) newAmt
    let sayAfter := Solm.EVM.storageLoad evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩
    let withoutOld := UInt256.sub sayAfter oldAmt
    let localsWithout : Store :=
      localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))
    let sayNew := withoutOld + newAmt
    let localsSay : Store := localsWithout.insert "sayNew" (.int (Int.ofNat sayNew.toNat))
    let evmSay := Solm.EVM.storageStore evmAmt evmAmt.executionEnv.codeOwner ⟨9⟩ sayNew
    let evmLoaded := Solm.EVM.storageStore evmSay evmSay.executionEnv.codeOwner
      (loadLoadedSlotFor I) ⟨1⟩
    let count := Solm.EVM.storageLoad evmLoaded evmLoaded.executionEnv.codeOwner ⟨8⟩
    let evmCount := Solm.EVM.storageStore evmLoaded evmLoaded.executionEnv.codeOwner
      ⟨8⟩ (count + ⟨1⟩)
    Solm.EVM.storageLoad evmSay evmSay.executionEnv.codeOwner (loadLoadedSlotFor I) = ⟨0⟩ →
    ExecTransitionBody config contract evm0 (loadLocals I) loadTransition.body
      (.returned { contract := contract, locals := localsSay } evmCount none) := by
  intro evm0 oldAmt oldAmtVal localsOld localsNew evmAmt sayAfter withoutOld localsWithout
    sayNew localsSay evmSay evmLoaded count evmCount hloaded
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨1⟩ = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (loadPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardLive := evalExpr_loadLiveEqZero_true evm0 I hliveLoad
  have hguardPos := evalExpr_loadPosGtZero_true evm0 I hposLoad
  have holdAmt := evalExpr_loadAmtStorage evm0 I
  have hsrc : localsOld.get? "src" = some (.address (loadSrc I)) := by
    change ((loadLocals I).insert "oldAmt_" oldAmtVal).get? "src" =
      some (.address (loadSrc I))
    rw [store_get_ne (loadLocals I) (k := "oldAmt_") (a := "src") oldAmtVal
      (by native_decide)]
    simp [loadLocals]
  have hguardCall :
      evalExpr? config { contract := contract, locals := localsOld } evm0
        (.binary .gt (.extCodeSize (.var "src")) (.intLit 0)) = .ok (.bool true) := by
    simpa [evm0, localsOld] using
      evalExpr_loadExtCodeSizeGtZero_true_of_src
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) (locals := localsOld) hsrc hcode
  have hargs :
      evalExprs? config { contract := contract, locals := localsOld } evm0 [] = .ok [] := by
    rfl
  have hcallBlock :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false))
        (.ok { contract := contract, locals := localsNew } evmCall) := by
    simpa [checkedExternalCallStmts, localsNew] using
      checkedExternalCallVarSuccess
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmCall)
        (locals := localsOld) (receiver := "src") (retVar := "newAmt_")
        (name := "cure") (target := loadSrc I) (sendVal := 0) (args := [])
        (argVals := []) (out := out) (perm := false)
        (value := [.int (Int.ofNat newAmt.toNat)])
        hguardCall hsrc hargs hcall hdec
  have hnewVar :
      evalExpr? config { contract := contract, locals := localsNew } evmCall (.var "newAmt_") =
        .ok (.int (Int.ofNat newAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmCall) (locals := localsNew)
      (name := "newAmt_") (value := newAmt)
      (by
        change (localsOld.insert "newAmt_" (.int (Int.ofNat newAmt.toNat))).get? "newAmt_" =
          some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_self])
  have hassignAmt :
      assignStorageRef? config { contract := contract, locals := localsNew } evmCall
        .storage (amtRef (.var "src")) (.int (Int.ofNat newAmt.toNat)) =
          .ok ({ contract := contract, locals := localsNew }, evmAmt) := by
    have hbase : localsNew.get? "amt" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "amt" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    have hsrcNew : localsNew.get? "src" = some (.address (loadSrc I)) := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "src" = some (.address (loadSrc I))
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt] using assign_loadAmtStorage (evm := evmCall) (locals := localsNew)
      I newAmt hbase hsrcNew
  have holdVar :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.var "oldAmt_") =
        .ok (.int (Int.ofNat oldAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsNew)
      (name := "oldAmt_") (value := oldAmt)
      (by
        change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
          (.int (Int.ofNat newAmt.toNat))).get? "oldAmt_" =
            some (.int (Int.ofNat oldAmt.toNat))
        rw [store_get_ne _ _ (by native_decide), store_get_self])
  have hsay :
      evalExpr? config { contract := contract, locals := localsNew } evmAmt (.storage sayRef) =
        .ok (.int (Int.ofNat sayAfter.toNat)) := by
    have hbase : localsNew.get? "say" = none := by
      change (((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).get? "say" = none
      rw [store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmAmt, sayAfter] using evalExpr_loadSayStorage (evm := evmAmt)
      (locals := localsNew) hbase
  have hargsSub :
      evalExprs? config { contract := contract, locals := localsNew } evmAmt
        [.storage sayRef, .var "oldAmt_"] =
          .ok [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)] := by
    simp [evalExprs?, hsay, holdVar, EvalResult.bind, bind, pure]
  have hbindSub :
      bindParams? subFunction.params
          [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)] =
        some (uintBinaryLocals sayAfter oldAmt) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := localsNew } evmAmt
        (.internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld")
        (.ok { contract := contract, locals := localsWithout } evmAmt) := by
    have hownerAmt : evmAmt.executionEnv.codeOwner = evmCall.executionEnv.codeOwner := by
      dsimp [evmAmt]
      simp only [Solm.EVM.storageStore, State.lookupAccount]
      cases evmCall.accountMap.find? evmCall.executionEnv.codeOwner <;>
        simp only [Option.option, State.setAccount]
    have hle : oldAmt.toNat ≤ sayAfter.toNat := by
      simpa [evmAmt, oldAmt, evm0, sayAfter, hownerAmt] using hsubOk
    have hbody := execSubFunctionReturn (evm := evmAmt)
      (x := sayAfter) (y := oldAmt) (diff := withoutOld)
      (by simp [withoutOld]) hle
    simpa [localsWithout, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsNew })
        (evm := evmAmt) (calleeEvm := evmAmt) (name := "_sub") (retVar := "withoutOld")
        (args := [.storage sayRef, .var "oldAmt_"])
        (argVals := [.int (Int.ofNat sayAfter.toNat), .int (Int.ofNat oldAmt.toNat)])
        (callee := subFunction)
        (locals := uintBinaryLocals sayAfter oldAmt)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ sayAfter oldAmt withoutOld })
        (value := some [.int (Int.ofNat withoutOld.toNat)])
        hargsSub (by rfl) hbindSub hbody)
  have hwithoutVar :
      evalExpr? config { contract := contract, locals := localsWithout } evmAmt
        (.var "withoutOld") =
        .ok (.int (Int.ofNat withoutOld.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsWithout)
      (name := "withoutOld") (value := withoutOld)
      (by
        change (localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))).get?
            "withoutOld" = some (.int (Int.ofNat withoutOld.toNat))
        rw [store_get_self])
  have hnewVarWithout :
      evalExpr? config { contract := contract, locals := localsWithout } evmAmt
        (.var "newAmt_") =
        .ok (.int (Int.ofNat newAmt.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsWithout)
      (name := "newAmt_") (value := newAmt)
      (by
        change (localsNew.insert "withoutOld" (.int (Int.ofNat withoutOld.toNat))).get?
            "newAmt_" = some (.int (Int.ofNat newAmt.toNat))
        rw [store_get_ne _ _ (by native_decide)]
        rw [store_get_self])
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsWithout } evmAmt
        [.var "withoutOld", .var "newAmt_"] =
          .ok [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)] := by
    simp [evalExprs?, hwithoutVar, hnewVarWithout, EvalResult.bind, bind, pure]
  have hbindAdd :
      bindParams? addFunction.params
          [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)] =
        some (uintBinaryLocals withoutOld newAmt) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hownerAmtLocal : evmAmt.executionEnv.codeOwner = evmCall.executionEnv.codeOwner := by
    dsimp [evmAmt]
    simp only [Solm.EVM.storageStore, State.lookupAccount]
    cases evmCall.accountMap.find? evmCall.executionEnv.codeOwner <;>
      simp only [Option.option, State.setAccount]
  have howner0Local : evm0.executionEnv.codeOwner = I.codeOwner := by
    simp [evm0, initState]
  have haddOkLocal : withoutOld.toNat + newAmt.toNat < UInt256.size := by
    simpa [withoutOld, sayAfter, evmAmt, oldAmt, evm0, hownerAmtLocal, howner0Local] using haddOk
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsWithout } evmAmt
        (.internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew")
        (.ok { contract := contract, locals := localsSay } evmAmt) := by
    have hbody := execAddFunctionReturn (evm := evmAmt)
      (x := withoutOld) (y := newAmt) (sum := sayNew) (by simp [sayNew]) haddOkLocal
    simpa [localsSay, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsWithout })
        (evm := evmAmt) (calleeEvm := evmAmt) (name := "_add") (retVar := "sayNew")
        (args := [.var "withoutOld", .var "newAmt_"])
        (argVals := [.int (Int.ofNat withoutOld.toNat), .int (Int.ofNat newAmt.toNat)])
        (callee := addFunction)
        (locals := uintBinaryLocals withoutOld newAmt)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ withoutOld newAmt sayNew })
        (value := some [.int (Int.ofNat sayNew.toNat)])
        hargsAdd (by rfl) hbindAdd hbody)
  have hsayNewVar :
      evalExpr? config { contract := contract, locals := localsSay } evmAmt (.var "sayNew") =
        .ok (.int (Int.ofNat sayNew.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmAmt) (locals := localsSay)
      (name := "sayNew") (value := sayNew)
      (by
        change (localsWithout.insert "sayNew" (.int (Int.ofNat sayNew.toNat))).get?
            "sayNew" = some (.int (Int.ofNat sayNew.toNat))
        rw [store_get_self])
  have hassignSay :
      assignStorageRef? config { contract := contract, locals := localsSay } evmAmt
        .storage sayRef (.int (Int.ofNat sayNew.toNat)) =
          .ok ({ contract := contract, locals := localsSay }, evmSay) := by
    have hbase : localsSay.get? "say" = none := by
      change (((((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).insert "withoutOld"
          (.int (Int.ofNat withoutOld.toNat))).insert "sayNew"
          (.int (Int.ofNat sayNew.toNat))).get? "say" = none
      rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmSay] using assign_loadSayStorage (evm := evmAmt) (locals := localsSay)
      sayNew hbase
  have htail :
      ExecStmt config { contract := contract, locals := localsSay } evmSay
        (.ite
          (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
          [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
            .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
          [])
        (.ok { contract := contract, locals := localsSay } evmCount) := by
    have hbaseLoaded : localsSay.get? "loaded" = none := by
      change (((((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).insert "withoutOld"
          (.int (Int.ofNat withoutOld.toNat))).insert "sayNew"
          (.int (Int.ofNat sayNew.toNat))).get? "loaded" = none
      rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    have hbaseLCount : localsSay.get? "lCount" = none := by
      change (((((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).insert "withoutOld"
          (.int (Int.ofNat withoutOld.toNat))).insert "sayNew"
          (.int (Int.ofNat sayNew.toNat))).get? "lCount" = none
      rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    have hsrcSay : localsSay.get? "src" = some (.address (loadSrc I)) := by
      change (((((loadLocals I).insert "oldAmt_" oldAmtVal).insert "newAmt_"
        (.int (Int.ofNat newAmt.toNat))).insert "withoutOld"
          (.int (Int.ofNat withoutOld.toNat))).insert "sayNew"
          (.int (Int.ofNat sayNew.toNat))).get? "src" = some (.address (loadSrc I))
      rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
      simp [loadLocals]
    simpa [evmLoaded, count, evmCount] using
      execLoadLoadedZeroTail (evm := evmSay) (locals := localsSay) I
        hbaseLoaded hbaseLCount hsrcSay hloaded
  have hcallTail :
      ExecBlock config { contract := contract, locals := localsOld } evm0
        (checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_"
          (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        (.ok { contract := contract, locals := localsSay } evmCount) := by
    have hrest :
        ExecBlock config { contract := contract, locals := localsNew } evmCall
          [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
            .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
            .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
            .assign .storage sayRef (.var "sayNew"),
            .ite
              (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
              [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
                .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
              [] ]
          (.ok { contract := contract, locals := localsSay } evmCount) := by
      refine ExecBlock.consNormal (ExecStmt.assign hnewVar hassignAmt) ?_
      refine ExecBlock.consNormal hsubStmt ?_
      refine ExecBlock.consNormal haddStmt ?_
      refine ExecBlock.consNormal (ExecStmt.assign hsayNewVar hassignSay) ?_
      exact ExecBlock.consNormal htail ExecBlock.nil
    exact Reasoning.Refinement.execBlock_append hcallBlock hrest
  have hblock :
      ExecBlock config { contract := contract, locals := loadLocals I } evm0
        (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
        .require (.binary .gt (.storage (posRef (.var "src"))) (.intLit 0)) ::
        .letDecl "oldAmt_" (some uint256) (.storage (amtRef (.var "src"))) ::
        checkedExternalCallStmts (.var "src") "cure" (.intLit 0) [] "newAmt_" (perm := false) ++
        [ .assign .storage (amtRef (.var "src")) (.var "newAmt_"),
          .internalCall "_sub" [.storage sayRef, .var "oldAmt_"] "withoutOld",
          .internalCall "_add" [.var "withoutOld", .var "newAmt_"] "sayNew",
          .assign .storage sayRef (.var "sayNew"),
          .ite
            (.binary .eq (.storage (loadedRef (.var "src"))) (.intLit 0))
            [ .assign .storage (loadedRef (.var "src")) (.intLit 1),
              .assign .storage lCountRef (incUnchecked (.storage lCountRef)) ]
            [] ])
        (.ok { contract := contract, locals := localsSay } evmCount) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := oldAmtVal) ?_) ?_
    · simpa [oldAmt, oldAmtVal, evm0] using holdAmt
    simpa [localsOld, oldAmtVal] using hcallTail
  simpa [ExecTransitionBody, loadTransition, nonpayable, evm0] using
    ExecFuncBody.execBlockOK hblock



end Benchmarks.Dss.Cure
