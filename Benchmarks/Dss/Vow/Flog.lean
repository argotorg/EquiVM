import Benchmarks.Dss.Vow.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `flog(uint256)` -/

abbrev flogEra (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev flogEraSlot (I : ExecutionEnv) : UInt256 :=
  sinSlot (.int (Int.ofNat (flogEra I).toNat))

theorem flogEraSlot_eq (I : ExecutionEnv) :
    flogEraSlot I = solcMappingSlot ⟨4⟩ (flogEra I) := by
  unfold flogEraSlot flogEra sinSlot mapSlot solcMappingSlot keyValueToWord
  simp only
  rw [wordOfInt_ofNat_toNat]

abbrev flogLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "era" (.int (Int.ofNat (flogEra I).toNat))

abbrev flogLocalsDoneAt (I : ExecutionEnv) (doneAt : UInt256) : Store :=
  (flogLocals I).insert "doneAt" (.int (Int.ofNat doneAt.toNat))

abbrev flogLocalsDoneAtSinNew (I : ExecutionEnv) (doneAt SinNew : UInt256) : Store :=
  (flogLocalsDoneAt I doneAt).insert "SinNew" (.int (Int.ofNat SinNew.toNat))

theorem flogLocals_get_era (I : ExecutionEnv) :
    (flogLocals I).get? "era" = some (.int (Int.ofNat (flogEra I).toNat)) := by
  rw [flogLocals, store_get_self]

theorem flogLocalsDoneAt_get_era (I : ExecutionEnv) (doneAt : UInt256) :
    (flogLocalsDoneAt I doneAt).get? "era" =
      some (.int (Int.ofNat (flogEra I).toNat)) := by
  rw [flogLocalsDoneAt, store_get_ne _ _ (by decide), flogLocals_get_era]

theorem flogLocalsDoneAt_get_doneAt (I : ExecutionEnv) (doneAt : UInt256) :
    (flogLocalsDoneAt I doneAt).get? "doneAt" =
      some (.int (Int.ofNat doneAt.toNat)) := by
  rw [flogLocalsDoneAt, store_get_self]

theorem flogLocalsDoneAtSinNew_get_era
    (I : ExecutionEnv) (doneAt SinNew : UInt256) :
    (flogLocalsDoneAtSinNew I doneAt SinNew).get? "era" =
      some (.int (Int.ofNat (flogEra I).toNat)) := by
  rw [flogLocalsDoneAtSinNew, store_get_ne _ _ (by decide),
    flogLocalsDoneAt_get_era]

theorem flogLocalsDoneAtSinNew_get_doneAt
    (I : ExecutionEnv) (doneAt SinNew : UInt256) :
    (flogLocalsDoneAtSinNew I doneAt SinNew).get? "doneAt" =
      some (.int (Int.ofNat doneAt.toNat)) := by
  rw [flogLocalsDoneAtSinNew, store_get_ne _ _ (by decide),
    flogLocalsDoneAt_get_doneAt]

theorem flogLocalsDoneAtSinNew_get_SinNew
    (I : ExecutionEnv) (doneAt SinNew : UInt256) :
    (flogLocalsDoneAtSinNew I doneAt SinNew).get? "SinNew" =
      some (.int (Int.ofNat SinNew.toNat)) := by
  rw [flogLocalsDoneAtSinNew, store_get_self]

abbrev flogWaitEvaledRef : EvaledStorageRef :=
  { base := "wait", steps := [] }

abbrev flogSinCapitalEvaledRef : EvaledStorageRef :=
  { base := "Sin", steps := [] }

abbrev flogSinEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sin", steps := [.mindex (.int (Int.ofNat (flogEra I).toNat))] }

theorem evalExpr_flogWaitStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wait" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage waitRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := flogWaitEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨7⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨7⟩)
  · exact hbase
  · simp [flogWaitEvaledRef, waitRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, flogWaitEvaledRef]

theorem evalExpr_flogSinCapitalStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "Sin" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage SinRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := flogSinCapitalEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨5⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨5⟩)
  · exact hbase
  · simp [flogSinCapitalEvaledRef, SinRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      flogSinCapitalEvaledRef]

theorem evalExpr_flogSinStorageOfLoad (evm : EVM.State) {I : ExecutionEnv}
    {locals : Store}
    (hbase : locals.get? "sin" = none)
    (hera : locals.get? "era" = some (.int (Int.ofNat (flogEra I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (sinRef (.var "era"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (flogEraSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (er := flogSinEvaledRef I) (t := .int uint256Int)
    (loc := wordLoc (flogEraSlot I))]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ (flogEraSlot I))
  · exact hbase
  · simp [flogSinEvaledRef, sinRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
    rw [← Std.HashMap.get?_eq_getElem?, hera]
    rfl
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, flogSinEvaledRef,
      flogEraSlot]

theorem flogInternalAddReturn (I : ExecutionEnv) (evm : EVM.State)
    {wait doneAt : UInt256}
    (hwaitLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = wait)
    (hdoneAt : doneAt = flogEra I + wait)
    (hfit : (flogEra I).toNat + wait.toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := flogLocals I } evm
      (.internalCall "add" [.var "era", .storage waitRef] "doneAt")
      (.ok { contract := contract, locals := flogLocalsDoneAt I doneAt } evm) := by
  have hargs :
      evalExprs? config { contract := contract, locals := flogLocals I } evm
        [.var "era", .storage waitRef] =
          .ok [.int (Int.ofNat (flogEra I).toNat), .int (Int.ofNat wait.toNat)] := by
    have hera :
        evalExpr? config { contract := contract, locals := flogLocals I } evm (.var "era") =
          .ok (.int (Int.ofNat (flogEra I).toNat)) := by
      exact evalExpr_varUInt256 (flogLocals_get_era I)
    have hwait :
        evalExpr? config { contract := contract, locals := flogLocals I } evm (.storage waitRef) =
          .ok (.int (Int.ofNat wait.toNat)) := by
      simpa [hwaitLoad] using
        (evalExpr_flogWaitStorage evm (locals := flogLocals I) (by simp [flogLocals]))
    simp [evalExprs?, hera, hwait, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (flogEra I).toNat), .int (Int.ofNat wait.toNat)] =
        some (uintBinaryLocals (flogEra I) wait) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hbody := execAddFunctionReturn (evm := evm) (x := flogEra I) (y := wait)
    (sum := doneAt) hdoneAt hfit
  simpa [flogLocalsDoneAt, resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := flogLocals I })
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "doneAt")
      (args := [.var "era", .storage waitRef])
      (argVals := [.int (Int.ofNat (flogEra I).toNat), .int (Int.ofNat wait.toNat)])
      (callee := addFunction) (locals := uintBinaryLocals (flogEra I) wait)
      (calleeSolm :=
        { contract := contract, locals := uintBinaryLocalsZ (flogEra I) wait doneAt })
      (value := some [.int (Int.ofNat doneAt.toNat)]) hargs (by rfl) hbind hbody)

theorem flogInternalAddRevert (I : ExecutionEnv) (evm : EVM.State)
    {wait : UInt256}
    (hwaitLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ = wait)
    (hover : UInt256.size ≤ (flogEra I).toNat + wait.toNat) :
    ExecStmt config { contract := contract, locals := flogLocals I } evm
      (.internalCall "add" [.var "era", .storage waitRef] "doneAt") .reverted := by
  have hargs :
      evalExprs? config { contract := contract, locals := flogLocals I } evm
        [.var "era", .storage waitRef] =
          .ok [.int (Int.ofNat (flogEra I).toNat), .int (Int.ofNat wait.toNat)] := by
    have hera :
        evalExpr? config { contract := contract, locals := flogLocals I } evm (.var "era") =
          .ok (.int (Int.ofNat (flogEra I).toNat)) := by
      exact evalExpr_varUInt256 (flogLocals_get_era I)
    have hwait :
        evalExpr? config { contract := contract, locals := flogLocals I } evm (.storage waitRef) =
          .ok (.int (Int.ofNat wait.toNat)) := by
      simpa [hwaitLoad] using
        (evalExpr_flogWaitStorage evm (locals := flogLocals I) (by simp [flogLocals]))
    simp [evalExprs?, hera, hwait, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (flogEra I).toNat), .int (Int.ofNat wait.toNat)] =
        some (uintBinaryLocals (flogEra I) wait) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hbody := execAddFunctionRevert (evm := evm) (x := flogEra I) (y := wait) hover
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := flogLocals I })
    (evm := evm) (name := "add") (retVar := "doneAt")
    (args := [.var "era", .storage waitRef])
    (argVals := [.int (Int.ofNat (flogEra I).toNat), .int (Int.ofNat wait.toNat)])
    (callee := addFunction) (locals := uintBinaryLocals (flogEra I) wait)
    hargs (by rfl) hbind hbody

theorem flogInternalSubReturn (I : ExecutionEnv) (evm : EVM.State)
    {doneAt SinVal sinVal SinNew : UInt256}
    (hSinLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hsinLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (flogEraSlot I) = sinVal)
    (hdiff : SinNew = UInt256.sub SinVal sinVal)
    (hle : sinVal.toNat ≤ SinVal.toNat) :
    ExecStmt config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
      (.internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew")
      (.ok { contract := contract, locals := flogLocalsDoneAtSinNew I doneAt SinNew } evm) := by
  have hargs :
      evalExprs? config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
        [.storage SinRef, .storage (sinRef (.var "era"))] =
          .ok [.int (Int.ofNat SinVal.toNat), .int (Int.ofNat sinVal.toNat)] := by
    have hSin :
        evalExpr? config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
          (.storage SinRef) = .ok (.int (Int.ofNat SinVal.toNat)) := by
      simpa [hSinLoad] using
        (evalExpr_flogSinCapitalStorage evm (locals := flogLocalsDoneAt I doneAt)
          (by simp [flogLocalsDoneAt, flogLocals]))
    have hsin :
        evalExpr? config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
          (.storage (sinRef (.var "era"))) = .ok (.int (Int.ofNat sinVal.toNat)) := by
      simpa [hsinLoad] using
        (evalExpr_flogSinStorageOfLoad evm (I := I) (locals := flogLocalsDoneAt I doneAt)
          (by simp [flogLocalsDoneAt, flogLocals])
          (by simpa using flogLocalsDoneAt_get_era I doneAt))
    simp [evalExprs?, hSin, hsin, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params [.int (Int.ofNat SinVal.toNat),
          .int (Int.ofNat sinVal.toNat)] =
        some (uintBinaryLocals SinVal sinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hbody := execSubFunctionReturn (evm := evm) (x := SinVal) (y := sinVal)
    (diff := SinNew) hdiff hle
  simpa [flogLocalsDoneAtSinNew, resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := flogLocalsDoneAt I doneAt })
      (evm := evm) (calleeEvm := evm) (name := "sub") (retVar := "SinNew")
      (args := [.storage SinRef, .storage (sinRef (.var "era"))])
      (argVals := [.int (Int.ofNat SinVal.toNat), .int (Int.ofNat sinVal.toNat)])
      (callee := subFunction) (locals := uintBinaryLocals SinVal sinVal)
      (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ SinVal sinVal SinNew })
      (value := some [.int (Int.ofNat SinNew.toNat)]) hargs (by rfl) hbind hbody)

theorem flogInternalSubRevert (I : ExecutionEnv) (evm : EVM.State)
    {doneAt SinVal sinVal : UInt256}
    (hSinLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hsinLoad : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (flogEraSlot I) = sinVal)
    (hlt : SinVal.toNat < sinVal.toNat) :
    ExecStmt config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
      (.internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew")
      .reverted := by
  have hargs :
      evalExprs? config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
        [.storage SinRef, .storage (sinRef (.var "era"))] =
          .ok [.int (Int.ofNat SinVal.toNat), .int (Int.ofNat sinVal.toNat)] := by
    have hSin :
        evalExpr? config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
          (.storage SinRef) = .ok (.int (Int.ofNat SinVal.toNat)) := by
      simpa [hSinLoad] using
        (evalExpr_flogSinCapitalStorage evm (locals := flogLocalsDoneAt I doneAt)
          (by simp [flogLocalsDoneAt, flogLocals]))
    have hsin :
        evalExpr? config { contract := contract, locals := flogLocalsDoneAt I doneAt } evm
          (.storage (sinRef (.var "era"))) = .ok (.int (Int.ofNat sinVal.toNat)) := by
      simpa [hsinLoad] using
        (evalExpr_flogSinStorageOfLoad evm (I := I) (locals := flogLocalsDoneAt I doneAt)
          (by simp [flogLocalsDoneAt, flogLocals])
          (by simpa using flogLocalsDoneAt_get_era I doneAt))
    simp [evalExprs?, hSin, hsin, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params [.int (Int.ofNat SinVal.toNat),
          .int (Int.ofNat sinVal.toNat)] =
        some (uintBinaryLocals SinVal sinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hbody := execSubFunctionRevert (evm := evm) (x := SinVal) (y := sinVal) hlt
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := flogLocalsDoneAt I doneAt })
    (evm := evm) (name := "sub") (retVar := "SinNew")
    (args := [.storage SinRef, .storage (sinRef (.var "era"))])
    (argVals := [.int (Int.ofNat SinVal.toNat), .int (Int.ofNat sinVal.toNat)])
    (callee := subFunction) (locals := uintBinaryLocals SinVal sinVal)
    hargs (by rfl) hbind hbody

theorem evalExpr_flogSinStorage
    {cA gh bl σ σ₀ A I} {g : UInt256} {locals : Store}
    (hbase : locals.get? "sin" = none)
    (hera : locals.get? "era" = some (.int (Int.ofNat (flogEra I).toNat))) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage (sinRef (.var "era"))) =
        .ok (.int (Int.ofNat (vowSlotWord (flogEraSlot I) σ I).toNat)) := by
  simpa [vowSlotWord, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, initState] using
      (evalExpr_flogSinStorageOfLoad
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (I := I)
        (locals := locals) hbase hera)

theorem assign_flogSinCapitalStorage (evm : EVM.State) {locals : Store} (SinNew : UInt256)
    (hbase : locals.get? "Sin" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ SinNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage SinRef (.int (Int.ofNat SinNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm SinRef =
        .ok flogSinCapitalEvaledRef := by
    simp [flogSinCapitalEvaledRef, SinRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨5⟩) (.int (Int.ofNat SinNew.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨5⟩ SinNew
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        flogSinCapitalEvaledRef])
    (hstore := hstore)

theorem assign_flogSinStorage (evm : EVM.State) {I : ExecutionEnv} {locals : Store}
    (value : UInt256)
    (hbase : locals.get? "sin" = none)
    (hera : locals.get? "era" = some (.int (Int.ofNat (flogEra I).toNat))) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (flogEraSlot I) value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (sinRef (.var "era")) (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (sinRef (.var "era")) = .ok (flogSinEvaledRef I) := by
    simp [flogSinEvaledRef, sinRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
    rw [← Std.HashMap.get?_eq_getElem?, hera]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (flogEraSlot I)) (.int (Int.ofNat value.toNat)) =
        some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm (flogEraSlot I) value
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (flogEraSlot I))
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, flogSinEvaledRef,
        flogEraSlot])
    (hstore := hstore)

theorem vowFlogSourceSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hfitWait : (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ_evm I).toNat < UInt256.size)
    (hready : (flogEra I + vowSlotWord ⟨7⟩ σ_evm I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (hsub : (vowSlotWord (flogEraSlot I) σ_evm I).toNat ≤
      (vowSlotWord ⟨5⟩ σ_evm I).toNat) :
    let era := flogEra I
    let wait := vowSlotWord ⟨7⟩ σ_evm I
    let doneAt := era + wait
    let SinVal := vowSlotWord ⟨5⟩ σ_evm I
    let sinVal := vowSlotWord (flogEraSlot I) σ_evm I
    let SinNew := UInt256.sub SinVal sinVal
    let locals := flogLocals I
    let locals2 := flogLocalsDoneAtSinNew I doneAt SinNew
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ SinNew
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner (flogEraSlot I) ⟨0⟩
    ExecTransitionBody config contract evm0 locals flogTransition.body
      (.returned { contract := contract, locals := locals2 } evm2 none) := by
  intro era wait doneAt SinVal sinVal SinNew locals locals2 evm0 evm1 evm2
  let locals1 := flogLocalsDoneAt I doneAt
  have hwaitWord : wait = vowSlotWord ⟨7⟩ σ_solm I := by
    simpa [wait] using accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  have hSinWord : SinVal = vowSlotWord ⟨5⟩ σ_solm I := by
    simpa [SinVal] using accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hsinWord : sinVal = vowSlotWord (flogEraSlot I) σ_solm I := by
    simpa [sinVal] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flogEraSlot I) ⟨0⟩
  have hwaitLoad : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ = wait := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ =
        vowSlotWord ⟨7⟩ σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hwaitWord.symm
  have hSinLoad : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨5⟩ = SinVal := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hSinWord.symm
  have hsinLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (flogEraSlot I) = sinVal := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (flogEraSlot I) =
        vowSlotWord (flogEraSlot I) σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hsinWord.symm
  have hcallAdd :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.internalCall "add" [.var "era", .storage waitRef] "doneAt")
        (.ok { contract := contract, locals := locals1 } evm0) := by
    simpa [locals, locals1, doneAt] using
      (flogInternalAddReturn I evm0 (wait := wait) (doneAt := doneAt)
        hwaitLoad (by rfl) (by simpa [era, wait] using hfitWait))
  have hreadyEval :
      evalExpr? config { contract := contract, locals := locals1 } evm0
        (.binary .le (.var "doneAt") (.env .timestamp)) = .ok (.bool true) := by
    have hdone :
        evalExpr? config { contract := contract, locals := locals1 } evm0 (.var "doneAt") =
          .ok (.int (Int.ofNat doneAt.toNat)) := by
      simpa [locals1, doneAt] using
        evalExpr_varUInt256 (evm := evm0) (locals := locals1) (name := "doneAt")
          (value := doneAt) (flogLocalsDoneAt_get_doneAt I doneAt)
    have htime :
        evalExpr? config { contract := contract, locals := locals1 } evm0 (.env .timestamp) =
          .ok (.int (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat)) := by
      simp [evm0, initState, evalExpr?, envValue, pure]
    exact evalExpr_le_uint256_true hdone htime (by simpa [doneAt, wait] using hready)
  have hcallSub :
      ExecStmt config { contract := contract, locals := locals1 } evm0
        (.internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew")
        (.ok { contract := contract, locals := locals2 } evm0) := by
    simpa [locals1, locals2, SinVal, sinVal, SinNew] using
      (flogInternalSubReturn I evm0 (doneAt := doneAt) (SinVal := SinVal)
        (sinVal := sinVal) (SinNew := SinNew) hSinLoad hsinLoad (by rfl)
        (by simpa [SinVal, sinVal] using hsub))
  have hSinNewVar :
      evalExpr? config { contract := contract, locals := locals2 } evm0 (.var "SinNew") =
        .ok (.int (Int.ofNat SinNew.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evm0) (locals := locals2) (name := "SinNew")
        (value := SinNew) (flogLocalsDoneAtSinNew_get_SinNew I doneAt SinNew)
  have hassignSinCapital :
      assignStorageRef? config { contract := contract, locals := locals2 } evm0
        .storage SinRef (.int (Int.ofNat SinNew.toNat)) =
          .ok ({ contract := contract, locals := locals2 }, evm1) := by
    simpa [evm1, locals2] using
      (assign_flogSinCapitalStorage evm0 (locals := locals2) SinNew
        (by simp [locals2, flogLocalsDoneAtSinNew, flogLocalsDoneAt, flogLocals]))
  have hzero :
      evalExpr? config { contract := contract, locals := locals2 } evm1 (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hassignSin :
      assignStorageRef? config { contract := contract, locals := locals2 } evm1
        .storage (sinRef (.var "era")) (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) =
          .ok ({ contract := contract, locals := locals2 }, evm2) := by
    simpa [evm2, locals2] using
      (assign_flogSinStorage evm1 (I := I) (locals := locals2) (⟨0⟩ : UInt256)
        (by simp [locals2, flogLocalsDoneAtSinNew, flogLocalsDoneAt, flogLocals])
        (by simpa [locals2] using flogLocalsDoneAtSinNew_get_era I doneAt SinNew))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .internalCall "add" [.var "era", .storage waitRef] "doneAt",
          .require (.binary .le (.var "doneAt") (.env .timestamp)),
          .internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew",
          .assign .storage SinRef (.var "SinNew"),
          .assign .storage (sinRef (.var "era")) (.intLit 0) ]
        (.ok { contract := contract, locals := locals2 } evm2) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal hcallAdd ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreadyEval) ?_
    refine ExecBlock.consNormal hcallSub ?_
    refine ExecBlock.consNormal (ExecStmt.assign hSinNewVar hassignSinCapital) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hzero hassignSin) ExecBlock.nil
  simpa [ExecTransitionBody, flogTransition, nonpayable, evm0, locals] using
    ExecFuncBody.execBlockOK hblock

theorem vowFlogSourceAddOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hover : UInt256.size ≤ (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ_evm I).toNat) :
    ExecTransitionBody config contract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flogLocals I)
      flogTransition.body .reverted := by
  let wait := vowSlotWord ⟨7⟩ σ_evm I
  let locals := flogLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hwaitWord : wait = vowSlotWord ⟨7⟩ σ_solm I := by
    simpa [wait] using accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  have hwaitLoad : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ = wait := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ =
        vowSlotWord ⟨7⟩ σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hwaitWord.symm
  have hcallAdd :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.internalCall "add" [.var "era", .storage waitRef] "doneAt") .reverted := by
    simpa [locals] using
      (flogInternalAddRevert I evm0 (wait := wait) hwaitLoad
        (by simpa [wait] using hover))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .internalCall "add" [.var "era", .storage waitRef] "doneAt",
          .require (.binary .le (.var "doneAt") (.env .timestamp)),
          .internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew",
          .assign .storage SinRef (.var "SinNew"),
          .assign .storage (sinRef (.var "era")) (.intLit 0) ] .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert hcallAdd
  simpa [ExecTransitionBody, flogTransition, nonpayable, evm0, locals] using
    ExecFuncBody.execBlockRevert hblock

theorem vowFlogSourceWaitNotFinished
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hfitWait : (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ_evm I).toNat < UInt256.size)
    (hnotReady : (UInt256.ofNat I.header.timestamp).toNat <
      (flogEra I + vowSlotWord ⟨7⟩ σ_evm I).toNat) :
    ExecTransitionBody config contract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flogLocals I)
      flogTransition.body .reverted := by
  let era := flogEra I
  let wait := vowSlotWord ⟨7⟩ σ_evm I
  let doneAt := era + wait
  let locals := flogLocals I
  let locals1 := flogLocalsDoneAt I doneAt
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hwaitWord : wait = vowSlotWord ⟨7⟩ σ_solm I := by
    simpa [wait] using accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  have hwaitLoad : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ = wait := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ =
        vowSlotWord ⟨7⟩ σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hwaitWord.symm
  have hcallAdd :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.internalCall "add" [.var "era", .storage waitRef] "doneAt")
        (.ok { contract := contract, locals := locals1 } evm0) := by
    simpa [locals, locals1, doneAt] using
      (flogInternalAddReturn I evm0 (wait := wait) (doneAt := doneAt)
        hwaitLoad (by rfl) (by simpa [era, wait] using hfitWait))
  have hreadyEval :
      evalExpr? config { contract := contract, locals := locals1 } evm0
        (.binary .le (.var "doneAt") (.env .timestamp)) = .ok (.bool false) := by
    have hdone :
        evalExpr? config { contract := contract, locals := locals1 } evm0 (.var "doneAt") =
          .ok (.int (Int.ofNat doneAt.toNat)) := by
      simpa [locals1, doneAt] using
        evalExpr_varUInt256 (evm := evm0) (locals := locals1) (name := "doneAt")
          (value := doneAt) (flogLocalsDoneAt_get_doneAt I doneAt)
    have htime :
        evalExpr? config { contract := contract, locals := locals1 } evm0 (.env .timestamp) =
          .ok (.int (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat)) := by
      simp [evm0, initState, evalExpr?, envValue, pure]
    exact evalExpr_le_uint256_false hdone htime (by simpa [doneAt, wait] using hnotReady)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .internalCall "add" [.var "era", .storage waitRef] "doneAt",
          .require (.binary .le (.var "doneAt") (.env .timestamp)),
          .internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew",
          .assign .storage SinRef (.var "SinNew"),
          .assign .storage (sinRef (.var "era")) (.intLit 0) ] .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal hcallAdd ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreadyEval)
  simpa [ExecTransitionBody, flogTransition, nonpayable, evm0, locals] using
    ExecFuncBody.execBlockRevert hblock

theorem vowFlogSourceSubUnderflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hfitWait : (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ_evm I).toNat < UInt256.size)
    (hready : (flogEra I + vowSlotWord ⟨7⟩ σ_evm I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (hlt : (vowSlotWord ⟨5⟩ σ_evm I).toNat <
      (vowSlotWord (flogEraSlot I) σ_evm I).toNat) :
    ExecTransitionBody config contract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (flogLocals I)
      flogTransition.body .reverted := by
  let era := flogEra I
  let wait := vowSlotWord ⟨7⟩ σ_evm I
  let doneAt := era + wait
  let SinVal := vowSlotWord ⟨5⟩ σ_evm I
  let sinVal := vowSlotWord (flogEraSlot I) σ_evm I
  let locals := flogLocals I
  let locals1 := flogLocalsDoneAt I doneAt
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hwaitWord : wait = vowSlotWord ⟨7⟩ σ_solm I := by
    simpa [wait] using accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  have hSinWord : SinVal = vowSlotWord ⟨5⟩ σ_solm I := by
    simpa [SinVal] using accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hsinWord : sinVal = vowSlotWord (flogEraSlot I) σ_solm I := by
    simpa [sinVal] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flogEraSlot I) ⟨0⟩
  have hwaitLoad : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ = wait := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩ =
        vowSlotWord ⟨7⟩ σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hwaitWord.symm
  have hSinLoad : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨5⟩ = SinVal := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hSinWord.symm
  have hsinLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (flogEraSlot I) = sinVal := by
    have hload : Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (flogEraSlot I) =
        vowSlotWord (flogEraSlot I) σ_solm I := by
      simp [evm0, initState, vowSlotWord, solcSlotWord, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    exact hload.trans hsinWord.symm
  have hcallAdd :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.internalCall "add" [.var "era", .storage waitRef] "doneAt")
        (.ok { contract := contract, locals := locals1 } evm0) := by
    simpa [locals, locals1, doneAt] using
      (flogInternalAddReturn I evm0 (wait := wait) (doneAt := doneAt)
        hwaitLoad (by rfl) (by simpa [era, wait] using hfitWait))
  have hreadyEval :
      evalExpr? config { contract := contract, locals := locals1 } evm0
        (.binary .le (.var "doneAt") (.env .timestamp)) = .ok (.bool true) := by
    have hdone :
        evalExpr? config { contract := contract, locals := locals1 } evm0 (.var "doneAt") =
          .ok (.int (Int.ofNat doneAt.toNat)) := by
      simpa [locals1, doneAt] using
        evalExpr_varUInt256 (evm := evm0) (locals := locals1) (name := "doneAt")
          (value := doneAt) (flogLocalsDoneAt_get_doneAt I doneAt)
    have htime :
        evalExpr? config { contract := contract, locals := locals1 } evm0 (.env .timestamp) =
          .ok (.int (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat)) := by
      simp [evm0, initState, evalExpr?, envValue, pure]
    exact evalExpr_le_uint256_true hdone htime (by simpa [doneAt, wait] using hready)
  have hcallSub :
      ExecStmt config { contract := contract, locals := locals1 } evm0
        (.internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew")
        .reverted := by
    simpa [locals1, SinVal, sinVal] using
      (flogInternalSubRevert I evm0 (doneAt := doneAt) (SinVal := SinVal)
        (sinVal := sinVal) hSinLoad hsinLoad (by simpa [SinVal, sinVal] using hlt))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .internalCall "add" [.var "era", .storage waitRef] "doneAt",
          .require (.binary .le (.var "doneAt") (.env .timestamp)),
          .internalCall "sub" [.storage SinRef, .storage (sinRef (.var "era"))] "SinNew",
          .assign .storage SinRef (.var "SinNew"),
          .assign .storage (sinRef (.var "era")) (.intLit 0) ] .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal hcallAdd ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreadyEval) ?_
    exact ExecBlock.consRevert hcallSub
  simpa [ExecTransitionBody, flogTransition, nonpayable, evm0, locals] using
    ExecFuncBody.execBlockRevert hblock

theorem vowDispatch_flog {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩) :
    dispatchMsg contract I.calldata = some flogTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition])
    (post := [flopTransition, flopperTransition, healTransition, humpTransition, kissTransition,
      liveTransition, relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition])
    (ti := flogTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xd7, 0xee, 0x67, 0x4b]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        hcd]
      native_decide
  · rw [selectorOf, flogSelectorBytes]
    exact hsel

theorem vowDecode_flog_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flogTransition.params.map Param.name)
      (transitionSignature flogTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "era" (.int (Int.ofNat (flogEra I).toNat))) := by
  simpa [config, flogTransition, flogEra, uint256] using
    (decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "era") hsz36)

theorem vowDecode_flog_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (flogTransition.params.map Param.name)
      (transitionSignature flogTransition).paramTypes I.calldata = none := by
  simpa [config, flogTransition, uint256] using
    (decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "era") hsz4 hshort)

theorem vowReachFlogBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨781⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨3622725451⟩ :=
    vowSelWord_eq_of_beq I hsz 0xd7 0xee 0x67 0x4b ⟨3622725451⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc 3))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighHighBody 3 (by omega) ⟨781⟩ hcode hwv hsz hsize hroot hhigh heq0
    htake (by jump_dest) (by native_decide)

theorem RD.vowFlogDecodeToRoutine
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4498⟩
      [flogEra I, ⟨412⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  let era := flogEra I
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨781⟩) (ret := ⟨412⟩)
    (decoded := ⟨803⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  have rd804 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd805 := rd804.pop (by native_decide) (by evm_ov)
  have rd806 := rd805.calldataload (by native_decide) (by evm_ov)
  have rd809 := rd806.push2 ⟨4498⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [era, flogEra, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd809.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.vowFlogToFirstAdd
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5074⟩
      (vowSlotWord ⟨7⟩ σ I :: flogEra I :: ⟨4511⟩ ::
        UInt256.ofNat I.header.timestamp :: flogEra I :: ⟨412⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, htoRoutine⟩ := RD.vowFlogDecodeToRoutine hreach hsz36 hsize
  have rd4499 := htoRoutine.jumpdest (by native_decide) (by evm_ov)
  have rd4500 := rd4499.timestamp (by native_decide) (by evm_ov)
  have rd4503 := rd4500.push2 ⟨4511⟩ (by native_decide) (by evm_ov)
  have rd4504 := rd4503.dup3 (by native_decide) (by evm_ov)
  have rd4506 := rd4504.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4507⟩ := rd4506.sload (by native_decide) (by evm_ov)
  have rd4510 := rd4507.push2 ⟨5074⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [vowSlotWord, solcSlotWord] using
      rd4510.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.vowFlogAfterWaitReady
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hfit : (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ I).toNat < UInt256.size)
    (hready : (flogEra I + vowSlotWord ⟨7⟩ σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4586⟩
      [flogEra I, ⟨412⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  let wait := vowSlotWord ⟨7⟩ σ I
  obtain ⟨_, _, hfirstAdd⟩ := RD.vowFlogToFirstAdd hreach hsz36 hsize
  obtain ⟨_, _, hafterAdd⟩ := RD.solcCheckedAddSuccess
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := flogEra I) (b := wait) (ret := ⟨4511⟩)
    (R := [UInt256.ofNat I.header.timestamp, flogEra I, ⟨412⟩, sel])
    (by simpa [wait] using hfirstAdd)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [wait] using hfit)
    (by jump_dest) (by jump_dest) (by simp)
  have rd4512 := hafterAdd.jumpdest (by native_decide) (by evm_ov)
  have rd4513₀ := rd4512.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (flogEra I + wait) (UInt256.ofNat I.header.timestamp) = ⟨0⟩ :=
    ugt_zero (by simpa [wait] using hready)
  have rd4513 := rd4513₀
  rw [hgt] at rd4513
  have rd4514₀ := rd4513.iszero (by native_decide) (by evm_ov)
  have rd4514 := rd4514₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4514
  have rd4517 := rd4514.push2 ⟨4586⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [wait] using
      rd4517.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.vowFlogFirstAddOverflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hover : UInt256.size ≤ (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let wait := vowSlotWord ⟨7⟩ σ I
  obtain ⟨_, _, hfirstAdd⟩ := RD.vowFlogToFirstAdd hreach hsz36 hsize
  exact RD.solcCheckedAddEmptyRevert
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := flogEra I) (b := wait) (ret := ⟨4511⟩)
    (R := [UInt256.ofNat I.header.timestamp, flogEra I, ⟨412⟩, sel])
    (by simpa [wait] using hfirstAdd)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [wait] using hover)
    (by simp)

@[reducible] def vowFlogToCheckedSubWf
    (code : ByteArray) (pc afterSubPc routinePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p16 := p14 + UInt256.ofNat 2
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p22 := p19 + UInt256.ofNat 3
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p27 := p24 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨5⟩, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p6 = some (.DUP3, .none)
  ∧ decode code p7 = some (.DUP2, .none)
  ∧ decode code p8 = some (.MSTORE, .none)
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p13 = some (.MSTORE, .none)
  ∧ decode code p14 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p16 = some (.SWAP1, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.SLOAD, .none)
  ∧ decode code p19 = some (.Push .PUSH2, some (afterSubPc, 2))
  ∧ decode code p22 = some (.SWAP2, .none)
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p27 = some (.JUMP, .none)

theorem RD.vowFlogToCheckedSub {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc afterSubPc routinePc era ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (era :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowFlogToCheckedSubWf code pc afterSubPc routinePc)
    (hmem : mem.size = 96)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (solcSlotWord σ ee (solcMappingSlot ⟨4⟩ era) :: solcSlotWord σ ee ⟨5⟩ ::
        afterSubPc :: era :: ret :: R)
      (twoWordHashMem era ⟨4⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd8, hd9, hd11, hd13, hd14, hd16,
      hd17, hd18, hd19, hd22, hd23, hd24, hd27⟩
  have rdBeforeLoad := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨5⟩ hd1 (by evm_ov)]
  obtain ⟨_, _, rdSin⟩ := rdBeforeLoad.sload hd3 (by evm_ov)
  have rdMem0Prefix := evm_run rdSin with [
    raw push1 ⟨0⟩ hd4 (by evm_ov),
    raw dup3 hd6 (by evm_ov),
    raw dup2 hd7 (by evm_ov)]
  have rdMem0 := rdMem0Prefix.mstore 0 (wordAt0Mem era mem)
    (UInt256.ofNat 3) hd8 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMemSlotPrefix := evm_run rdMem0 with [
    raw push1 ⟨4⟩ hd9 (by evm_ov),
    raw push1 ⟨32⟩ hd11 (by evm_ov)]
  have rdHashMem := rdMemSlotPrefix.mstore 0 (twoWordHashMem era ⟨4⟩ mem)
    (UInt256.ofNat 3) hd13 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd14 (by evm_ov),
    raw swap1 hd16 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨4⟩ era hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨4⟩ era)
    (UInt256.ofNat 3) hd17 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoaded⟩ := rdSlot.sload hd18 (by evm_ov)
  have rdJump := evm_run rdLoaded with [
    raw push2 afterSubPc hd19 (by evm_ov),
    raw swap2 hd22 (by evm_ov),
    raw swap1 hd23 (by evm_ov),
    raw push2 routinePc hd24 (by evm_ov)]
  exact ⟨_, _, by simpa [solcSlotWord] using rdJump.jump hd27 hroutine (by evm_ov)⟩

@[reducible] def vowFlogStoreSinAndClearWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p16 := p14 + UInt256.ofNat 2
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨5⟩, 1))
  ∧ decode code p3 = some (.SSTORE, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.DUP2, .none)
  ∧ decode code p8 = some (.MSTORE, .none)
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p13 = some (.MSTORE, .none)
  ∧ decode code p14 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.SSTORE, .none)
  ∧ decode code p19 = some (.JUMP, .none)

theorem RD.vowFlogStoreSinAndClear {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc SinNew era ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (SinNew :: era :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hwf : vowFlogStoreSinAndClearWf code pc)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem era ⟨4⟩ mem) (UInt256.ofNat 3)
      rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ ⟨5⟩ SinNew) (solcMappingSlot ⟨4⟩ era) ⟨0⟩)
      k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd8, hd9, hd11, hd13, hd14, hd16, hd17,
      hd18, hd19⟩
  let σ1 := sstoreAccountMap ee.codeOwner σ ⟨5⟩ SinNew
  have rdStoreSinPrefix := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨5⟩ hd1 (by evm_ov)]
  obtain ⟨_, _, rdStoreSin⟩ := rdStoreSinPrefix.sstore hperm hd3 (by evm_ov)
  have rdMem0Prefix := evm_run rdStoreSin with [
    raw push1 ⟨0⟩ hd4 (by evm_ov),
    raw swap1 hd6 (by evm_ov),
    raw dup2 hd7 (by evm_ov)]
  have rdMem0 := rdMem0Prefix.mstore 0 (wordAt0Mem era mem)
    (UInt256.ofNat 3) hd8 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMemSlotPrefix := evm_run rdMem0 with [
    raw push1 ⟨4⟩ hd9 (by evm_ov),
    raw push1 ⟨32⟩ hd11 (by evm_ov)]
  have rdHashMem := rdMemSlotPrefix.mstore 0 (twoWordHashMem era ⟨4⟩ mem)
    (UInt256.ofNat 3) hd13 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd14 (by evm_ov),
    raw dup2 hd16 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨4⟩ era hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨4⟩ era)
    (UInt256.ofNat 3) hd17 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdStoreZero⟩ := rdSlot.sstore hperm hd18 (by evm_ov)
  exact ⟨_, _, by simpa [σ1] using rdStoreZero.jump hd19 hret (by evm_ov)⟩

theorem RD.vowFlogSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hfitWait : (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ I).toNat < UInt256.size)
    (hready : (flogEra I + vowSlotWord ⟨7⟩ σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (hsub : (vowSlotWord (flogEraSlot I) σ I).toNat ≤ (vowSlotWord ⟨5⟩ σ I).toNat) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨5⟩
          (UInt256.sub (vowSlotWord ⟨5⟩ σ I) (vowSlotWord (flogEraSlot I) σ I)))
        (flogEraSlot I) ⟨0⟩)
      ByteArray.empty := by
  let era := flogEra I
  let eraSlot := solcMappingSlot ⟨4⟩ era
  let sinEra := solcSlotWord σ I eraSlot
  let SinNew := UInt256.sub (solcSlotWord σ I ⟨5⟩) sinEra
  obtain ⟨_, _, hafterReady⟩ := RD.vowFlogAfterWaitReady hreach hsz36 hsize hfitWait hready
  obtain ⟨_, _, htoSub⟩ := RD.vowFlogToCheckedSub
    (code := vowBytecode) (pc := ⟨4586⟩) (afterSubPc := ⟨4614⟩)
    (routinePc := ⟨5096⟩) (era := era) (ret := ⟨412⟩) (R := [sel])
    (by simpa [era] using hafterReady)
    (by
      unfold vowFlogToCheckedSubWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_size (by jump_dest) (by simp)
  obtain ⟨_, _, hafterSub⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := solcSlotWord σ I ⟨5⟩) (b := sinEra) (ret := ⟨4614⟩)
    (R := [era, ⟨412⟩, sel])
    (by simpa [era, eraSlot, sinEra] using htoSub)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [era, eraSlot, sinEra, flogEraSlot_eq, vowSlotWord] using hsub)
    (by jump_dest) (by jump_dest) (by simp)
  have hmem : (twoWordHashMem era ⟨4⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 era ⟨4⟩ solcFreePtrMem_size
  obtain ⟨_, _, hretPc⟩ := RD.vowFlogStoreSinAndClear
    (code := vowBytecode) (pc := ⟨4614⟩) (SinNew := SinNew) (era := era)
    (ret := ⟨412⟩) (R := [sel])
    (by simpa [SinNew, era, eraSlot, sinEra] using hafterSub)
    (by
      unfold vowFlogStoreSinAndClearWf
      repeat' first | apply And.intro | native_decide)
    hmem hperm (by jump_dest) (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  simpa [era, eraSlot, sinEra, SinNew, flogEraSlot_eq, vowSlotWord] using
    RD.stop hretPc' (by native_decide) (by simp)

theorem RD.vowFlogSubUnderflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hfitWait : (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ I).toNat < UInt256.size)
    (hready : (flogEra I + vowSlotWord ⟨7⟩ σ I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (hlt : (vowSlotWord ⟨5⟩ σ I).toNat < (vowSlotWord (flogEraSlot I) σ I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let era := flogEra I
  let eraSlot := solcMappingSlot ⟨4⟩ era
  let sinEra := solcSlotWord σ I eraSlot
  obtain ⟨_, _, hafterReady⟩ := RD.vowFlogAfterWaitReady hreach hsz36 hsize hfitWait hready
  obtain ⟨_, _, htoSub⟩ := RD.vowFlogToCheckedSub
    (code := vowBytecode) (pc := ⟨4586⟩) (afterSubPc := ⟨4614⟩)
    (routinePc := ⟨5096⟩) (era := era) (ret := ⟨412⟩) (R := [sel])
    (by simpa [era] using hafterReady)
    (by
      unfold vowFlogToCheckedSubWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_size (by jump_dest) (by simp)
  exact RD.solcCheckedSubEmptyRevert
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := solcSlotWord σ I ⟨5⟩) (b := sinEra) (ret := ⟨4614⟩)
    (R := [era, ⟨412⟩, sel])
    (by simpa [era, eraSlot, sinEra] using htoSub)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [era, eraSlot, sinEra, flogEraSlot_eq, vowSlotWord] using hlt)
    (by simp)

abbrev vowWaitNotFinishedRawWord : UInt256 :=
  ⟨31581374177399561354076032325440466293602194692441⟩

theorem RD.vowFlogWaitNotFinished
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hfit : (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ I).toNat < UInt256.size)
    (hnotReady : (UInt256.ofNat I.header.timestamp).toNat <
      (flogEra I + vowSlotWord ⟨7⟩ σ I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let wait := vowSlotWord ⟨7⟩ σ I
  obtain ⟨_, _, hfirstAdd⟩ := RD.vowFlogToFirstAdd hreach hsz36 hsize
  obtain ⟨_, _, hafterAdd⟩ := RD.solcCheckedAddSuccess
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := flogEra I) (b := wait) (ret := ⟨4511⟩)
    (R := [UInt256.ofNat I.header.timestamp, flogEra I, ⟨412⟩, sel])
    (by simpa [wait] using hfirstAdd)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [wait] using hfit)
    (by jump_dest) (by jump_dest) (by simp)
  have rd4512 := hafterAdd.jumpdest (by native_decide) (by evm_ov)
  have rd4513₀ := rd4512.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (flogEra I + wait) (UInt256.ofNat I.header.timestamp) = ⟨1⟩ :=
    ugt_one (by simpa [wait] using hnotReady)
  have rd4513 := rd4513₀
  rw [hgt] at rd4513
  have rd4514₀ := rd4513.iszero (by native_decide) (by evm_ov)
  have rd4514 := rd4514₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4514
  have rd4517 := rd4514.push2 ⟨4586⟩ (by native_decide) (by evm_ov)
  have rdTail₀ := rd4517.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨4518⟩) (len := ⟨21⟩) (rawWord := vowWaitNotFinishedRawWord)
    (shift := ⟨90⟩) (op := .PUSH21) (width := 21)
    (word := UInt256.shiftLeft vowWaitNotFinishedRawWord ⟨90⟩)
    (by simpa [wait] using rdTail₀)
    (by
      unfold solcErrorStringRevertTailWf vowWaitNotFinishedRawWord
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) solcFreePtrMem_size solcFreePtrMem_read64 (by simp)

theorem vowFlogBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some flogTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flogTransition.params.map Param.name)
        (transitionSignature flogTransition).paramTypes I.calldata = some (flogLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨781⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hfitWait :
      (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ_evm I).toNat < UInt256.size
  · by_cases hready : (flogEra I + vowSlotWord ⟨7⟩ σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat
    · by_cases hsub : (vowSlotWord (flogEraSlot I) σ_evm I).toNat ≤
          (vowSlotWord ⟨5⟩ σ_evm I).toNat
      · let era := flogEra I
        let wait := vowSlotWord ⟨7⟩ σ_evm I
        let doneAt := era + wait
        let SinVal := vowSlotWord ⟨5⟩ σ_evm I
        let sinVal := vowSlotWord (flogEraSlot I) σ_evm I
        let SinNew := UInt256.sub SinVal sinVal
        let locals := flogLocals I
        let locals2 := flogLocalsDoneAtSinNew I doneAt SinNew
        let σ1_evm := sstoreAccountMap I.codeOwner σ_evm ⟨5⟩ SinNew
        let σ2_evm := sstoreAccountMap I.codeOwner σ1_evm (flogEraSlot I) ⟨0⟩
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ SinNew
        let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner (flogEraSlot I) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract evm0 locals flogTransition.body
              (.returned { contract := contract, locals := locals2 } evm2 none) := by
          simpa [era, wait, doneAt, SinVal, sinVal, SinNew, locals, locals2, evm0, evm1,
            evm2] using
              (vowFlogSourceSuccess (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hAccounts hfitWait hready hsub)
        have hret := RD.vowFlogSuccess hreach hperm hsz36 hsize hfitWait hready hsub
        have hcreated : (cA, σ2_evm).1 = evm2.createdAccounts := by
          simp [evm2, evm1, evm0, initState, storageStore_createdAccounts]
        have haccounts1 : accountMapEquiv σ1_evm evm1.accountMap := by
          simpa [σ1_evm, evm1, evm0, initState, storageStore_accountMap] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ SinNew hAccounts
        have haccounts : accountMapEquiv (cA, σ2_evm).2 evm2.accountMap := by
          simpa [σ2_evm, evm2, evm1, evm0, initState, storageStore_accountMap,
            storageStore_executionEnv] using
              accountMapEquiv_sstoreAccountMap I.codeOwner (flogEraSlot I) ⟨0⟩ haccounts1
        have henc : returnEquiv ByteArray.empty none flogTransition.returnType := by
          rw [show flogTransition.returnType = [] by rfl]
          exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
        have hret' :
            RDret vowBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (cA, σ2_evm) ByteArray.empty := by
          simpa [σ2_evm, σ1_evm, SinNew, SinVal, sinVal] using hret
        exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          hcreated haccounts henc
      · have hlt : (vowSlotWord ⟨5⟩ σ_evm I).toNat <
            (vowSlotWord (flogEraSlot I) σ_evm I).toNat := by
          omega
        have hbody := vowFlogSourceSubUnderflow (cA := cA) (gh := gh) (bl := bl)
          (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) hwv hAccounts hfitWait hready hlt
        have hrev := RD.vowFlogSubUnderflow hreach hsz36 hsize hfitWait hready hlt
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hnotReady : (UInt256.ofNat I.header.timestamp).toNat <
          (flogEra I + vowSlotWord ⟨7⟩ σ_evm I).toNat := by
        omega
      have hbody := vowFlogSourceWaitNotFinished (cA := cA) (gh := gh) (bl := bl)
        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) hwv hAccounts hfitWait hnotReady
      have hrev := RD.vowFlogWaitNotFinished hreach hsz36 hsize hfitWait hnotReady
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hover : UInt256.size ≤
        (flogEra I).toNat + (vowSlotWord ⟨7⟩ σ_evm I).toNat := by
      omega
    have hbody := vowFlogSourceAddOverflow (cA := cA) (gh := gh) (bl := bl)
      (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hwv hAccounts hover
    have hrev := RD.vowFlogFirstAddOverflow hreach hsz36 hsize hover
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlogBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  exact vowFlogBodyCore hcode hwv hperm hsz36 hsize (vowDispatch_flog hsel)
    (by simpa [flogLocals] using vowDecode_flog_ok (I := I) hsz36)
    (vowReachFlogBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel)
    hAccounts

theorem vowFlogShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachFlogBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨781⟩) (ret := ⟨412⟩)
    (decoded := ⟨803⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_flog hsel)
    (vowDecode_flog_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
