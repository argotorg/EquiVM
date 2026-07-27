import Benchmarks.Dss.Clipper.YankSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperYankFluxRetStore_removeArgs (I : ExecutionEnv) (v : ClipperImmutables)
    (evm : EVM.State) :
    evalExprs? (config v) { contract := (contract v), locals := clipperYankFluxRetStore I }
        evm [.var "id"] =
      .ok [clipperYankArgValue I] := by
  have hgetId :
      (clipperYankFluxRetStore I).get? "id" = some (clipperYankArgValue I) := by
    unfold clipperYankFluxRetStore clipperYankDogRetStore
    rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
    simp [clipperYankStore]
  have hgetIdElem :
      (clipperYankFluxRetStore I)["id"]? = some (clipperYankArgValue I) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have hmemId : "id" ∈ clipperYankFluxRetStore I := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [hgetIdElem]
    rfl
  have hgetIdVal :
      (clipperYankFluxRetStore I)["id"] = clipperYankArgValue I := by
    rw [Std.HashMap.getElem_eq_getD (fallback := (.unit : Value)) (h' := hmemId)]
    have hsome := Std.HashMap.getElem?_eq_some_getD
      (m := clipperYankFluxRetStore I) (a := "id") (fallback := (.unit : Value)) hmemId
    rw [hgetIdElem] at hsome
    injection hsome with hval
    exact hval.symm
  exact evalExprs?_singleton (by simp [evalExpr?, hgetIdVal, EvalResult.ofOption])

theorem clipperYankFluxRetStore_removeRet_locked (I : ExecutionEnv) :
    ((clipperYankFluxRetStore I).insert "_removeRet" .unit).get? "locked" = none := by
  unfold clipperYankFluxRetStore clipperYankDogRetStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  exact clipperYankStore_get_locked I

theorem clipperYankRemoveIndexStore_get_active (I : ExecutionEnv)
    (lastIndex move idx : UInt256) :
    (clipperYankRemoveIndexStore I lastIndex move idx).get? "active" = none := by
  unfold clipperYankRemoveIndexStore clipperYankRemoveMoveStore
    clipperYankRemoveLastIndexStore clipperYankRemoveStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

theorem clipperYankRemoveIndexStore_get_sales (I : ExecutionEnv)
    (lastIndex move idx : UInt256) :
    (clipperYankRemoveIndexStore I lastIndex move idx).get? "sales" = none := by
  unfold clipperYankRemoveIndexStore clipperYankRemoveMoveStore
    clipperYankRemoveLastIndexStore clipperYankRemoveStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

theorem clipperYankRemoveIndexStore_get_id (I : ExecutionEnv)
    (lastIndex move idx : UInt256) :
    (clipperYankRemoveIndexStore I lastIndex move idx).get? "id" =
      some (clipperYankArgValue I) := by
  unfold clipperYankRemoveIndexStore
  rw [store_get_ne _ _ (by native_decide)]
  exact clipperYankRemoveMoveStore_get_id I lastIndex move

theorem clipperEvalYankRemoveSalesPos_moveStore (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) (lastIndex move : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
      (.storage (salesF (.var "id") "pos")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankSalesPosSlot I)).toNat)) := by
  let frame : Frame :=
    { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
  have hgetIdElem :
      ((clipperYankRemoveMoveStore I lastIndex move)["id"]?) =
        some (clipperYankArgValue I) := by
    simpa [Std.HashMap.get?_eq_getElem?] using
      clipperYankRemoveMoveStore_get_id I lastIndex move
  have hmemId : "id" ∈ clipperYankRemoveMoveStore I lastIndex move := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [hgetIdElem]
    rfl
  have hgetIdVal :
      (clipperYankRemoveMoveStore I lastIndex move)["id"] = clipperYankArgValue I := by
    rw [Std.HashMap.getElem_eq_getD (fallback := (.unit : Value)) (h' := hmemId)]
    have hsome := Std.HashMap.getElem?_eq_some_getD
      (m := clipperYankRemoveMoveStore I lastIndex move) (a := "id")
      (fallback := (.unit : Value)) hmemId
    rw [hgetIdElem] at hsome
    injection hsome with hval
    exact hval.symm
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "pos") (er := clipperYankSalesPosRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperYankSalesPosSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperYankSalesPosSlot I)).toNat))
    (by simp [frame, salesF, clipperYankRemoveMoveStore, clipperYankRemoveLastIndexStore,
      clipperYankRemoveStore])
    (by
      simp [frame, clipperYankSalesPosRef, clipperYankArgValue, clipperYankArgKey,
        salesF, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
        valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind, hgetIdVal])
    (by simp [frame, clipperYankArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperYankSalesPosSlot, clipperYankSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperYankSalesPosSlot I))

theorem clipperEvalYankRemoveMove_indexStore (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) (lastIndex move idx : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx } evm
      (.var "_move") = .ok (.int (Int.ofNat move.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((clipperYankRemoveIndexStore I lastIndex move idx).get? "_move") = _
  unfold clipperYankRemoveIndexStore clipperYankRemoveMoveStore
  rw [store_get_ne _ _ (by native_decide), store_get_self]
  rfl

theorem clipperEvalYankRemoveIndex_indexStore (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv) (lastIndex move idx : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx } evm
      (.var "_index") = .ok (.int (Int.ofNat idx.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((clipperYankRemoveIndexStore I lastIndex move idx).get? "_index") = _
  unfold clipperYankRemoveIndexStore
  rw [store_get_self]
  rfl

theorem clipperYankRemoveAssignActiveRevert (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex move idx : UInt256)
    (hbound :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat ≤ idx.toNat) :
    assignStorageRef? (config v)
      { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx } evm
      .storage (activeElemRef (.var "_index")) (.int (Int.ofNat move.toNat)) =
      .revert := by
  have hnot :
      ¬ idx.toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat :=
    Nat.not_lt_of_ge hbound
  have hidxEval :=
    clipperEvalYankRemoveIndex_indexStore v evm I lastIndex move idx
  unfold assignStorageRef? resolveStorageRef? evalStorageRef evalStorageRefSteps evalStorageRefStep
  simp only [hidxEval, EvalResult.ofOption, EvalResult.bind, bind, pure, valueToKey?, activeElemRef]
  simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, storageTypeAt?, contract,
    storageDecls, clipperStorageLocLoad_uint256, hnot]

theorem clipperYankRemovePopActiveRevert (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hactive : locals.get? "active" = none)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    popArray? (config v) { contract := contract v, locals := locals } evm activeRef =
      .revert := by
  have hresolve :
      resolveStorageRef? (config v)
        { contract := contract v, locals := locals }
        evm activeRef =
        .ok (({ base := "active", steps := [] } : EvaledStorageRef), .dynamicArray uint256St) := by
    have hactiveElem : locals["active"]? = none := by
      simpa [Std.HashMap.get?_eq_getElem?] using hactive
    simp [resolveStorageRef?, evalStorageRef, activeRef, hactiveElem, config,
      storageTypeAt?, contract, storageDecls, EvalResult.bind, bind, pure]
    change (EvalResult.ok
        (({ base := "active", steps := [] } : EvaledStorageRef), uint256St.dynamicArray) :
        EvalResult (EvaledStorageRef × StorageType)) =
      EvalResult.ok (({ base := "active", steps := [] } : EvaledStorageRef),
        uint256St.dynamicArray)
    rfl
  have hlenLoad :
      storageLocLoad evm (wordLoc ⟨11⟩) = .int 0 := by
    simpa [hlen] using clipperStorageLocLoad_uint256 evm ⟨11⟩
  have hlenLoc :
      (config v).storage.layout ({ base := "active", steps := [.length] } :
        EvaledStorageRef) evm = some (wordLoc ⟨11⟩) := by
    rfl
  unfold popArray?
  rw [hresolve]
  simp [EvalResult.bind, bind]
  rw [hlenLoc]
  simp only [EvalResult.ofOption]
  rw [hlenLoad]
  simp

set_option maxHeartbeats 1000000 in
theorem clipperYankRemoveIdNeMoveSource (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    {acc : Account} (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      clipperYankArgWord I ≠
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)))
    (hidxBound :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesPosSlot I)).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let move :=
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankActiveSlot lastIndex)
    let idx := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesPosSlot I)
    let evmIndex := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (clipperYankActiveSlot idx) move
    let evmMovePos := Solm.EVM.storageStore evmIndex evmIndex.executionEnv.codeOwner
      (clipperYankSalesMovePosSlot move) idx
    let popLastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ →
    ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I } evm removeFunction.body
      (.returned { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        (clipperYankDeleteSaleState (clipperYankRemovePopState evmMovePos popLastIndex) I)
        none) := by
  intro lastIndex move idx evmIndex evmMovePos popLastIndex hlenAfter
  have hpos : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    by_contra hnot
    have hzeroNat :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat = 0 := by omega
    exact hlen (uint256_toNat_eq_zero hzeroNat)
  have hlastNat :
      lastIndex.toNat =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat - 1 := by
    unfold lastIndex
    rw [usub_toNat]
    · rw [show (⟨1⟩ : UInt256).toNat = 1 from by native_decide]
    · simpa using hpos
  have hlastBound :
      lastIndex.toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    rw [hlastNat]
    omega
  have hlastStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evm
        (.letDecl "lastIndex" (some uint256)
          (sub256 (.arrayLength .storage activeRef) (.intLit 1)))
        (.ok { contract := contract v, locals := clipperYankRemoveLastIndexStore I lastIndex }
          evm) := by
    exact ExecStmt.letDecl (clipperEvalYankRemoveLastIndex v evm I hlen)
  have hmoveStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveLastIndexStore I lastIndex } evm
        (.letDecl "_move" (some uint256) (.storage (activeElemRef (.var "lastIndex"))))
        (.ok { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          evm) := by
    exact ExecStmt.letDecl (clipperEvalYankRemoveActiveElem v evm I lastIndex hlastBound)
  have hcond :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.binary .ne (.var "id") (.var "_move")) = .ok (.bool true) := by
    exact clipperEvalYankRemoveIdNeMove_true v evm I lastIndex move (by simpa [move] using hne)
  have hindexStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evm) := by
    exact ExecStmt.letDecl
      (by simpa [idx] using clipperEvalYankRemoveSalesPos_moveStore v evm I lastIndex move)
  have hmoveEval :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evm (.var "_move") = .ok (.int (Int.ofNat move.toNat)) :=
    clipperEvalYankRemoveMove_indexStore v evm I lastIndex move idx
  have hassignActive :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evm
        (.assign .storage (activeElemRef (.var "_index")) (.var "_move"))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmIndex) := by
    exact ExecStmt.assign hmoveEval
      (by
        simpa [evmIndex] using
          clipperYankRemoveAssignActive v evm I lastIndex move idx hidxBound)
  have hindexEval :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evmIndex (.var "_index") = .ok (.int (Int.ofNat idx.toNat)) := by
    simpa using clipperEvalYankRemoveIndex_indexStore v evmIndex I lastIndex move idx
  have hassignMovePos :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evmIndex
        (.assign .storage (salesF (.var "_move") "pos") (.var "_index"))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmMovePos) := by
    exact ExecStmt.assign hindexEval
      (by
        simpa [evmMovePos] using
          clipperYankRemoveAssignMovePos v evmIndex I lastIndex move idx)
  have hiteBlock :
      ExecBlock (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        [.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
          .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
          .assign .storage (salesF (.var "_move") "pos") (.var "_index")]
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmMovePos) := by
    exact ExecBlock.consNormal hindexStmt <|
      ExecBlock.consNormal hassignActive <|
        ExecBlock.consNormal hassignMovePos ExecBlock.nil
  have hite :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.ite (.binary .ne (.var "id") (.var "_move"))
          [.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
            .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
            .assign .storage (salesF (.var "_move") "pos") (.var "_index")]
          [])
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmMovePos) := by
    exact ExecStmt.iteTrue hcond hiteBlock
  have hpopArray :
      popArray? (config v)
          { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmMovePos activeRef =
        .ok (clipperYankRemovePopState evmMovePos popLastIndex) := by
    have hraw :=
      clipperYankRemovePopActive v evmMovePos
        (clipperYankRemoveIndexStore I lastIndex move idx)
        (clipperYankRemoveIndexStore_get_active I lastIndex move idx)
        hlenAfter
    simpa [popLastIndex] using hraw
  have hpop :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evmMovePos
        (.pop activeRef)
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          (clipperYankRemovePopState evmMovePos popLastIndex)) := by
    exact ExecStmt.pop hpopArray
  have haccPop :
      ∃ accPop,
        (clipperYankRemovePopState evmMovePos popLastIndex).accountMap.find?
            (clipperYankRemovePopState evmMovePos popLastIndex).executionEnv.codeOwner =
          some accPop := by
    simp [clipperYankRemovePopState, evmMovePos, evmIndex, storageStore_accountMap,
      storageStore_executionEnv, sstoreAccountMap, hacc, Option.option,
      accountMap_find_insert_self]
  obtain ⟨accPop, haccPop⟩ := haccPop
  have hdelete :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        (clipperYankRemovePopState evmMovePos popLastIndex)
        (.delete (saleRef (.var "id")))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          (clipperYankDeleteSaleState (clipperYankRemovePopState evmMovePos popLastIndex) I)) := by
    exact ExecStmt.delete
      (clipperYankDeleteSale v (clipperYankRemovePopState evmMovePos popLastIndex) I
        (clipperYankRemoveIndexStore I lastIndex move idx) haccPop
        (clipperYankRemoveIndexStore_get_sales I lastIndex move idx)
        (clipperYankRemoveIndexStore_get_id I lastIndex move idx))
  apply ExecFuncBody.execBlockOK
  simpa [removeFunction] using
    (ExecBlock.consNormal hlastStmt <|
      ExecBlock.consNormal hmoveStmt <|
        ExecBlock.consNormal hite <|
          ExecBlock.consNormal hpop <|
            ExecBlock.consNormal hdelete ExecBlock.nil)

set_option maxHeartbeats 1000000 in
theorem clipperYankRemoveIdNeMoveIndexOobSourceReverts (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      clipperYankArgWord I ≠
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)))
    (hidxBound :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesPosSlot I)).toNat) :
    ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I } evm removeFunction.body
      .reverted := by
  let lastIndex :=
    UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
  let move :=
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankActiveSlot lastIndex)
  let idx := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesPosSlot I)
  have hpos : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    by_contra hnot
    have hzeroNat :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat = 0 := by omega
    exact hlen (uint256_toNat_eq_zero hzeroNat)
  have hlastNat :
      lastIndex.toNat =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat - 1 := by
    unfold lastIndex
    rw [usub_toNat]
    · rw [show (⟨1⟩ : UInt256).toNat = 1 from by native_decide]
    · simpa using hpos
  have hlastBound :
      lastIndex.toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    rw [hlastNat]
    omega
  have hlastStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evm
        (.letDecl "lastIndex" (some uint256)
          (sub256 (.arrayLength .storage activeRef) (.intLit 1)))
        (.ok { contract := contract v, locals := clipperYankRemoveLastIndexStore I lastIndex }
          evm) := by
    exact ExecStmt.letDecl (clipperEvalYankRemoveLastIndex v evm I hlen)
  have hmoveStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveLastIndexStore I lastIndex } evm
        (.letDecl "_move" (some uint256) (.storage (activeElemRef (.var "lastIndex"))))
        (.ok { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          evm) := by
    exact ExecStmt.letDecl (clipperEvalYankRemoveActiveElem v evm I lastIndex hlastBound)
  have hcond :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.binary .ne (.var "id") (.var "_move")) = .ok (.bool true) := by
    exact clipperEvalYankRemoveIdNeMove_true v evm I lastIndex move (by simpa [move] using hne)
  have hindexStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evm) := by
    exact ExecStmt.letDecl
      (by simpa [idx] using clipperEvalYankRemoveSalesPos_moveStore v evm I lastIndex move)
  have hmoveEval :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evm (.var "_move") = .ok (.int (Int.ofNat move.toNat)) :=
    clipperEvalYankRemoveMove_indexStore v evm I lastIndex move idx
  have hassignActive :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evm
        (.assign .storage (activeElemRef (.var "_index")) (.var "_move"))
        .reverted := by
    exact ExecStmt.assignStoreRevert hmoveEval
      (by
        simpa [idx] using
          clipperYankRemoveAssignActiveRevert v evm I lastIndex move idx hidxBound)
  have hiteBlock :
      ExecBlock (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        [.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
          .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
          .assign .storage (salesF (.var "_move") "pos") (.var "_index")]
        .reverted := by
    exact ExecBlock.consNormal hindexStmt (ExecBlock.consRevert hassignActive)
  have hite :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.ite (.binary .ne (.var "id") (.var "_move"))
          [.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
            .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
            .assign .storage (salesF (.var "_move") "pos") (.var "_index")]
          [])
        .reverted := by
    exact ExecStmt.iteTrue hcond hiteBlock
  apply ExecFuncBody.execBlockRevert
  simpa [removeFunction] using
    (ExecBlock.consNormal hlastStmt <|
      ExecBlock.consNormal hmoveStmt <|
        ExecBlock.consRevert hite)

set_option maxHeartbeats 1000000 in
theorem clipperYankRemoveIdNeMovePopEmptySourceReverts (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      clipperYankArgWord I ≠
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)))
    (hidxBound :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperYankSalesPosSlot I)).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let move :=
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankActiveSlot lastIndex)
    let idx := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesPosSlot I)
    let evmIndex := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (clipperYankActiveSlot idx) move
    let evmMovePos := Solm.EVM.storageStore evmIndex evmIndex.executionEnv.codeOwner
      (clipperYankSalesMovePosSlot move) idx
    Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ →
    ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I } evm removeFunction.body
      .reverted := by
  intro lastIndex move idx evmIndex evmMovePos hlenAfter
  have hpos : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    by_contra hnot
    have hzeroNat :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat = 0 := by omega
    exact hlen (uint256_toNat_eq_zero hzeroNat)
  have hlastNat :
      lastIndex.toNat =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat - 1 := by
    unfold lastIndex
    rw [usub_toNat]
    · rw [show (⟨1⟩ : UInt256).toNat = 1 from by native_decide]
    · simpa using hpos
  have hlastBound :
      lastIndex.toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    rw [hlastNat]
    omega
  have hlastStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evm
        (.letDecl "lastIndex" (some uint256)
          (sub256 (.arrayLength .storage activeRef) (.intLit 1)))
        (.ok { contract := contract v, locals := clipperYankRemoveLastIndexStore I lastIndex }
          evm) := by
    exact ExecStmt.letDecl (clipperEvalYankRemoveLastIndex v evm I hlen)
  have hmoveStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveLastIndexStore I lastIndex } evm
        (.letDecl "_move" (some uint256) (.storage (activeElemRef (.var "lastIndex"))))
        (.ok { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          evm) := by
    exact ExecStmt.letDecl (clipperEvalYankRemoveActiveElem v evm I lastIndex hlastBound)
  have hcond :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.binary .ne (.var "id") (.var "_move")) = .ok (.bool true) := by
    exact clipperEvalYankRemoveIdNeMove_true v evm I lastIndex move (by simpa [move] using hne)
  have hindexStmt :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evm) := by
    exact ExecStmt.letDecl
      (by simpa [idx] using clipperEvalYankRemoveSalesPos_moveStore v evm I lastIndex move)
  have hmoveEval :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evm (.var "_move") = .ok (.int (Int.ofNat move.toNat)) :=
    clipperEvalYankRemoveMove_indexStore v evm I lastIndex move idx
  have hassignActive :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evm
        (.assign .storage (activeElemRef (.var "_index")) (.var "_move"))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmIndex) := by
    exact ExecStmt.assign hmoveEval
      (by
        simpa [evmIndex] using
          clipperYankRemoveAssignActive v evm I lastIndex move idx hidxBound)
  have hindexEval :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evmIndex (.var "_index") = .ok (.int (Int.ofNat idx.toNat)) := by
    simpa using clipperEvalYankRemoveIndex_indexStore v evmIndex I lastIndex move idx
  have hassignMovePos :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evmIndex
        (.assign .storage (salesF (.var "_move") "pos") (.var "_index"))
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmMovePos) := by
    exact ExecStmt.assign hindexEval
      (by
        simpa [evmMovePos] using
          clipperYankRemoveAssignMovePos v evmIndex I lastIndex move idx)
  have hiteBlock :
      ExecBlock (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        [.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
          .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
          .assign .storage (salesF (.var "_move") "pos") (.var "_index")]
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmMovePos) := by
    exact ExecBlock.consNormal hindexStmt <|
      ExecBlock.consNormal hassignActive <|
        ExecBlock.consNormal hassignMovePos ExecBlock.nil
  have hite :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.ite (.binary .ne (.var "id") (.var "_move"))
          [.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
            .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
            .assign .storage (salesF (.var "_move") "pos") (.var "_index")]
          [])
        (.ok { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
          evmMovePos) := by
    exact ExecStmt.iteTrue hcond hiteBlock
  have hpop :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
        evmMovePos
        (.pop activeRef)
        .reverted := by
    exact ExecStmt.popRevert
      (clipperYankRemovePopActiveRevert v evmMovePos
        (clipperYankRemoveIndexStore I lastIndex move idx)
        (clipperYankRemoveIndexStore_get_active I lastIndex move idx)
        hlenAfter)
  apply ExecFuncBody.execBlockRevert
  simpa [removeFunction] using
    (ExecBlock.consNormal hlastStmt <|
      ExecBlock.consNormal hmoveStmt <|
        ExecBlock.consNormal hite <|
          ExecBlock.consRevert hpop)

theorem clipperYankAfterVatRemoveIdEqMoveSourceOk (v : ClipperImmutables)
    (evmVat : EVM.State) (I : ExecutionEnv)
    {acc : Account} (hacc : evmVat.accountMap.find? evmVat.executionEnv.codeOwner = some acc)
    (hlen : Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      clipperYankArgWord I =
        Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let move :=
      Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner
        (clipperYankActiveSlot lastIndex)
    let evmRemove := clipperYankDeleteSaleState (clipperYankRemovePopState evmVat lastIndex) I
    let frameRemoveRet : Frame :=
      { contract := (contract v), locals := (clipperYankFluxRetStore I).insert "_removeRet" .unit }
    ExecBlock (config v)
      { contract := (contract v), locals := clipperYankFluxRetStore I } evmVat
      [.internalCall "_remove" [.var "id"] "_removeRet",
        .assign .storage lockedRef (.intLit 0)]
      (.ok frameRemoveRet
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro lastIndex move evmRemove frameRemoveRet
  have hremoveBody :
      ExecFuncBody (config v)
        { contract := (contract v), locals := clipperYankRemoveStore I } evmVat
        removeFunction.body
        (.returned { contract := (contract v), locals := clipperYankRemoveMoveStore I lastIndex move }
          evmRemove none) := by
    simpa [lastIndex, move, evmRemove] using
      clipperYankRemoveIdEqMoveSource v evmVat I hacc hlen heq
  have hremove :
      ExecStmt (config v)
        { contract := (contract v), locals := clipperYankFluxRetStore I } evmVat
        (.internalCall "_remove" [.var "id"] "_removeRet")
        (.ok frameRemoveRet evmRemove) := by
    simpa [resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := (contract v), locals := clipperYankFluxRetStore I })
        (evm := evmVat)
        (name := "_remove") (retVar := "_removeRet")
        (args := [.var "id"])
        (argVals := [clipperYankArgValue I])
        (callee := removeFunction)
        (locals := clipperYankRemoveStore I)
        (calleeSolm :=
          { contract := (contract v), locals := clipperYankRemoveMoveStore I lastIndex move })
        (calleeEvm := evmRemove)
        (value := none)
        (clipperYankFluxRetStore_removeArgs I v evmVat)
        (clipperYankRemoveLookup v)
        (clipperYankRemoveBind I)
        hremoveBody)
  have hzero :
      evalExpr? (config v)
        frameRemoveRet evmRemove
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, frameRemoveRet]
  have hassign :
      assignStorageRef? (config v)
        frameRemoveRet evmRemove
        .storage lockedRef (.int 0) =
        .ok (frameRemoveRet,
          Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [frameRemoveRet] using
      assign_clipperLocked v evmRemove
        ((clipperYankFluxRetStore I).insert "_removeRet" .unit)
        (clipperYankFluxRetStore_removeRet_locked I) ⟨0⟩
  have hunlock :
      ExecStmt (config v)
        frameRemoveRet evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecStmt.assign hzero hassign
  exact ExecBlock.consNormal hremove (ExecBlock.consNormal hunlock ExecBlock.nil)

set_option linter.unusedVariables false in
theorem clipperYankAfterVatRemoveIdNeMoveSourceOk (v : ClipperImmutables)
    (evmVat : EVM.State) (I : ExecutionEnv)
    {acc : Account} (hacc : evmVat.accountMap.find? evmVat.executionEnv.codeOwner = some acc)
    (hlen : Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      clipperYankArgWord I ≠
        Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)))
    (hidxBound :
      (Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner
        (clipperYankSalesPosSlot I)).toNat <
        (Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩).toNat) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let move :=
      Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner
        (clipperYankActiveSlot lastIndex)
    let idx :=
      Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner (clipperYankSalesPosSlot I)
    let evmIndex := Solm.EVM.storageStore evmVat evmVat.executionEnv.codeOwner
      (clipperYankActiveSlot idx) move
    let evmMovePos := Solm.EVM.storageStore evmIndex evmIndex.executionEnv.codeOwner
      (clipperYankSalesMovePosSlot move) idx
    let popLastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ →
    let evmRemove :=
      clipperYankDeleteSaleState (clipperYankRemovePopState evmMovePos popLastIndex) I
    let frameRemoveRet : Frame :=
      { contract := (contract v), locals := (clipperYankFluxRetStore I).insert "_removeRet" .unit }
    ExecBlock (config v)
      { contract := (contract v), locals := clipperYankFluxRetStore I } evmVat
      [.internalCall "_remove" [.var "id"] "_removeRet",
        .assign .storage lockedRef (.intLit 0)]
      (.ok frameRemoveRet
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro lastIndex move idx evmIndex evmMovePos popLastIndex hlenAfter evmRemove frameRemoveRet
  let calleeFrame : Frame :=
    { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx }
  have hremoveBody :
      ExecFuncBody (config v)
        { contract := (contract v), locals := clipperYankRemoveStore I } evmVat
        removeFunction.body
        (.returned calleeFrame evmRemove none) := by
    simpa [lastIndex, move, idx, evmIndex, evmMovePos, popLastIndex, evmRemove] using
      clipperYankRemoveIdNeMoveSource v evmVat I hacc hlen hne hidxBound hlenAfter
  have hremove :
      ExecStmt (config v)
        { contract := (contract v), locals := clipperYankFluxRetStore I } evmVat
        (.internalCall "_remove" [.var "id"] "_removeRet")
        (.ok frameRemoveRet evmRemove) := by
    simpa [resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := (contract v), locals := clipperYankFluxRetStore I })
        (evm := evmVat)
        (name := "_remove") (retVar := "_removeRet")
        (args := [.var "id"])
        (argVals := [clipperYankArgValue I])
        (callee := removeFunction)
        (locals := clipperYankRemoveStore I)
        (calleeSolm := calleeFrame)
        (calleeEvm := evmRemove)
        (value := none)
        (clipperYankFluxRetStore_removeArgs I v evmVat)
        (clipperYankRemoveLookup v)
        (clipperYankRemoveBind I)
        hremoveBody)
  have hzero :
      evalExpr? (config v)
        frameRemoveRet evmRemove
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, frameRemoveRet]
  have hassign :
      assignStorageRef? (config v)
        frameRemoveRet evmRemove
        .storage lockedRef (.int 0) =
        .ok (frameRemoveRet,
          Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [frameRemoveRet] using
      assign_clipperLocked v evmRemove
        ((clipperYankFluxRetStore I).insert "_removeRet" .unit)
        (clipperYankFluxRetStore_removeRet_locked I) ⟨0⟩
  have hunlock :
      ExecStmt (config v)
        frameRemoveRet evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecStmt.assign hzero hassign
  exact ExecBlock.consNormal hremove (ExecBlock.consNormal hunlock ExecBlock.nil)

theorem clipperYankAfterVatSourceBlock {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDog evmVat : EVM.State} {outDog outVat : ByteArray} {result : ExecResult}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (husr :
      clipperYankSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hdogCode :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩).lookupAccount
            (AccountAddress.ofUInt256
              (clipperYankDogTarget (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I))).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v)
        (Solm.EVM.storageStore
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩)
        (EVM.address (AccountAddress.ofUInt256
          (clipperYankDogTarget (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I)))
        "digs" 0
        [v.ilk,
          .int (Int.ofNat
            (clipperYankSalesTabWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I).toNat)]
        (true, evmDog, outDog) true)
    (hvatCode :
      0 < (UInt256.ofNat ((evmDog.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner, .address evmDog.executionEnv.source,
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
              (clipperYankSalesLotSlot I)).toNat)]
        (true, evmVat, outVat) true)
    (hafter :
      ExecBlock (config v) { contract := contract v, locals := clipperYankFluxRetStore I } evmVat
        [.internalCall "_remove" [.var "id"] "_removeRet",
          .assign .storage lockedRef (.intLit 0)]
        result) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock (config v) { contract := contract v, locals := locals } evm0
      (yankTransition v).body result := by
  intro locals evm0
  let evmLock := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperAuth_true v evm0 I locals (by simp [evm0, initState])
        (by simp [locals]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool true) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperLocked_zero_true v evm0 locals
        (by simp [locals]) hlocked
  have hlockRhs :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.intLit 1) =
        .ok (.int 1) := by
    simp [evalExpr?, pure]
  have hlockAssign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage lockedRef (.int 1) =
          .ok ({ contract := contract v, locals := locals }, evmLock) := by
    simpa [locals, evmLock] using assign_clipperLocked v evm0 locals
      (by simp [locals]) ⟨1⟩
  have husrLoad :
      UInt256.land
        (Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner
          (clipperYankSalesUsrSlot I)) solcAddrMask ≠ ⟨0⟩ := by
    simpa [evmLock, evm0, initState, clipperYankSalesUsrWord, solcSlotWord,
      storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
      State.lookupAccount] using husr
  have husrEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .ne (.storage (salesF (.var "id") "usr")) zeroAddr) = .ok (.bool true) := by
    simpa [locals] using clipperEvalYankSalesUsrNeZero_true v evmLock I husrLoad
  have hdogEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) = .ok (.bool true) := by
    exact clipperEvalYankDogCodeGuard_true v evmLock locals (by simp [locals])
      (by
        simpa [evmLock, evm0, initState, storageStore_accountMap,
          storageStore_executionEnv, State.lookupAccount] using hdogCode)
  have hdogArgs :
      evalExprs? (config v) { contract := contract v, locals := locals } evmLock
          [ilkExpr v, .storage (salesF (.var "id") "tab")] =
        .ok
          [v.ilk,
            .int (Int.ofNat
              (clipperYankSalesTabWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I).toNat)] := by
    have htabLoad :
        Solm.EVM.storageLoad evmLock evmLock.executionEnv.codeOwner
            (clipperYankSalesTabSlot I) =
          clipperYankSalesTabWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I := by
      simp [evmLock, evm0, initState, clipperYankSalesTabWord, solcSlotWord,
        storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
        State.lookupAccount]
      cases (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩).find? I.codeOwner <;> rfl
    simpa [locals, htabLoad] using clipperEvalYankDogDigsArgs v evmLock I
  have hcallDog' :
      typedCallViaEVM (config v) evmLock
        (EVM.address (AccountAddress.ofUInt256
          (clipperYankDogTarget evmLock.accountMap evmLock.executionEnv)))
        "digs" 0
        [v.ilk,
          .int (Int.ofNat
            (clipperYankSalesTabWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I).toNat)]
        (true, evmDog, outDog) true := by
    simpa [evmLock, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv] using hcallDog
  have hvatEval :
      evalExpr? (config v)
        { contract := contract v, locals := clipperYankDogRetStore I } evmDog
        (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool true) := by
    exact clipperEvalYankVatCodeGuard_true v evmDog (clipperYankDogRetStore I)
      hvatCode
  have hvatArgs :
      evalExprs? (config v)
        { contract := contract v, locals := clipperYankDogRetStore I } evmDog
        [ilkExpr v, thisAddr, sender, .storage (salesF (.var "id") "lot")] =
      .ok
        [v.ilk, .address evmDog.executionEnv.codeOwner, .address evmDog.executionEnv.source,
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
              (clipperYankSalesLotSlot I)).toNat)] :=
    clipperEvalYankVatFluxArgsAfterDog v evmDog I
  simpa [yankTransition, nonpayable, auth, lockPrefix, checkedExternalCallStmts,
    List.cons_append, List.nil_append, clipperYankDogRetStore, clipperYankFluxRetStore] using
    (by
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
      refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
      refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue hdogEval) ?_
      refine ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalYankDogTarget v evmLock locals (by simp [locals]))
          (by simp [evalExpr?, pure]) hdogArgs hcallDog'
          (clipperYankDecodeDigsVoid v outDog)) ?_
      refine ExecBlock.consNormal (ExecStmt.requireTrue hvatEval) ?_
      refine ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (clipperEvalVat v evmDog (clipperYankDogRetStore I))
          (by simp [evalExpr?, pure]) hvatArgs hcallVat
          (clipperYankDecodeFluxVoid v outVat)) ?_
      exact hafter)

theorem clipperYankAfterVatSourceOk {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDog evmVat : EVM.State} {outDog outVat : ByteArray} {frame : Frame}
    {evmFinal : EVM.State}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (husr :
      clipperYankSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hdogCode :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩).lookupAccount
            (AccountAddress.ofUInt256
              (clipperYankDogTarget (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I))).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v)
        (Solm.EVM.storageStore
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩)
        (EVM.address (AccountAddress.ofUInt256
          (clipperYankDogTarget (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I)))
        "digs" 0
        [v.ilk,
          .int (Int.ofNat
            (clipperYankSalesTabWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I).toNat)]
        (true, evmDog, outDog) true)
    (hvatCode :
      0 < (UInt256.ofNat ((evmDog.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner, .address evmDog.executionEnv.source,
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
              (clipperYankSalesLotSlot I)).toNat)]
        (true, evmVat, outVat) true)
    (hafter :
      ExecBlock (config v) { contract := contract v, locals := clipperYankFluxRetStore I } evmVat
        [.internalCall "_remove" [.var "id"] "_removeRet",
          .assign .storage lockedRef (.intLit 0)]
        (.ok frame evmFinal)) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body
      (.returned frame evmFinal none) := by
  intro locals evm0
  have hblock :=
    clipperYankAfterVatSourceBlock
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evmDog := evmDog) (evmVat := evmVat)
      (outDog := outDog) (outVat := outVat) (result := .ok frame evmFinal)
      v hwv hauth hlocked husr hdogCode hcallDog hvatCode hcallVat hafter
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockOK
    (by simpa [locals, evm0] using hblock)

theorem clipperYankAfterVatSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDog evmVat : EVM.State} {outDog outVat : ByteArray}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (husr :
      clipperYankSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hdogCode :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩).lookupAccount
            (AccountAddress.ofUInt256
              (clipperYankDogTarget (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I))).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallDog :
      typedCallViaEVM (config v)
        (Solm.EVM.storageStore
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨13⟩ ⟨1⟩)
        (EVM.address (AccountAddress.ofUInt256
          (clipperYankDogTarget (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I)))
        "digs" 0
        [v.ilk,
          .int (Int.ofNat
            (clipperYankSalesTabWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I).toNat)]
        (true, evmDog, outDog) true)
    (hvatCode :
      0 < (UInt256.ofNat ((evmDog.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallVat :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner, .address evmDog.executionEnv.source,
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmDog evmDog.executionEnv.codeOwner
              (clipperYankSalesLotSlot I)).toNat)]
        (true, evmVat, outVat) true)
    (hafter :
      ExecBlock (config v) { contract := contract v, locals := clipperYankFluxRetStore I } evmVat
        [.internalCall "_remove" [.var "id"] "_removeRet",
          .assign .storage lockedRef (.intLit 0)]
        .reverted) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body
      .reverted := by
  intro locals evm0
  have hblock :=
    clipperYankAfterVatSourceBlock
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evmDog := evmDog) (evmVat := evmVat)
      (outDog := outDog) (outVat := outVat) (result := .reverted)
      v hwv hauth hlocked husr hdogCode hcallDog hvatCode hcallVat hafter
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert
    (by simpa [locals, evm0] using hblock)

end Benchmarks.Dss.Clipper
