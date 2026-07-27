import Benchmarks.Dss.Clipper.Guards
import Benchmarks.Dss.Clipper.Dog
import Benchmarks.Dss.Clipper.Vat
import Benchmarks.Dss.Clipper.Count
import Benchmarks.Dss.Clipper.YankBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperYankStore_get_wards (I : ExecutionEnv) :
    (clipperYankStore I).get? "wards" = none := by
  unfold clipperYankStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem clipperYankStore_get_locked (I : ExecutionEnv) :
    (clipperYankStore I).get? "locked" = none := by
  unfold clipperYankStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

abbrev clipperYankDogRetStore (I : ExecutionEnv) : Store :=
  (clipperYankStore I).insert "_digsRet" .unit

abbrev clipperYankFluxRetStore (I : ExecutionEnv) : Store :=
  (clipperYankDogRetStore I).insert "_fluxRet" .unit

abbrev clipperYankRemoveStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (clipperYankArgValue I)

abbrev clipperYankRemoveLastIndexStore (I : ExecutionEnv) (lastIndex : UInt256) : Store :=
  (clipperYankRemoveStore I).insert "lastIndex" (.int (Int.ofNat lastIndex.toNat))

theorem clipperYankRemoveLookup (v : ClipperImmutables) :
    lookupCallable? (contract v) "_remove" = some removeFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    removeFunction, minFunction, addFunction, subFunction, mulFunction, wmulFunction,
    rmulFunction, rdivFunction, statusFunction, getFeedPriceFunction]

theorem clipperYankRemoveBind (I : ExecutionEnv) :
    bindParams? removeFunction.params [clipperYankArgValue I] =
      some (clipperYankRemoveStore I) := by
  simp [removeFunction, bindParams?, clipperYankRemoveStore]

theorem clipperYankRemoveEmptySourceReverts (v : ClipperImmutables)
    (evm : EVM.State) (I : ExecutionEnv)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I } evm removeFunction.body
      .reverted := by
  have hlenEval :=
    clipperEvalActiveLength v evm (clipperYankRemoveStore I)
      (by simp [clipperYankRemoveStore])
  have hlast :
      evalExpr? (config v) { contract := contract v, locals := clipperYankRemoveStore I } evm
        (sub256 (.arrayLength .storage activeRef) (.intLit 1)) = .revert := by
    simp [sub256, u256, evalExpr?, hlenEval, hlen, evalBinaryOp?, bind, EvalResult.bind,
      uint256Int]
  unfold removeFunction
  exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.letDeclRevert hlast))

theorem clipperEvalYankRemoveSalesPos (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveStore I } evm
      (.storage (salesF (.var "id") "pos")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankSalesPosSlot I)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperYankRemoveStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "pos") (er := clipperYankSalesPosRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperYankSalesPosSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperYankSalesPosSlot I)).toNat))
    (by simp [frame, salesF, clipperYankRemoveStore])
    (by
      simp [frame, clipperYankSalesPosRef, clipperYankArgValue, clipperYankArgKey,
        clipperYankRemoveStore, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperYankArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperYankSalesPosSlot, clipperYankSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperYankSalesPosSlot I))

theorem clipperEvalYankRemoveLastIndex (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperYankRemoveStore I } evm
        (sub256 (.arrayLength .storage activeRef) (.intLit 1)) =
      .ok (.int (Int.ofNat
        (UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩).toNat)) := by
  have hlenEval :=
    clipperEvalActiveLength v evm (clipperYankRemoveStore I)
      (by simp [clipperYankRemoveStore])
  have hpos : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    by_contra hnot
    have hzeroNat :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat = 0 := by omega
    exact hlen (uint256_toNat_eq_zero hzeroNat)
  have hsubNat :
      (UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩).toNat =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat - 1 := by
    rw [usub_toNat]
    · rw [show (⟨1⟩ : UInt256).toNat = 1 from by native_decide]
    · simpa using hpos
  have hnotCast :
      ¬ ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat = 0 ∨
        UInt256.size <
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) := by
    intro hbad
    rcases hbad with hbad | hbad
    · omega
    · exact Nat.not_lt_of_ge
        (Nat.le_of_lt (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).val.isLt)
        hbad
  have hint :
      (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat - 1) =
        Int.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat - 1) := by
    exact (Nat.cast_sub (R := Int)
      (show 1 ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat
        from hpos)).symm
  simp [sub256, u256, evalExpr?, hlenEval, evalBinaryOp?, EvalResult.bind, bind,
    uint256Int, hsubNat]
  rw [if_neg (by simpa [UInt256.size] using hnotCast)]
  simpa [pure, hint]

theorem clipperEvalYankRemoveActiveElem (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (idx : UInt256)
    (hbound :
      idx.toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveLastIndexStore I idx } evm
      (.storage (activeElemRef (.var "lastIndex"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankActiveSlot idx)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperYankRemoveLastIndexStore I idx }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := activeElemRef (.var "lastIndex"))
    (er := ({ base := "active", steps := [.aindex (.int (Int.ofNat idx.toNat))] } :
      EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc (clipperYankActiveSlot idx))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperYankActiveSlot idx)).toNat))
    (by simp [frame, clipperYankRemoveLastIndexStore, clipperYankRemoveStore, activeElemRef])
    (by
      simp [frame, clipperYankRemoveLastIndexStore, clipperYankRemoveStore, activeElemRef,
        evalStorageRef, evalStorageRefStep, evalExpr?, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, config, storageLayout,
        solidityStorageLayout, storageLayoutRaw, storageTypeAt?, contract, storageDecls,
        clipperStorageLocLoad_uint256, hbound])
    (by simp [frame, storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperYankActiveSlot idx))

abbrev clipperYankRemoveMoveStore (I : ExecutionEnv) (lastIndex move : UInt256) : Store :=
  (clipperYankRemoveLastIndexStore I lastIndex).insert "_move" (.int (Int.ofNat move.toNat))

theorem clipperYankRemoveMoveStore_get_id (I : ExecutionEnv) (lastIndex move : UInt256) :
    (clipperYankRemoveMoveStore I lastIndex move).get? "id" =
      some (clipperYankArgValue I) := by
  unfold clipperYankRemoveMoveStore clipperYankRemoveLastIndexStore clipperYankRemoveStore
  rw [store_get_ne]
  · rw [store_get_ne]
    · rw [store_get_self]
    · native_decide
  · native_decide

theorem clipperYankRemoveMoveStore_get_move (I : ExecutionEnv) (lastIndex move : UInt256) :
    (clipperYankRemoveMoveStore I lastIndex move).get? "_move" =
      some (.int (Int.ofNat move.toNat)) := by
  unfold clipperYankRemoveMoveStore
  rw [store_get_self]

theorem clipperYankRemoveMoveStore_get_active (I : ExecutionEnv)
    (lastIndex move : UInt256) :
    (clipperYankRemoveMoveStore I lastIndex move).get? "active" = none := by
  unfold clipperYankRemoveMoveStore clipperYankRemoveLastIndexStore clipperYankRemoveStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem clipperYankRemoveMoveStore_get_sales (I : ExecutionEnv)
    (lastIndex move : UInt256) :
    (clipperYankRemoveMoveStore I lastIndex move).get? "sales" = none := by
  unfold clipperYankRemoveMoveStore clipperYankRemoveLastIndexStore clipperYankRemoveStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem clipperEvalYankRemoveId (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex move : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
      (.var "id") = .ok (clipperYankArgValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((clipperYankRemoveMoveStore I lastIndex move).get? "id") = _
  rw [clipperYankRemoveMoveStore_get_id]
  rfl

theorem clipperEvalYankRemoveMove (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex move : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
      (.var "_move") = .ok (.int (Int.ofNat move.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((clipperYankRemoveMoveStore I lastIndex move).get? "_move") = _
  rw [clipperYankRemoveMoveStore_get_move]
  rfl

theorem clipperEvalYankRemoveIdNeMove_true (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex move : UInt256)
    (hne : clipperYankArgWord I ≠ move) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
      (.binary .ne (.var "id") (.var "_move")) = .ok (.bool true) := by
  have hnatNe : ¬ (clipperYankArgWord I).toNat = move.toNat := by
    intro hnat
    apply hne
    apply u256_inj
    exact hnat
  rw [evalExpr?]
  rw [clipperEvalYankRemoveId, clipperEvalYankRemoveMove]
  simp only [bind, EvalResult.bind]
  change evalBinaryOp? .ne (clipperYankArgValue I) (.int (Int.ofNat move.toNat)) =
    .ok (.bool true)
  unfold evalBinaryOp?
  simp [clipperYankArgValue, hnatNe]
  all_goals intro h; cases h

theorem clipperEvalYankRemoveIdNeMove_false (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex move : UInt256)
    (heq : clipperYankArgWord I = move) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
      (.binary .ne (.var "id") (.var "_move")) = .ok (.bool false) := by
  have hnat : (clipperYankArgWord I).toNat = move.toNat := by rw [heq]
  rw [evalExpr?]
  rw [clipperEvalYankRemoveId, clipperEvalYankRemoveMove]
  simp only [bind, EvalResult.bind]
  change evalBinaryOp? .ne (clipperYankArgValue I) (.int (Int.ofNat move.toNat)) =
    .ok (.bool false)
  unfold evalBinaryOp?
  simp [clipperYankArgValue, hnat]
  all_goals intro h; cases h

abbrev clipperYankRemoveIndexStore (I : ExecutionEnv) (lastIndex move idx : UInt256) : Store :=
  (clipperYankRemoveMoveStore I lastIndex move).insert "_index" (.int (Int.ofNat idx.toNat))

theorem clipperYankRemoveAssignActive (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex move idx : UInt256)
    (hbound : idx.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) :
    assignStorageRef? (config v)
      { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx } evm
      .storage (activeElemRef (.var "_index")) (.int (Int.ofNat move.toNat)) =
      .ok ({ contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperYankActiveSlot idx) move) := by
  apply assignStorageRef_storage_scalar
    (er := ({ base := "active", steps := [.aindex (.int (Int.ofNat idx.toNat))] } :
      EvaledStorageRef))
    (ty := uint256St) (loc := wordLoc (clipperYankActiveSlot idx))
  · simp [clipperYankRemoveIndexStore, clipperYankRemoveMoveStore,
      clipperYankRemoveLastIndexStore, clipperYankRemoveStore, activeElemRef]
  · simp [clipperYankRemoveIndexStore, clipperYankRemoveMoveStore,
      clipperYankRemoveLastIndexStore, clipperYankRemoveStore, activeElemRef, evalStorageRef,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind,
      pure, config, storageLayout, solidityStorageLayout, storageLayoutRaw, storageTypeAt?,
      contract, storageDecls, clipperStorageLocLoad_uint256, hbound]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rfl
  · simpa [wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperYankActiveSlot idx) move

theorem clipperYankRemoveAssignMovePos (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (lastIndex move idx : UInt256) :
    assignStorageRef? (config v)
      { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx } evm
      .storage (salesF (.var "_move") "pos") (.int (Int.ofNat idx.toNat)) =
      .ok ({ contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (clipperYankSalesMovePosSlot move) idx) := by
  apply assignStorageRef_storage_scalar
    (er := clipperYankSalesMovePosRef move)
    (ty := uint256St) (loc := wordLoc (clipperYankSalesMovePosSlot move))
  · simp [clipperYankRemoveIndexStore, clipperYankRemoveMoveStore,
      clipperYankRemoveLastIndexStore, clipperYankRemoveStore, salesF]
  · have hmoveEval :
        evalExpr? (config v)
          { contract := contract v, locals := clipperYankRemoveIndexStore I lastIndex move idx } evm
          (.var "_move") = .ok (.int (Int.ofNat move.toNat)) := by
      rw [evalExpr?]
      change EvalResult.ofOption .unboundVariable
        ((clipperYankRemoveIndexStore I lastIndex move idx).get? "_move") = _
      unfold clipperYankRemoveIndexStore clipperYankRemoveMoveStore
        clipperYankRemoveLastIndexStore clipperYankRemoveStore
      rw [store_get_ne _ _ (by native_decide), store_get_self]
      rfl
    simp [salesF, clipperYankSalesMovePosRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, hmoveEval, valueToKey?, EvalResult.bind, EvalResult.ofOption,
      bind, pure]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, SaleStructTy, uint256St]
  · rfl
  · simpa [clipperYankSalesMovePosSlot, clipperYankSalesBaseSlotOfWord, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (clipperYankSalesMovePosSlot move) idx

theorem clipperStorageLocStore_address_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (addrLoc slot) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot solcAddrMask))) := by
  unfold storageLocStore storageLocWriteWord addrLoc
  simp only [valueToWord, bind, Option.bind, pure]
  rw [show EVM.wordOfInt 0 = (⟨0⟩ : UInt256) by native_decide]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.lnot solcAddrMask)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show (⟨0⟩ : UInt256).toNat % 256 ^ 20 = 0 by native_decide]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 20).length =
      20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = (2 : Nat) ^ 160 by norm_num]
  rw [show 256 ^ 20 = (2 : Nat) ^ 160 by norm_num]
  rw [addressOffset0High160Mask_toNat]
  ring

theorem clipperStorageLocStore_uint96_offset20_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (uint96Loc slot ⟨20, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask)) := by
  unfold storageLocStore storageLocWriteWord uint96Loc
  simp only [valueToWord, bind, Option.bind, pure]
  rw [show EVM.wordOfInt 0 = (⟨0⟩ : UInt256) by native_decide]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (20 : Fin 32).val _ ++ List.take (12 : Fin 33).val _
        ++ List.drop ((20 : Fin 32).val + (12 : Fin 33).val) _) =
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        solcAddrMask).toNat
  rw [show (20 : Fin 32).val = 20 from rfl, show (12 : Fin 33).val = 12 from rfl]
  rw [show 20 + 12 = 32 by norm_num, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask, fromBytes'_take_wordLE]
  rw [show (⟨0⟩ : UInt256).toNat % 256 ^ 12 = 0 by native_decide]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20).length =
      20 := by
    rw [List.length_take, hslen]
    norm_num
  rw [hlen20]
  ring

theorem clipperYankPackedClearZero (w : UInt256) :
    UInt256.land (UInt256.land w (UInt256.lnot solcAddrMask)) solcAddrMask = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat, addressOffset0High160Mask_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by native_decide]
  rw [nat_land_mask_eq_mod]
  rw [Nat.mul_comm]
  rw [Nat.mul_mod_right]
  rfl

abbrev clipperYankDeleteSaleState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  let base := clipperYankSalesBaseSlot I
  let evm0 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner base ⟨0⟩
  let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (base + ⟨1⟩) ⟨0⟩
  let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner (base + ⟨2⟩) ⟨0⟩
  let evmUsr := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩)
    (UInt256.land (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩))
      (UInt256.lnot solcAddrMask))
  let evm3 := Solm.EVM.storageStore evmUsr evmUsr.executionEnv.codeOwner (base + ⟨3⟩) ⟨0⟩
  Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner (base + ⟨4⟩) ⟨0⟩

theorem clipperYankDeleteSale (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (locals : Store)
    {acc : Account} (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hgetSales : locals.get? "sales" = none)
    (hgetId : locals.get? "id" = some (clipperYankArgValue I)) :
    deleteStorage? (config v) { contract := contract v, locals := locals } evm
        (saleRef (.var "id")) =
      .ok (clipperYankDeleteSaleState evm I) := by
  have hid :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "id") =
        .ok (clipperYankArgValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption .unboundVariable (locals.get? "id") = _
    rw [hgetId]
    rfl
  have hsalesElem : locals["sales"]? = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetSales
  have hresolve :
      resolveStorageRef? (config v) { contract := contract v, locals := locals } evm
          (saleRef (.var "id")) =
        .ok (clipperYankSalesDeleteRef I, SaleStructTy) := by
    have her :
        evalStorageRef (config v) { contract := contract v, locals := locals } evm
            (saleRef (.var "id")) =
          .ok (clipperYankSalesDeleteRef I) := by
      simp [saleRef, clipperYankSalesDeleteRef, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, hid, valueToKey?, EvalResult.bind, EvalResult.ofOption,
        bind, pure, clipperYankArgValue, clipperYankArgKey]
    unfold resolveStorageRef?
    rw [show (saleRef (.var "id")).base = "sales" by rfl]
    rw [show ({ contract := contract v, locals := locals } : Frame).locals.get? "sales" = none by
      simpa [Std.HashMap.get?_eq_getElem?] using hsalesElem]
    rw [her]
    simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, SaleStructTy,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
  have hclear :
      clearStorage? (config v) evm (clipperYankSalesDeleteRef I) SaleStructTy =
        .ok (clipperYankDeleteSaleState evm I) := by
    let base := clipperYankSalesBaseSlot I
    let evm0 := Solm.EVM.storageStore evm evm.executionEnv.codeOwner base ⟨0⟩
    let evm1 := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner (base + ⟨1⟩) ⟨0⟩
    let evm2 := Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner (base + ⟨2⟩) ⟨0⟩
    let evmUsr := Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩)
      (UInt256.land (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩))
        (UInt256.lnot solcAddrMask))
    let evm3 := Solm.EVM.storageStore evmUsr evmUsr.executionEnv.codeOwner (base + ⟨3⟩) ⟨0⟩
    have hacc2 : ∃ acc2, evm2.accountMap.find? evm2.executionEnv.codeOwner = some acc2 := by
      simp [evm2, evm1, evm0, storageStore_accountMap, storageStore_executionEnv,
        sstoreAccountMap, hacc, Option.option, accountMap_find_insert_self]
    have hpos :
        storageLocStore evm (wordLoc base) (.int 0) = some evm0 := by
      simpa [evm0, wordLoc, uint256Loc] using storageLocStore_uint256 evm base ⟨0⟩
    have htab :
        storageLocStore evm0 (wordLoc (base + ⟨1⟩)) (.int 0) = some evm1 := by
      simpa [evm1, wordLoc, uint256Loc] using storageLocStore_uint256 evm0 (base + ⟨1⟩) ⟨0⟩
    have hlot :
        storageLocStore evm1 (wordLoc (base + ⟨2⟩)) (.int 0) = some evm2 := by
      simpa [evm2, wordLoc, uint256Loc] using storageLocStore_uint256 evm1 (base + ⟨2⟩) ⟨0⟩
    have husr :
        storageLocStore evm2 (addrLoc (base + ⟨3⟩)) (.int 0) = some evmUsr := by
      simpa [evmUsr] using clipperStorageLocStore_address_zero evm2 (base + ⟨3⟩)
    have htic :
        storageLocStore evmUsr (uint96Loc (base + ⟨3⟩) ⟨20, by decide⟩ (by decide))
            (.int 0) =
          some evm3 := by
      have hload :
          Solm.EVM.storageLoad evmUsr evmUsr.executionEnv.codeOwner (base + ⟨3⟩) =
            UInt256.land (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩))
              (UInt256.lnot solcAddrMask) := by
        obtain ⟨acc2, hacc2'⟩ := hacc2
        simpa [evmUsr, storageStore_executionEnv] using
          storageLoad_storageStore_same_present evm2 evm2.executionEnv.codeOwner hacc2'
            (base + ⟨3⟩)
            (UInt256.land
              (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner (base + ⟨3⟩))
              (UInt256.lnot solcAddrMask))
      rw [clipperStorageLocStore_uint96_offset20_zero]
      rw [hload, clipperYankPackedClearZero]
    have htop :
        storageLocStore evm3 (wordLoc (base + ⟨4⟩)) (.int 0) =
          some (Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner (base + ⟨4⟩) ⟨0⟩) := by
      simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm3 (base + ⟨4⟩) ⟨0⟩
    have hclearPos :
        clearStorage? (config v) evm
          { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "pos"] }
          uint256St = .ok evm0 := by
      unfold clearStorage?
      simp [uint256St, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        EvalResult.ofOption, base, hpos]
    have hclearTab :
        clearStorage? (config v) evm0
          { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "tab"] }
          uint256St = .ok evm1 := by
      unfold clearStorage?
      simp [uint256St, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        EvalResult.ofOption, base, htab]
    have hclearLot :
        clearStorage? (config v) evm1
          { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "lot"] }
          uint256St = .ok evm2 := by
      unfold clearStorage?
      simp [uint256St, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        EvalResult.ofOption, base, hlot]
    have hclearUsr :
        clearStorage? (config v) evm2
          { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "usr"] }
          addrSt = .ok evmUsr := by
      unfold clearStorage?
      simp [addrSt, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        EvalResult.ofOption, base, husr]
    have hclearTic :
        clearStorage? (config v) evmUsr
          { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "tic"] }
          uint96St = .ok evm3 := by
      have htic' := htic
      simp at htic'
      unfold clearStorage?
      simp [uint96St, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        EvalResult.ofOption]
      rw [htic']
    have hclearTop :
        clearStorage? (config v) evm3
          { base := "sales", steps := [.mindex (clipperYankArgKey I), .field "top"] }
          uint256St =
            .ok (Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner (base + ⟨4⟩) ⟨0⟩) := by
      unfold clearStorage?
      simp [uint256St, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        EvalResult.ofOption, base, clipperYankSalesBaseSlot, htop]
    simp [clearStorage?, clearFields?, SaleStructTy, clipperYankSalesDeleteRef,
      hclearPos, hclearTab, hclearLot, hclearUsr, hclearTic, hclearTop]
    simp [clipperYankDeleteSaleState, base, evm0, evm1, evm2, evmUsr, evm3,
      storageStore_executionEnv]
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

abbrev clipperYankRemovePopState (evm : EVM.State) (lastIndex : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperYankActiveSlot lastIndex) ⟨0⟩)
    evm.executionEnv.codeOwner ⟨11⟩ lastIndex

theorem clipperYankRemovePopActive (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hactive : locals.get? "active" = none)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    popArray? (config v)
        { contract := contract v, locals := locals }
        evm activeRef =
      .ok (clipperYankRemovePopState evm lastIndex) := by
  intro lastIndex
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
  have hlastInt :
      Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat - 1 =
        Int.ofNat lastIndex.toNat := by
    rw [hlastNat]
    exact (Nat.cast_sub (R := Int)
      (show 1 ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat
        from hpos)).symm
  have hlastIntCast :
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat : Int) - 1 =
        Int.ofNat lastIndex.toNat := by
    simpa using hlastInt
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
      storageLocLoad evm (wordLoc ⟨11⟩) =
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) :=
    clipperStorageLocLoad_uint256 evm ⟨11⟩
  have hlenLoc :
      (config v).storage.layout ({ base := "active", steps := [.length] } :
        EvaledStorageRef) evm = some (wordLoc ⟨11⟩) := by
    rfl
  have hlenNatNe :
      ¬ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat = 0 :=
    Nat.ne_of_gt hpos
  have hclear :
      clearStorage? (config v) evm
          ({ base := "active", steps := [.aindex (.int (Int.ofNat lastIndex.toNat))] } :
            EvaledStorageRef)
          uint256St =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (clipperYankActiveSlot lastIndex) ⟨0⟩) := by
    have hstoreActive :
        storageLocStore evm (wordLoc (activeSlot (.int (lastIndex.toNat : Int)))) (.int 0) =
          some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (activeSlot (.int (lastIndex.toNat : Int))) ⟨0⟩) := by
      simpa [wordLoc, uint256Loc] using
        storageLocStore_uint256 evm (activeSlot (.int (Int.ofNat lastIndex.toNat))) ⟨0⟩
    unfold clearStorage?
    simp [uint256St, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      EvalResult.ofOption, clipperYankActiveSlot]
    rw [hstoreActive]
  let evmClear :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (clipperYankActiveSlot lastIndex) ⟨0⟩
  have hstoreLen :
      storageLocStore evmClear (wordLoc ⟨11⟩) (.int (lastIndex.toNat : Int)) =
        some (Solm.EVM.storageStore evmClear evmClear.executionEnv.codeOwner ⟨11⟩ lastIndex) := by
    simpa using storageLocStore_uint256 evmClear ⟨11⟩ lastIndex
  unfold popArray?
  rw [hresolve]
  simp [EvalResult.bind, bind]
  rw [hlenLoc]
  simp only [EvalResult.ofOption]
  rw [hlenLoad]
  simp
  rw [if_neg hlenNatNe]
  rw [hlastIntCast]
  rw [hclear]
  simp
  rw [hstoreLen]
  simp [clipperYankRemovePopState, evmClear, storageStore_executionEnv]

theorem clipperYankRemoveIdEqMoveSource (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    {acc : Account} (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      clipperYankArgWord I =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let move :=
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankActiveSlot lastIndex)
    ExecFuncBody (config v)
      { contract := contract v, locals := clipperYankRemoveStore I } evm removeFunction.body
      (.returned { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
        (clipperYankDeleteSaleState (clipperYankRemovePopState evm lastIndex) I) none) := by
  intro lastIndex move
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
        (.binary .ne (.var "id") (.var "_move")) = .ok (.bool false) := by
    exact clipperEvalYankRemoveIdNeMove_false v evm I lastIndex move (by simpa [move] using heq)
  have hite :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.ite (.binary .ne (.var "id") (.var "_move"))
          [.letDecl "_index" (some uint256) (.storage (salesF (.var "id") "pos")),
            .assign .storage (activeElemRef (.var "_index")) (.var "_move"),
            .assign .storage (salesF (.var "_move") "pos") (.var "_index")]
          [])
        (.ok { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          evm) := by
    exact ExecStmt.iteFalse hcond ExecBlock.nil
  have hpop :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move } evm
        (.pop activeRef)
        (.ok { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          (clipperYankRemovePopState evm lastIndex)) := by
    exact ExecStmt.pop
      (by
        simpa [lastIndex] using
          clipperYankRemovePopActive v evm (clipperYankRemoveMoveStore I lastIndex move)
            (clipperYankRemoveMoveStore_get_active I lastIndex move) hlen)
  have haccPop :
      ∃ accPop,
        (clipperYankRemovePopState evm lastIndex).accountMap.find?
            (clipperYankRemovePopState evm lastIndex).executionEnv.codeOwner = some accPop := by
    simp [clipperYankRemovePopState, storageStore_accountMap, storageStore_executionEnv,
      sstoreAccountMap, hacc, Option.option, accountMap_find_insert_self]
  obtain ⟨accPop, haccPop⟩ := haccPop
  have hdelete :
      ExecStmt (config v)
        { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
        (clipperYankRemovePopState evm lastIndex)
        (.delete (saleRef (.var "id")))
        (.ok { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          (clipperYankDeleteSaleState (clipperYankRemovePopState evm lastIndex) I)) := by
    exact ExecStmt.delete
      (clipperYankDeleteSale v (clipperYankRemovePopState evm lastIndex) I
        (clipperYankRemoveMoveStore I lastIndex move) haccPop
        (clipperYankRemoveMoveStore_get_sales I lastIndex move)
        (clipperYankRemoveMoveStore_get_id I lastIndex move))
  apply ExecFuncBody.execBlockOK
  simpa [removeFunction] using
    (ExecBlock.consNormal hlastStmt <|
      ExecBlock.consNormal hmoveStmt <|
        ExecBlock.consNormal hite <|
          ExecBlock.consNormal hpop <|
            ExecBlock.consNormal hdelete ExecBlock.nil)

theorem clipperEvalYankSalesUsr (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankStore I } evm
      (.storage (salesF (.var "id") "usr")) =
      .ok (.address (AccountAddress.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankSalesUsrSlot I)) solcAddrMask).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperYankStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "usr") (er := clipperYankSalesUsrRef I)
    (t := .address) (loc := addrLoc (clipperYankSalesUsrSlot I))
    (value := .address (AccountAddress.ofNat (UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperYankSalesUsrSlot I)) solcAddrMask).toNat))
    (by simp [frame, salesF, clipperYankStore])
    (by
      simp [frame, clipperYankSalesUsrRef, clipperYankArgValue, clipperYankArgKey,
        clipperYankStore, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperYankArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, addrSt])
    (by rfl)
    (by simpa [clipperYankSalesUsrSlot, clipperYankSalesBaseSlot] using
      clipperStorageLocLoad_address evm (clipperYankSalesUsrSlot I))

theorem clipperEvalYankSalesUsrNeZero_false (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (husr :
      UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesUsrSlot I))
        solcAddrMask = ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperYankStore I } evm
      (.binary .ne (.storage (salesF (.var "id") "usr")) zeroAddr) = .ok (.bool false) := by
  have hstorage := clipperEvalYankSalesUsr v evm I
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := clipperYankStore I } evm zeroAddr =
        .ok (.address (AccountAddress.ofNat 0)) := by
    simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
      pure, bind]
  simp only [evalExpr?, hstorage, hzero, EvalResult.bind, bind, evalBinaryOp?]
  rw [husr]
  native_decide

theorem clipperYankMaskedAddress_ne_zero {w : UInt256}
    (h : UInt256.land w solcAddrMask ≠ ⟨0⟩) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  have hval : (UInt256.land w solcAddrMask).toNat = 0 := by
    have hlt : (UInt256.land w solcAddrMask).toNat < AccountAddress.size := by
      rw [u256_land_toNat]
      have hland : Nat.land w.toNat solcAddrMask.toNat ≤ solcAddrMask.toNat :=
        Nat.and_le_right
      have hmask : solcAddrMask.toNat < AccountAddress.size := by
        native_decide
      have hlandlt : Nat.land w.toNat solcAddrMask.toNat < UInt256.size := by
        have hsize : AccountAddress.size < UInt256.size := by decide
        omega
      rw [Nat.mod_eq_of_lt hlandlt]
      omega
    apply congrArg Fin.val at haddr
    simpa [AccountAddress.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hlt] using haddr
  exact h (u256_inj (by simpa using hval))

theorem clipperEvalYankSalesUsrNeZero_true (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (husr :
      UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesUsrSlot I))
        solcAddrMask ≠ ⟨0⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperYankStore I } evm
      (.binary .ne (.storage (salesF (.var "id") "usr")) zeroAddr) = .ok (.bool true) := by
  have hstorage := clipperEvalYankSalesUsr v evm I
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := clipperYankStore I } evm zeroAddr =
        .ok (.address (AccountAddress.ofNat 0)) := by
    simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
      pure, bind]
  simp only [evalExpr?, hstorage, hzero, EvalResult.bind, bind, evalBinaryOp?]
  have hne :
      Value.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesUsrSlot I))
            solcAddrMask).toNat) ≠
        Value.address (AccountAddress.ofNat 0) := by
    intro hbad
    rw [Value.address.injEq] at hbad
    exact clipperYankMaskedAddress_ne_zero husr hbad
  have hbeq :
      (Value.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperYankSalesUsrSlot I))
            solcAddrMask).toNat) == Value.address (AccountAddress.ofNat 0)) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  rw [hbeq]
  rfl

theorem clipperEvalYankDogTarget (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "dog" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage dogRef) =
      .ok (.address (AccountAddress.ofUInt256
        (clipperYankDogTarget evm.accountMap evm.executionEnv))) := by
  rw [clipperEvalDog v evm locals hbase]
  simp [clipperYankDogTarget, clipperYankDogWord, solcSlotWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, accountAddress_ofUInt256_eq_ofNat_toNat,
    u256_land_comm]

theorem clipperEvalYankDogCodeGuard_false (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "dog" = none)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperYankDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) =
        .ok (.bool false) := by
  have hnoCode' :
      (EVM.Word.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperYankDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa using hnoCode
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalYankDogTarget v evm locals hbase,
    evalBinaryOp?, hnoCode']

theorem clipperEvalYankDogCodeGuard_true (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (hbase : locals.get? "dog" = none)
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperYankDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) =
        .ok (.bool true) := by
  have hcode' :
      0 < (EVM.Word.ofNat ((evm.lookupAccount
        (AccountAddress.ofUInt256
          (clipperYankDogTarget evm.accountMap evm.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa using hcode
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalYankDogTarget v evm locals hbase,
    evalBinaryOp?, hcode']

theorem clipperEvalYankSalesTab (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankStore I } evm
      (.storage (salesF (.var "id") "tab")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankSalesTabSlot I)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperYankStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "tab") (er := clipperYankSalesTabRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperYankSalesTabSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperYankSalesTabSlot I)).toNat))
    (by simp [frame, salesF, clipperYankStore])
    (by
      simp [frame, clipperYankSalesTabRef, clipperYankArgValue, clipperYankArgKey,
        clipperYankStore, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperYankArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperYankSalesTabSlot, clipperYankSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperYankSalesTabSlot I))

theorem clipperEvalYankSalesLot (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankStore I } evm
      (.storage (salesF (.var "id") "lot")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankSalesLotSlot I)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperYankStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "lot") (er := clipperYankSalesLotRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperYankSalesLotSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperYankSalesLotSlot I)).toNat))
    (by simp [frame, salesF, clipperYankStore])
    (by
      simp [frame, clipperYankSalesLotRef, clipperYankArgValue, clipperYankArgKey,
        clipperYankStore, salesF, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind])
    (by simp [frame, clipperYankArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperYankSalesLotSlot, clipperYankSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperYankSalesLotSlot I))

theorem clipperEvalYankIlkExpr (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (ilkExpr v) =
      .ok v.ilk := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  simp [ilkExpr, hilk, evalExpr?, pure]

theorem clipperEvalYankDogDigsArgs (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? (config v) { contract := contract v, locals := clipperYankStore I } evm
        [ilkExpr v, .storage (salesF (.var "id") "tab")] =
      .ok
        [v.ilk,
          .int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperYankSalesTabSlot I)).toNat)] := by
  simp only [evalExprs?, clipperEvalYankIlkExpr, clipperEvalYankSalesTab,
    EvalResult.bind, bind, pure]

theorem clipperEvalYankVatFluxArgs (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? (config v) { contract := contract v, locals := clipperYankStore I } evm
        [ilkExpr v, thisAddr, sender, .storage (salesF (.var "id") "lot")] =
      .ok
        [v.ilk, .address evm.executionEnv.codeOwner, .address evm.executionEnv.source,
          .int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperYankSalesLotSlot I)).toNat)] := by
  simp only [evalExprs?, clipperEvalYankIlkExpr, clipperEvalYankSalesLot,
    thisAddr, sender, evalExpr?, envValue, EvalResult.bind, bind, pure]

theorem clipperEvalYankSalesLotAfterDog (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperYankDogRetStore I } evm
      (.storage (salesF (.var "id") "lot")) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperYankSalesLotSlot I)).toNat)) := by
  let frame : Frame := { contract := contract v, locals := clipperYankDogRetStore I }
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := frame) (evm := evm)
    (slot := salesF (.var "id") "lot") (er := clipperYankSalesLotRef I)
    (t := .int uint256Int) (loc := wordLoc (clipperYankSalesLotSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (clipperYankSalesLotSlot I)).toNat))
    (by simp [frame, salesF, clipperYankDogRetStore, clipperYankStore])
    (by
      have hgetId :
          (clipperYankDogRetStore I).get? "id" = some (clipperYankArgValue I) := by
        unfold clipperYankDogRetStore
        rw [store_get_ne _ _ (by native_decide)]
        simp [clipperYankStore]
      have hgetIdElem :
          (clipperYankDogRetStore I)["id"]? = some (clipperYankArgValue I) := by
        simpa [Std.HashMap.get?_eq_getElem?] using hgetId
      have hmemId : "id" ∈ clipperYankDogRetStore I := by
        rw [Std.HashMap.mem_iff_isSome_getElem?]
        rw [hgetIdElem]
        rfl
      have hgetIdVal :
          (clipperYankDogRetStore I)["id"] = clipperYankArgValue I := by
        rw [Std.HashMap.getElem_eq_getD (fallback := (.unit : Value)) (h' := hmemId)]
        have hsome := Std.HashMap.getElem?_eq_some_getD
          (m := clipperYankDogRetStore I) (a := "id") (fallback := (.unit : Value)) hmemId
        rw [hgetIdElem] at hsome
        injection hsome with hval
        exact hval.symm
      have hindex :
          evalExpr? (config v) frame evm (.var "id") =
            .ok (clipperYankArgValue I) := by
        unfold evalExpr?
        simp [frame, hgetIdVal, EvalResult.ofOption]
      simp [frame, clipperYankSalesLotRef, clipperYankArgValue, clipperYankArgKey,
        hindex, salesF, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind])
    (by simp [frame, clipperYankArgKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, SaleStructTy, uint256St])
    (by rfl)
    (by simpa [clipperYankSalesLotSlot, clipperYankSalesBaseSlot, wordLoc, uint256Loc] using
      clipperStorageLocLoad_uint256 evm (clipperYankSalesLotSlot I))

theorem clipperEvalYankVatFluxArgsAfterDog (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? (config v) { contract := contract v, locals := clipperYankDogRetStore I } evm
        [ilkExpr v, thisAddr, sender, .storage (salesF (.var "id") "lot")] =
      .ok
        [v.ilk, .address evm.executionEnv.codeOwner, .address evm.executionEnv.source,
          .int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperYankSalesLotSlot I)).toNat)] := by
  simp only [evalExprs?, clipperEvalYankIlkExpr, clipperEvalYankSalesLotAfterDog,
    thisAddr, sender, evalExpr?, envValue, EvalResult.bind, bind, pure]

theorem clipperYankDecodeDigsVoid (v : ClipperImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "digs" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem clipperYankDecodeFluxVoid (v : ClipperImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "flux" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem clipperEvalYankVatCodeGuard_true (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hcode :
      0 <
        (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?, EVM.Word.ofNat,
    hcode]

theorem clipperEvalYankVatCodeGuard_false (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store)
    (hnoCode :
      (UInt256.ofNat ((evm.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, clipperEvalVat, evalBinaryOp?, EVM.Word.ofNat,
    hnoCode]

theorem clipperYankAuthSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
  intro locals evm0
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperAuth_false v evm0 I locals (by simp [evm0, initState])
        (by simp [locals]) hauth
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
    simpa [yankTransition, nonpayable, auth] using
      nonpayableSecondRequireReverts
        (cfg := config v)
        (solm := { contract := contract v, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (by simp [evm0, initState]; exact hwv)
        hauthEval
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperYankInactiveSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (husr :
      clipperYankSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I = ⟨0⟩) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
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
          (clipperYankSalesUsrSlot I)) solcAddrMask = ⟨0⟩ := by
    simpa [evmLock, evm0, initState, clipperYankSalesUsrWord, solcSlotWord,
      storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
      State.lookupAccount] using husr
  have husrEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .ne (.storage (salesF (.var "id") "usr")) zeroAddr) = .ok (.bool false) := by
    simpa [locals] using clipperEvalYankSalesUsrNeZero_false v evmLock I husrLoad
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
    simpa [yankTransition, nonpayable, auth, lockPrefix] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse husrEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperYankLockedSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
  intro locals evm0
  have hauthEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, clipperRelyAuthWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_clipperAuth_true v evm0 I locals (by simp [evm0, initState])
        (by simp [locals]) hauth
  have hlockedEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage lockedRef) (.intLit 0)) = .ok (.bool false) := by
    simpa [locals, evm0, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_clipperLocked_zero_false v evm0 locals
        (by simp [locals]) hlocked
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
    simpa [yankTransition, nonpayable, auth, lockPrefix] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse hlockedEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperYankDogDigsNoCodeSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (v : ClipperImmutables) (hwv : I.weiValue = ⟨0⟩)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (husr :
      clipperYankSalesUsrWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ≠ ⟨0⟩)
    (hcodeSizeDog :
      Reasoning.Theory.uniswapExtCodeSizeWord
        (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩)
        (clipperYankDogTarget (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I) = ⟨0⟩) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
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
  have hnoDogCode :
      (UInt256.ofNat ((evmLock.lookupAccount
        (AccountAddress.ofUInt256
          (clipperYankDogTarget evmLock.accountMap evmLock.executionEnv))).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    have h := congrArg UInt256.toNat hcodeSizeDog
    let σLock := sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩
    let target := clipperYankDogTarget σLock I
    suffices hlookup :
        (UInt256.ofNat
          ((σLock.find? (AccountAddress.ofUInt256 target)).option 0
            (fun acc => acc.code.size))).toNat = 0 by
      simpa [evmLock, evm0, initState, storageStore_accountMap, storageStore_executionEnv,
        State.lookupAccount, σLock, target] using hlookup
    change (Reasoning.Theory.uniswapExtCodeSizeWord σLock target).toNat = 0 at h
    unfold Reasoning.Theory.uniswapExtCodeSizeWord at h
    cases hacc : σLock.find? (AccountAddress.ofUInt256 target) with
    | none =>
        rfl
    | some acc =>
        simpa [hacc] using h
  have hdogEval :
      evalExpr? (config v) { contract := contract v, locals := locals } evmLock
        (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) = .ok (.bool false) := by
    exact clipperEvalYankDogCodeGuard_false v evmLock locals (by simp [locals]) hnoDogCode
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
    simpa [yankTransition, nonpayable, auth, lockPrefix, checkedExternalCallStmts,
      List.cons_append, List.nil_append] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        exact ExecBlock.consRevert (ExecStmt.requireFalse hdogEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperYankDogDigsCallFailureSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {outDog : ByteArray}
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
        (false, evmDog, outDog) true) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
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
        (false, evmDog, outDog) true := by
    simpa [evmLock, evm0, initState, storageStore_accountMap,
      storageStore_executionEnv] using hcallDog
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
    simpa [yankTransition, nonpayable, auth, lockPrefix, checkedExternalCallStmts,
      List.cons_append, List.nil_append] using
      (by
        refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
        · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
        refine ExecBlock.consNormal (ExecStmt.requireTrue hauthEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hlockedEval) ?_
        refine ExecBlock.consNormal (ExecStmt.assign hlockRhs hlockAssign) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue husrEval) ?_
        refine ExecBlock.consNormal (ExecStmt.requireTrue hdogEval) ?_
        exact ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalYankDogTarget v evmLock locals (by simp [locals]))
            (by simp [evalExpr?, pure]) hdogArgs hcallDog'))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperYankVatFluxNoCodeSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {outDog : ByteArray}
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
    (hvatNoCode :
      (UInt256.ofNat ((evmDog.lookupAccount v.vat).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
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
        (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool false) := by
    exact clipperEvalYankVatCodeGuard_false v evmDog (clipperYankDogRetStore I)
      hvatNoCode
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
    simpa [yankTransition, nonpayable, auth, lockPrefix, checkedExternalCallStmts,
      List.cons_append, List.nil_append, clipperYankDogRetStore] using
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
        exact ExecBlock.consRevert (ExecStmt.requireFalse hvatEval))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperYankVatFluxCallFailureSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
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
        (false, evmVat, outVat) true) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
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
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
    simpa [yankTransition, nonpayable, auth, lockPrefix, checkedExternalCallStmts,
      List.cons_append, List.nil_append, clipperYankDogRetStore] using
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
        exact ExecBlock.consRevert
          (ExecStmt.externalCallFailure
            (clipperEvalVat v evmDog (clipperYankDogRetStore I))
            (by simp [evalExpr?, pure]) hvatArgs hcallVat))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem clipperYankRemoveEmptyAfterVatSourceReverts {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (hactiveLen : Solm.EVM.storageLoad evmVat evmVat.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    let locals := clipperYankStore I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (yankTransition v).body .reverted := by
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
  have hremoveArgs :
      evalExprs? (config v) { contract := contract v, locals := clipperYankFluxRetStore I }
        evmVat [.var "id"] = .ok [clipperYankArgValue I] := by
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
  have hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmVat
        removeFunction.body .reverted :=
    clipperYankRemoveEmptySourceReverts v evmVat I hactiveLen
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (yankTransition v).body .reverted := by
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
        exact ExecBlock.consRevert
          (internalCallFunctionRevert
            (cfg := config v)
            (caller := { contract := contract v, locals := clipperYankFluxRetStore I })
            (evm := evmVat)
            (name := "_remove") (retVar := "_removeRet")
            (args := [.var "id"])
            (argVals := [clipperYankArgValue I])
            (callee := removeFunction)
            (locals := clipperYankRemoveStore I)
            hremoveArgs (clipperYankRemoveLookup v) (clipperYankRemoveBind I)
            hremoveBody))
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Clipper
