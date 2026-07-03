import Examples.UniswapV2Pair.SyncRuntime
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `sync()` source/ABI prefix -/

theorem uniswapDecode_sync {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (syncTransition.params.map Param.name)
      (transitionSignature syncTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz


/-! ## Source body slices -/

abbrev syncBalanceStore (balance0 balance1 : UInt256) : Store :=
  uniswapBalanceOfStore (∅ : Store) (uniswapUint256Value balance0)
    (uniswapUint256Value balance1)

abbrev syncAfterUpdateStore (balance0 balance1 : UInt256) : Store :=
  (syncBalanceStore balance0 balance1).insert "_updateResult" Value.unit

abbrev syncAfterUpdateFrame (balance0 balance1 : UInt256) : Frame :=
  { contract := contract, locals := syncAfterUpdateStore balance0 balance1 }

abbrev syncUpdateCallArgVals (evm : EVM.State) (balance0 balance1 : UInt256) : List Value :=
  [ uniswapUint256Value balance0,
    uniswapUint256Value balance1,
    .int (Int.ofNat (uniswapReserve0Word evm).toNat),
    .int (Int.ofNat (uniswapReserve1Word evm).toNat) ]

abbrev syncUpdateCallStore (evm : EVM.State) (balance0 balance1 : UInt256) : Store :=
  ((((∅ : Store).insert "_reserve1" (.int (Int.ofNat (uniswapReserve1Word evm).toNat))).insert
      "_reserve0" (.int (Int.ofNat (uniswapReserve0Word evm).toNat))).insert
      "balance1" (uniswapUint256Value balance1)).insert
      "balance0" (uniswapUint256Value balance0)

abbrev syncUpdateCallFrame (evm : EVM.State) (balance0 balance1 : UInt256) : Frame :=
  { contract := contract, locals := syncUpdateCallStore evm balance0 balance1 }

theorem syncBalanceStore_balance0 (balance0 balance1 : UInt256) :
    (syncBalanceStore balance0 balance1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  exact uniswapBalanceOfStore_balance0 (∅ : Store) (uniswapUint256Value balance0)
    (uniswapUint256Value balance1)

theorem syncBalanceStore_balance1 (balance0 balance1 : UInt256) :
    (syncBalanceStore balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  exact uniswapBalanceOfStore_balance1 (∅ : Store) (uniswapUint256Value balance0)
    (uniswapUint256Value balance1)

theorem syncUpdateCallStore_balance0 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateCallStore evm balance0 balance1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  rw [syncUpdateCallStore, store_get_self]

theorem syncUpdateCallStore_balance1 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateCallStore evm balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  rw [syncUpdateCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem syncUpdateCallStore_reserve0 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateCallStore evm balance0 balance1).get? "_reserve0" =
      some (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) := by
  rw [syncUpdateCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem syncUpdateCallStore_reserve1 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateCallStore evm balance0 balance1).get? "_reserve1" =
      some (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  rw [syncUpdateCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_sync_update_balance0_le_max_true (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : Int.ofNat balance0.toNat ≤ maxUint112) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .le (.var "balance0") (.intLit maxUint112)) = .ok (.bool true) := by
  simp only [syncUpdateCallFrame, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance0]
  simpa [uniswapUint256Value, evalBinaryOp?] using hbound

theorem evalExpr_sync_update_balance0_le_max_false (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .le (.var "balance0") (.intLit maxUint112)) = .ok (.bool false) := by
  simp only [syncUpdateCallFrame, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance0]
  simpa [uniswapUint256Value, evalBinaryOp?] using hbound

theorem evalExpr_sync_update_balance1_le_max_false (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance1.toNat) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .le (.var "balance1") (.intLit maxUint112)) = .ok (.bool false) := by
  simp only [syncUpdateCallFrame, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance1]
  simpa [uniswapUint256Value, evalBinaryOp?] using hbound

theorem evalExpr_sync_update_bounds_true (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance0, syncUpdateCallStore_balance1]
  simp [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?]
  exact ⟨hbound0, hbound1⟩

theorem evalExpr_sync_update_bounds_false_first (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool false) := by
  have hnot : ¬ Int.ofNat balance0.toNat ≤ maxUint112 := by omega
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance0, syncUpdateCallStore_balance1]
  simp [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?]
  intro hle
  exact False.elim (hnot hle)

theorem evalExpr_sync_update_bounds_false_second (evm : EVM.State) (balance0 balance1 : UInt256)
    (_hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance0, syncUpdateCallStore_balance1]
  simp [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?]
  intro _hle0
  exact hbound1

theorem evalExprs_sync_update_call_args (evm : EVM.State) (balance0 balance1 : UInt256) :
    evalExprs? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ] =
        .ok (syncUpdateCallArgVals evm balance0 balance1) := by
  have h0 :
      evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
        (.var "balance0") = .ok (uniswapUint256Value balance0) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [syncBalanceStore_balance0]
  have h1 :
      evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
        (.var "balance1") = .ok (uniswapUint256Value balance1) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [syncBalanceStore_balance1]
  have hr0 :
      evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
        (.storage reserve0Ref) = .ok (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) :=
    evalExpr_uniswap_reserve0 evm (syncBalanceStore balance0 balance1)
      (by simp [syncBalanceStore, uniswapBalanceOfStore])
  have hr1 :
      evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
        (.storage reserve1Ref) = .ok (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) :=
    evalExpr_uniswap_reserve1 evm (syncBalanceStore balance0 balance1)
      (by simp [syncBalanceStore, uniswapBalanceOfStore])
  simp only [evalExprs?, EvalResult.bind, bind, syncUpdateCallArgVals]
  rw [h0, h1, hr0, hr1]
  rfl

theorem uniswapLookupUpdateFunction :
    lookupCallable? contract "_update" = some updateFunction.toCallable := by
  rfl

theorem bindParams_sync_update_call (evm : EVM.State) (balance0 balance1 : UInt256) :
    bindParams? updateFunction.params (syncUpdateCallArgVals evm balance0 balance1) =
      some (syncUpdateCallStore evm balance0 balance1) := by
  simp [bindParams?, updateFunction, syncUpdateCallArgVals, syncUpdateCallStore]

theorem uniswapUpdateFunctionReverts_firstBound
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    ExecFuncBody config (syncUpdateCallFrame evm balance0 balance1) evm
      updateFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_sync_update_bounds_false_first evm balance0 balance1 hbound)))

theorem uniswapUpdateFunctionReverts_secondBound
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecFuncBody config (syncUpdateCallFrame evm balance0 balance1) evm
      updateFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_sync_update_bounds_false_second evm balance0 balance1 hbound0 hbound1)))

theorem uniswapSyncUpdateCallReverts_firstBound
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    ExecStmt config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
        "_updateResult") .reverted := by
  exact Reasoning.Theory.internalCallFunctionRevert
    (callee := updateFunction) (locals := syncUpdateCallStore evm balance0 balance1)
    (evalExprs_sync_update_call_args evm balance0 balance1)
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call evm balance0 balance1)
    (uniswapUpdateFunctionReverts_firstBound evm balance0 balance1 hbound)

theorem uniswapSyncUpdateCallReverts_secondBound
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecStmt config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
        "_updateResult") .reverted := by
  exact Reasoning.Theory.internalCallFunctionRevert
    (callee := updateFunction) (locals := syncUpdateCallStore evm balance0 balance1)
    (evalExprs_sync_update_call_args evm balance0 balance1)
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call evm balance0 balance1)
    (uniswapUpdateFunctionReverts_secondBound evm balance0 balance1 hbound0 hbound1)

abbrev syncBlockTimestampInt (evm : EVM.State) : Int :=
  Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat % twoPow32

abbrev syncBlockTimestampValue (evm : EVM.State) : Value :=
  .int (syncBlockTimestampInt evm)

abbrev syncBlockTimestampStore (evm : EVM.State) (balance0 balance1 : UInt256) : Store :=
  (syncBalanceStore balance0 balance1).insert "blockTimestamp" (syncBlockTimestampValue evm)

abbrev syncUpdateBlockTimestampStore (evm : EVM.State) (balance0 balance1 : UInt256) : Store :=
  (syncUpdateCallStore evm balance0 balance1).insert "blockTimestamp"
    (syncBlockTimestampValue evm)

abbrev syncBlockTimestampLastWord (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
      reserve224Shift)
    reserve32Mask

abbrev syncTimeElapsedInt (evm : EVM.State) : Int :=
  (syncBlockTimestampInt evm - Int.ofNat (syncBlockTimestampLastWord evm).toNat + twoPow32) %
    twoPow32

abbrev syncTimeElapsedValue (evm : EVM.State) : Value :=
  .int (syncTimeElapsedInt evm)

abbrev syncPrice0CumulativeIntAt (storageEvm updateEvm : EVM.State) : Int :=
  (Int.ofNat (Solm.EVM.storageLoad storageEvm storageEvm.executionEnv.codeOwner ⟨9⟩).toNat +
    ((Int.ofNat (uniswapReserve1Word updateEvm).toNat * q112) /
      Int.ofNat (uniswapReserve0Word updateEvm).toNat) *
        syncTimeElapsedInt updateEvm) % twoPow256

abbrev syncPrice0CumulativeInt (evm : EVM.State) : Int :=
  syncPrice0CumulativeIntAt evm evm

abbrev syncPrice0CumulativeValueAt (storageEvm updateEvm : EVM.State) : Value :=
  .int (syncPrice0CumulativeIntAt storageEvm updateEvm)

abbrev syncPrice0CumulativeValue (evm : EVM.State) : Value :=
  .int (syncPrice0CumulativeInt evm)

abbrev syncPrice1CumulativeIntAt (storageEvm updateEvm : EVM.State) : Int :=
  (Int.ofNat (Solm.EVM.storageLoad storageEvm storageEvm.executionEnv.codeOwner ⟨10⟩).toNat +
    ((Int.ofNat (uniswapReserve0Word updateEvm).toNat * q112) /
      Int.ofNat (uniswapReserve1Word updateEvm).toNat) *
        syncTimeElapsedInt updateEvm) % twoPow256

abbrev syncPrice1CumulativeInt (evm : EVM.State) : Int :=
  syncPrice1CumulativeIntAt evm evm

abbrev syncPrice1CumulativeValueAt (storageEvm updateEvm : EVM.State) : Value :=
  .int (syncPrice1CumulativeIntAt storageEvm updateEvm)

abbrev syncPrice1CumulativeValue (evm : EVM.State) : Value :=
  .int (syncPrice1CumulativeInt evm)

abbrev syncUpdateTimeElapsedStore (evm : EVM.State) (balance0 balance1 : UInt256) : Store :=
  (syncUpdateBlockTimestampStore evm balance0 balance1).insert "timeElapsed"
    (syncTimeElapsedValue evm)

theorem syncBlockTimestampStore_balance0 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncBlockTimestampStore evm balance0 balance1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  rw [syncBlockTimestampStore, store_get_ne _ _ (by decide), syncBalanceStore_balance0]

theorem syncBlockTimestampStore_balance1 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncBlockTimestampStore evm balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  rw [syncBlockTimestampStore, store_get_ne _ _ (by decide), syncBalanceStore_balance1]

theorem syncBlockTimestampStore_blockTimestamp (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncBlockTimestampStore evm balance0 balance1).get? "blockTimestamp" =
      some (syncBlockTimestampValue evm) := by
  rw [syncBlockTimestampStore, store_get_self]

theorem syncUpdateBlockTimestampStore_balance0 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateBlockTimestampStore evm balance0 balance1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  rw [syncUpdateBlockTimestampStore, store_get_ne _ _ (by decide),
    syncUpdateCallStore_balance0]

theorem syncUpdateBlockTimestampStore_balance1 (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateBlockTimestampStore evm balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  rw [syncUpdateBlockTimestampStore, store_get_ne _ _ (by decide),
    syncUpdateCallStore_balance1]

theorem syncUpdateBlockTimestampStore_blockTimestamp
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateBlockTimestampStore evm balance0 balance1).get? "blockTimestamp" =
      some (syncBlockTimestampValue evm) := by
  rw [syncUpdateBlockTimestampStore, store_get_self]

theorem syncUpdateBlockTimestampStore_blockTimestampLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateBlockTimestampStore evm balance0 balance1).get? "blockTimestampLast" =
      none := by
  rw [syncUpdateBlockTimestampStore, store_get_ne _ _ (by decide)]
  simp [syncUpdateCallStore]

theorem syncUpdateTimeElapsedStore_balance0
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  rw [syncUpdateTimeElapsedStore, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStore_balance0]

theorem syncUpdateTimeElapsedStore_balance1
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  rw [syncUpdateTimeElapsedStore, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStore_balance1]

theorem syncUpdateTimeElapsedStore_blockTimestamp
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "blockTimestamp" =
      some (syncBlockTimestampValue evm) := by
  rw [syncUpdateTimeElapsedStore, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStore_blockTimestamp]

theorem syncUpdateTimeElapsedStore_timeElapsed
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "timeElapsed" =
      some (syncTimeElapsedValue evm) := by
  rw [syncUpdateTimeElapsedStore, store_get_self]

theorem syncUpdateTimeElapsedStore_reserve0
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "_reserve0" =
      some (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) := by
  rw [syncUpdateTimeElapsedStore, store_get_ne _ _ (by decide), syncUpdateBlockTimestampStore,
    store_get_ne _ _ (by decide), syncUpdateCallStore_reserve0]

theorem syncUpdateTimeElapsedStore_reserve1
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "_reserve1" =
      some (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  rw [syncUpdateTimeElapsedStore, store_get_ne _ _ (by decide), syncUpdateBlockTimestampStore,
    store_get_ne _ _ (by decide), syncUpdateCallStore_reserve1]

theorem syncUpdateTimeElapsedStore_reserve0_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "reserve0" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem syncUpdateTimeElapsedStore_reserve1_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "reserve1" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem syncUpdateTimeElapsedStore_blockTimestampLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "blockTimestampLast" = none := by
  rw [syncUpdateTimeElapsedStore, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStore_blockTimestampLast_none]

theorem syncUpdateTimeElapsedStore_price0CumulativeLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "price0CumulativeLast" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem syncUpdateTimeElapsedStore_price1CumulativeLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "price1CumulativeLast" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem uniswapStorageLocStore_word_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (wordLoc slot) (.int n) = some evm' := by
  unfold storageLocStore storageLocWriteWord wordLoc
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

theorem uniswapAssignPrice0CumulativeLastOfStore
    (evm evm' : EVM.State) (locals : Store) (value : Value)
    (hbase : locals.get? "price0CumulativeLast" = none)
    (hscalar : match value with | .struct _ _ | .array _ => False | _ => True)
    (hstore : storageLocStore evm (wordLoc ⟨9⟩) value = some evm') :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      price0CumulativeLastRef value =
        .ok ({ contract := contract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value
      (er := ({ base := "price0CumulativeLast", steps := [] } : EvaledStorageRef))
      (ty := uint256St) (loc := wordLoc ⟨9⟩)
  · simpa [price0CumulativeLastRef] using hbase
  · simp [evalStorageRef, evalStorageRefSteps, price0CumulativeLastRef, EvalResult.bind,
      pure, bind]
  · rfl
  · rfl
  · cases value <;> simp at hscalar ⊢
    simp [storageLocStore, valueToWord] at hstore
  · exact hstore

theorem uniswapAssignPrice1CumulativeLastOfStore
    (evm evm' : EVM.State) (locals : Store) (value : Value)
    (hbase : locals.get? "price1CumulativeLast" = none)
    (hscalar : match value with | .struct _ _ | .array _ => False | _ => True)
    (hstore : storageLocStore evm (wordLoc ⟨10⟩) value = some evm') :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      price1CumulativeLastRef value =
        .ok ({ contract := contract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value
      (er := ({ base := "price1CumulativeLast", steps := [] } : EvaledStorageRef))
      (ty := uint256St) (loc := wordLoc ⟨10⟩)
  · simpa [price1CumulativeLastRef] using hbase
  · simp [evalStorageRef, evalStorageRefSteps, price1CumulativeLastRef, EvalResult.bind,
      pure, bind]
  · rfl
  · rfl
  · cases value <;> simp at hscalar ⊢
    simp [storageLocStore, valueToWord] at hstore
  · exact hstore

theorem evalExpr_sync_balance0_le_max_true (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : Int.ofNat balance0.toNat ≤ maxUint112) :
    evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (.binary .le (.var "balance0") (.intLit maxUint112)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncBalanceStore_balance0]
  simpa [uniswapUint256Value, evalBinaryOp?] using hbound

theorem evalExpr_sync_balance1_le_max_true (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : Int.ofNat balance1.toNat ≤ maxUint112) :
    evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (.binary .le (.var "balance1") (.intLit maxUint112)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncBalanceStore_balance1]
  simpa [uniswapUint256Value, evalBinaryOp?] using hbound

theorem evalExpr_sync_balance0_le_max_false (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (.binary .le (.var "balance0") (.intLit maxUint112)) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncBalanceStore_balance0]
  simpa [uniswapUint256Value, evalBinaryOp?] using hbound

theorem evalExpr_sync_balance1_le_max_false (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance1.toNat) :
    evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (.binary .le (.var "balance1") (.intLit maxUint112)) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncBalanceStore_balance1]
  simpa [uniswapUint256Value, evalBinaryOp?] using hbound

theorem evalExpr_sync_blockTimestamp (evm : EVM.State) (balance0 balance1 : UInt256) :
    evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (u32 (.binary .mod now (.intLit twoPow32))) = .ok (syncBlockTimestampValue evm) := by
  simpa [u32, now, syncBlockTimestampValue, syncBlockTimestampInt, twoPow32, uint32Int] using
    evalExpr_timestampModUint32
      (cfg := config) (solm := { contract := contract, locals := syncBalanceStore balance0 balance1 })
      evm

theorem evalExpr_sync_update_blockTimestamp
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (u32 (.binary .mod now (.intLit twoPow32))) = .ok (syncBlockTimestampValue evm) := by
  simpa [u32, now, syncBlockTimestampValue, syncBlockTimestampInt, twoPow32, uint32Int] using
    evalExpr_timestampModUint32
      (cfg := config) (solm := syncUpdateCallFrame evm balance0 balance1) evm

theorem evalExpr_sync_blockTimestampLast (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "blockTimestampLast" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage blockTimestampLastRef) =
        .ok (.int (Int.ofNat (syncBlockTimestampLastWord evm).toNat)) := by
  have hload :
      storageLocLoad evm (uint32Loc28 ⟨8⟩) =
        .int (Int.ofNat (syncBlockTimestampLastWord evm).toNat) := by
    simpa [syncBlockTimestampLastWord] using uniswapStorageLocLoad_uint32_offset28 evm ⟨8⟩
  rw [evalExpr_storage_scalar (t := .int uint32Int) (slot := blockTimestampLastRef)
    (er := ({ base := "blockTimestampLast", steps := [] } : EvaledStorageRef))
    (loc := uint32Loc28 ⟨8⟩)
    (hbase := by simpa [blockTimestampLastRef] using hbase)
    (her := evalStorageRef_uniswap_blockTimestampLast evm locals)
    (hty := by rfl)
    (hloc := by rfl), hload]

theorem evalExpr_sync_price0CumulativeLast (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "price0CumulativeLast" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage price0CumulativeLastRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat)) := by
  have hload :
      storageLocLoad evm (wordLoc ⟨9⟩) =
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat) := by
    exact uniswapStorageLocLoad_uint256 evm ⟨9⟩
  rw [evalExpr_storage_scalar (t := .int uint256Int) (slot := price0CumulativeLastRef)
    (er := ({ base := "price0CumulativeLast", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨9⟩)
    (hbase := by simpa [price0CumulativeLastRef] using hbase)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, price0CumulativeLastRef, EvalResult.bind,
        pure, bind])
    (hty := by rfl)
    (hloc := by rfl), hload]

theorem evalExpr_sync_price1CumulativeLast (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "price1CumulativeLast" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage price1CumulativeLastRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩).toNat)) := by
  have hload :
      storageLocLoad evm (wordLoc ⟨10⟩) =
        .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩).toNat) := by
    exact uniswapStorageLocLoad_uint256 evm ⟨10⟩
  rw [evalExpr_storage_scalar (t := .int uint256Int) (slot := price1CumulativeLastRef)
    (er := ({ base := "price1CumulativeLast", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨10⟩)
    (hbase := by simpa [price1CumulativeLastRef] using hbase)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, price1CumulativeLastRef, EvalResult.bind,
        pure, bind])
    (hty := by rfl)
    (hloc := by rfl), hload]

theorem evalExpr_sync_update_timeElapsed
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    evalExpr? config
      { contract := contract, locals := syncUpdateBlockTimestampStore evm balance0 balance1 }
      evm
      (u32 (.binary .mod
        (.binary .add
          (.binary .sub (.var "blockTimestamp") (.storage blockTimestampLastRef))
          (.intLit twoPow32))
        (.intLit twoPow32))) = .ok (syncTimeElapsedValue evm) := by
  unfold u32 syncTimeElapsedValue syncTimeElapsedInt
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind,
    syncUpdateBlockTimestampStore_blockTimestamp,
    evalExpr_sync_blockTimestampLast evm (syncUpdateBlockTimestampStore evm balance0 balance1)
      (syncUpdateBlockTimestampStore_blockTimestampLast_none evm balance0 balance1)]
  simp [evalBinaryOp?]
  norm_num [twoPow32, uint32Int]
  have hnonneg :
      0 ≤ (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat -
          Int.ofNat (syncBlockTimestampLastWord evm).toNat) %
        (4294967296 : Int) := by
    exact Int.emod_nonneg _ (by norm_num)
  have hlt :
      (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat -
          Int.ofNat (syncBlockTimestampLastWord evm).toNat) %
          (4294967296 : Int) <
        4294967296 := by
    exact Int.emod_lt_of_pos _ (by norm_num)
  rw [if_neg]
  · rfl
  · exact fun h => by
      rcases h with hneg | hge
      · exact not_lt_of_ge hnonneg hneg
      · exact not_le_of_gt hlt hge

theorem evalExpr_sync_update_condition_false_elapsed_zero
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (helapsed : syncTimeElapsedInt evm = 0) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evm
      (.binary .and
        (.binary .gt (.var "timeElapsed") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "_reserve0") (.intLit 0))
          (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStore_timeElapsed, syncUpdateTimeElapsedStore_reserve0,
    syncUpdateTimeElapsedStore_reserve1]
  unfold syncTimeElapsedValue
  rw [helapsed]
  simp [evalBinaryOp?]

theorem evalExpr_sync_update_condition_false_reserve0_zero
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat = 0) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evm
      (.binary .and
        (.binary .gt (.var "timeElapsed") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "_reserve0") (.intLit 0))
          (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStore_timeElapsed, syncUpdateTimeElapsedStore_reserve0,
    syncUpdateTimeElapsedStore_reserve1]
  unfold syncTimeElapsedValue
  rw [hreserve0]
  simp [evalBinaryOp?]

theorem evalExpr_sync_update_condition_false_reserve1_zero
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm).toNat = 0) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evm
      (.binary .and
        (.binary .gt (.var "timeElapsed") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "_reserve0") (.intLit 0))
          (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStore_timeElapsed, syncUpdateTimeElapsedStore_reserve0,
    syncUpdateTimeElapsedStore_reserve1]
  unfold syncTimeElapsedValue
  rw [hreserve1]
  simp [evalBinaryOp?]

theorem evalExpr_sync_update_condition_true
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm).toNat ≠ 0) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evm
      (.binary .and
        (.binary .gt (.var "timeElapsed") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "_reserve0") (.intLit 0))
          (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStore_timeElapsed, syncUpdateTimeElapsedStore_reserve0,
    syncUpdateTimeElapsedStore_reserve1]
  unfold syncTimeElapsedValue
  simp [evalBinaryOp?]
  constructor
  · simpa [syncTimeElapsedInt] using helapsed
  · constructor
    · intro hzero
      exact hreserve0 (by simp [hzero])
    · intro hzero
      exact hreserve1 (by simp [hzero])

theorem evalExpr_sync_update_price0Cumulative
    (storageEvm updateEvm : EVM.State) (balance0 balance1 : UInt256)
    (hreserve0 : Int.ofNat (uniswapReserve0Word updateEvm).toNat ≠ 0) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore updateEvm balance0 balance1 }
      storageEvm
      (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
        (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
          (.var "timeElapsed")))) =
        .ok (syncPrice0CumulativeValueAt storageEvm updateEvm) := by
  have hreserve0Nat : (uniswapReserve0Word updateEvm).toNat ≠ 0 := by
    intro hzero
    exact hreserve0 (by simp [hzero])
  unfold wrapU256 uq112Price syncPrice0CumulativeValueAt syncPrice0CumulativeIntAt
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind,
    evalExpr_sync_price0CumulativeLast storageEvm
      (syncUpdateTimeElapsedStore updateEvm balance0 balance1)
      (syncUpdateTimeElapsedStore_price0CumulativeLast_none updateEvm balance0 balance1),
    syncUpdateTimeElapsedStore_reserve1, syncUpdateTimeElapsedStore_reserve0,
    syncUpdateTimeElapsedStore_timeElapsed]
  unfold syncTimeElapsedValue
  simp [evalBinaryOp?, hreserve0Nat, twoPow256]

theorem evalExpr_sync_update_price1Cumulative
    (storageEvm updateEvm : EVM.State) (balance0 balance1 : UInt256)
    (hreserve1 : Int.ofNat (uniswapReserve1Word updateEvm).toNat ≠ 0) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore updateEvm balance0 balance1 }
      storageEvm
      (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
        (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
          (.var "timeElapsed")))) =
        .ok (syncPrice1CumulativeValueAt storageEvm updateEvm) := by
  have hreserve1Nat : (uniswapReserve1Word updateEvm).toNat ≠ 0 := by
    intro hzero
    exact hreserve1 (by simp [hzero])
  unfold wrapU256 uq112Price syncPrice1CumulativeValueAt syncPrice1CumulativeIntAt
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind,
    evalExpr_sync_price1CumulativeLast storageEvm
      (syncUpdateTimeElapsedStore updateEvm balance0 balance1)
      (syncUpdateTimeElapsedStore_price1CumulativeLast_none updateEvm balance0 balance1),
    syncUpdateTimeElapsedStore_reserve0, syncUpdateTimeElapsedStore_reserve1,
    syncUpdateTimeElapsedStore_timeElapsed]
  unfold syncTimeElapsedValue
  simp [evalBinaryOp?, hreserve1Nat, twoPow256]

theorem evalExpr_sync_update_u112_balance0
    (evm evalEvm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : Int.ofNat balance0.toNat ≤ maxUint112) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evalEvm (u112 (.var "balance0")) = .ok (uniswapUint256Value balance0) := by
  have hltInt : Int.ofNat balance0.toNat < Int.ofNat (2 ^ 112) := by
    norm_num [maxUint112] at hbound ⊢
    omega
  unfold u112 uniswapUint256Value
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStore_balance0]
  simp only [uint112Int]
  rw [if_neg]
  · rfl
  · exact fun h => by
      rw [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with hneg | hge
      · exact not_lt_of_ge (Int.natCast_nonneg balance0.toNat) hneg
      · rw [decide_eq_true_eq] at hge
        exact not_le_of_gt hltInt hge

theorem evalExpr_sync_update_u112_balance1
    (evm evalEvm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : Int.ofNat balance1.toNat ≤ maxUint112) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evalEvm (u112 (.var "balance1")) = .ok (uniswapUint256Value balance1) := by
  have hltInt : Int.ofNat balance1.toNat < Int.ofNat (2 ^ 112) := by
    norm_num [maxUint112] at hbound ⊢
    omega
  unfold u112 uniswapUint256Value
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStore_balance1]
  simp only [uint112Int]
  rw [if_neg]
  · rfl
  · exact fun h => by
      rw [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with hneg | hge
      · exact not_lt_of_ge (Int.natCast_nonneg balance1.toNat) hneg
      · rw [decide_eq_true_eq] at hge
        exact not_le_of_gt hltInt hge

theorem evalExpr_sync_update_blockTimestamp_var
    (evm timestampEvm : EVM.State) (balance0 balance1 : UInt256) :
    evalExpr? config
      { contract := contract, locals := syncUpdateTimeElapsedStore timestampEvm balance0 balance1 }
      evm (.var "blockTimestamp") = .ok (syncBlockTimestampValue timestampEvm) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [syncUpdateTimeElapsedStore_blockTimestamp]

theorem uniswapUpdateFunctionReturns_conditionFalse
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (hcond :
      evalExpr? config
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
        evm
        (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false)) :
    ∃ evm',
      ExecFuncBody config (syncUpdateCallFrame evm balance0 balance1) evm
        updateFunction.body
        (.returned
          { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
          evm' none) := by
  obtain ⟨evm0, hstore0⟩ :=
    uniswapStorageLocStore_uint112_offset0_int_some evm ⟨8⟩ (Int.ofNat balance0.toNat)
  obtain ⟨evm1, hstore1⟩ :=
    uniswapStorageLocStore_uint112_offset14_int_some evm0 ⟨8⟩
      (Int.ofNat balance1.toNat)
  obtain ⟨evm2, hstoreTs⟩ :=
    uniswapStorageLocStore_uint32_offset28_int_some evm1 ⟨8⟩ (syncBlockTimestampInt evm)
  refine ⟨evm2, ExecFuncBody.execBlockOK ?_⟩
  change ExecBlock config (syncUpdateCallFrame evm balance0 balance1) evm
    [ .require (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))),
      .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))),
      .letDecl "timeElapsed" (some uint32)
        (u32 (.binary .mod
          (.binary .add
            (.binary .sub (.var "blockTimestamp") (.storage blockTimestampLastRef))
            (.intLit twoPow32))
          (.intLit twoPow32))),
      .ite (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0))))
        [ .assign .storage price0CumulativeLastRef
            (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                (.var "timeElapsed")))),
          .assign .storage price1CumulativeLastRef
            (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                (.var "timeElapsed")))) ]
        [],
      .assign .storage reserve0Ref (u112 (.var "balance0")),
      .assign .storage reserve1Ref (u112 (.var "balance1")),
      .assign .storage blockTimestampLastRef (.var "blockTimestamp") ]
    (.ok { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evm2)
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_sync_update_bounds_true evm balance0 balance1 hbound0 hbound1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sync_update_blockTimestamp evm balance0 balance1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sync_update_timeElapsed evm balance0 balance1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse hcond ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance0 evm evm balance0 balance1 hbound0)
      (uniswapAssignReserve0OfStore evm evm0
        (syncUpdateTimeElapsedStore evm balance0 balance1) balance0
        (syncUpdateTimeElapsedStore_reserve0_none evm balance0 balance1)
        hstore0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance1 evm evm0 balance0 balance1 hbound1)
      (uniswapAssignReserve1OfStore evm0 evm1
        (syncUpdateTimeElapsedStore evm balance0 balance1) balance1
        (syncUpdateTimeElapsedStore_reserve1_none evm balance0 balance1)
        hstore1)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_blockTimestamp_var evm1 evm balance0 balance1)
      (uniswapAssignBlockTimestampLastOfStore evm1 evm2
        (syncUpdateTimeElapsedStore evm balance0 balance1) (syncBlockTimestampValue evm)
        (syncUpdateTimeElapsedStore_blockTimestampLast_none evm balance0 balance1)
        (by simp)
        hstoreTs))
    ExecBlock.nil

theorem uniswapUpdateFunctionReturns_elapsedZero
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : syncTimeElapsedInt evm = 0) :
    ∃ evm',
      ExecFuncBody config (syncUpdateCallFrame evm balance0 balance1) evm
        updateFunction.body
        (.returned
          { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
          evm' none) := by
  exact uniswapUpdateFunctionReturns_conditionFalse evm balance0 balance1 hbound0 hbound1
    (evalExpr_sync_update_condition_false_elapsed_zero evm balance0 balance1 helapsed)

theorem uniswapUpdateFunctionReturns_conditionTrue
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm).toNat ≠ 0) :
    ∃ evm',
      ExecFuncBody config (syncUpdateCallFrame evm balance0 balance1) evm
        updateFunction.body
        (.returned
          { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
          evm' none) := by
  obtain ⟨evmP0, hstoreP0⟩ :=
    uniswapStorageLocStore_word_int_some evm ⟨9⟩
      (syncPrice0CumulativeIntAt evm evm)
  obtain ⟨evmP1, hstoreP1⟩ :=
    uniswapStorageLocStore_word_int_some evmP0 ⟨10⟩
      (syncPrice1CumulativeIntAt evmP0 evm)
  obtain ⟨evmR0, hstoreR0⟩ :=
    uniswapStorageLocStore_uint112_offset0_int_some evmP1 ⟨8⟩
      (Int.ofNat balance0.toNat)
  obtain ⟨evmR1, hstoreR1⟩ :=
    uniswapStorageLocStore_uint112_offset14_int_some evmR0 ⟨8⟩
      (Int.ofNat balance1.toNat)
  obtain ⟨evmTs, hstoreTs⟩ :=
    uniswapStorageLocStore_uint32_offset28_int_some evmR1 ⟨8⟩ (syncBlockTimestampInt evm)
  refine ⟨evmTs, ExecFuncBody.execBlockOK ?_⟩
  change ExecBlock config (syncUpdateCallFrame evm balance0 balance1) evm
    [ .require (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))),
      .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))),
      .letDecl "timeElapsed" (some uint32)
        (u32 (.binary .mod
          (.binary .add
            (.binary .sub (.var "blockTimestamp") (.storage blockTimestampLastRef))
            (.intLit twoPow32))
          (.intLit twoPow32))),
      .ite (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0))))
        [ .assign .storage price0CumulativeLastRef
            (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                (.var "timeElapsed")))),
          .assign .storage price1CumulativeLastRef
            (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                (.var "timeElapsed")))) ]
        [],
      .assign .storage reserve0Ref (u112 (.var "balance0")),
      .assign .storage reserve1Ref (u112 (.var "balance1")),
      .assign .storage blockTimestampLastRef (.var "blockTimestamp") ]
    (.ok { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
      evmTs)
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_sync_update_bounds_true evm balance0 balance1 hbound0 hbound1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sync_update_blockTimestamp evm balance0 balance1)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_sync_update_timeElapsed evm balance0 balance1)) ?_
  have hpriceBlock :
      ExecBlock config
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 } evm
        [ .assign .storage price0CumulativeLastRef
            (wrapU256 (.binary .add (.storage price0CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve1") (.var "_reserve0"))
                (.var "timeElapsed")))),
          .assign .storage price1CumulativeLastRef
            (wrapU256 (.binary .add (.storage price1CumulativeLastRef)
              (.binary .mul (uq112Price (.var "_reserve0") (.var "_reserve1"))
                (.var "timeElapsed")))) ]
        (.ok { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
          evmP1) := by
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_update_price0Cumulative evm evm balance0 balance1 hreserve0)
        (uniswapAssignPrice0CumulativeLastOfStore evm evmP0
          (syncUpdateTimeElapsedStore evm balance0 balance1)
          (syncPrice0CumulativeValueAt evm evm)
          (syncUpdateTimeElapsedStore_price0CumulativeLast_none evm balance0 balance1)
          (by simp)
          (by simpa [syncPrice0CumulativeValueAt] using hstoreP0))) ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_update_price1Cumulative evmP0 evm balance0 balance1 hreserve1)
        (uniswapAssignPrice1CumulativeLastOfStore evmP0 evmP1
          (syncUpdateTimeElapsedStore evm balance0 balance1)
          (syncPrice1CumulativeValueAt evmP0 evm)
          (syncUpdateTimeElapsedStore_price1CumulativeLast_none evm balance0 balance1)
          (by simp)
          (by simpa [syncPrice1CumulativeValueAt] using hstoreP1)))
      ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (evalExpr_sync_update_condition_true evm balance0 balance1 helapsed hreserve0 hreserve1)
      hpriceBlock) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance0 evm evmP1 balance0 balance1 hbound0)
      (uniswapAssignReserve0OfStore evmP1 evmR0
        (syncUpdateTimeElapsedStore evm balance0 balance1) balance0
        (syncUpdateTimeElapsedStore_reserve0_none evm balance0 balance1)
        hstoreR0)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_u112_balance1 evm evmR0 balance0 balance1 hbound1)
      (uniswapAssignReserve1OfStore evmR0 evmR1
        (syncUpdateTimeElapsedStore evm balance0 balance1) balance1
        (syncUpdateTimeElapsedStore_reserve1_none evm balance0 balance1)
        hstoreR1)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_sync_update_blockTimestamp_var evmR1 evm balance0 balance1)
      (uniswapAssignBlockTimestampLastOfStore evmR1 evmTs
        (syncUpdateTimeElapsedStore evm balance0 balance1) (syncBlockTimestampValue evm)
        (syncUpdateTimeElapsedStore_blockTimestampLast_none evm balance0 balance1)
        (by simp)
        hstoreTs))
    ExecBlock.nil

theorem uniswapSyncUpdateCallReturns_elapsedZero
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : syncTimeElapsedInt evm = 0) :
    ∃ evm',
      ExecStmt config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
        (.internalCall "_update"
          [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
          "_updateResult")
        (.ok (syncAfterUpdateFrame balance0 balance1) evm') := by
  obtain ⟨evm', hbody⟩ :=
    uniswapUpdateFunctionReturns_elapsedZero evm balance0 balance1 hbound0 hbound1 helapsed
  refine ⟨evm', ?_⟩
  simpa [syncAfterUpdateFrame, syncAfterUpdateStore, resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := syncBalanceStore balance0 balance1 })
      (evm := evm) (calleeEvm := evm')
      (name := "_update") (retVar := "_updateResult")
      (args := [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ])
      (argVals := syncUpdateCallArgVals evm balance0 balance1) (callee := updateFunction)
      (locals := syncUpdateCallStore evm balance0 balance1)
      (calleeSolm :=
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 })
      (value := none)
      (evalExprs_sync_update_call_args evm balance0 balance1)
      uniswapLookupUpdateFunction
      (bindParams_sync_update_call evm balance0 balance1)
      hbody)

theorem uniswapSyncUpdateCallReturns_conditionFalse
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (hcond :
      evalExpr? config
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
        evm
        (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false)) :
    ∃ evm',
      ExecStmt config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
        (.internalCall "_update"
          [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
          "_updateResult")
        (.ok (syncAfterUpdateFrame balance0 balance1) evm') := by
  obtain ⟨evm', hbody⟩ :=
    uniswapUpdateFunctionReturns_conditionFalse evm balance0 balance1 hbound0 hbound1 hcond
  refine ⟨evm', ?_⟩
  simpa [syncAfterUpdateFrame, syncAfterUpdateStore, resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := syncBalanceStore balance0 balance1 })
      (evm := evm) (calleeEvm := evm')
      (name := "_update") (retVar := "_updateResult")
      (args := [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ])
      (argVals := syncUpdateCallArgVals evm balance0 balance1) (callee := updateFunction)
      (locals := syncUpdateCallStore evm balance0 balance1)
      (calleeSolm :=
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 })
      (value := none)
      (evalExprs_sync_update_call_args evm balance0 balance1)
      uniswapLookupUpdateFunction
      (bindParams_sync_update_call evm balance0 balance1)
      hbody)

theorem uniswapSyncUpdateCallReturns_conditionTrue
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm).toNat ≠ 0) :
    ∃ evm',
      ExecStmt config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
        (.internalCall "_update"
          [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
          "_updateResult")
        (.ok (syncAfterUpdateFrame balance0 balance1) evm') := by
  obtain ⟨evm', hbody⟩ :=
    uniswapUpdateFunctionReturns_conditionTrue evm balance0 balance1 hbound0 hbound1
      helapsed hreserve0 hreserve1
  refine ⟨evm', ?_⟩
  simpa [syncAfterUpdateFrame, syncAfterUpdateStore, resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := syncBalanceStore balance0 balance1 })
      (evm := evm) (calleeEvm := evm')
      (name := "_update") (retVar := "_updateResult")
      (args := [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ])
      (argVals := syncUpdateCallArgVals evm balance0 balance1) (callee := updateFunction)
      (locals := syncUpdateCallStore evm balance0 balance1)
      (calleeSolm :=
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 })
      (value := none)
      (evalExprs_sync_update_call_args evm balance0 balance1)
      uniswapLookupUpdateFunction
      (bindParams_sync_update_call evm balance0 balance1)
      hbody)

theorem evalExpr_sync_balance0_afterTimestamp (evm timestampEvm : EVM.State)
    (balance0 balance1 : UInt256) :
    evalExpr? config
      { contract := contract, locals := syncBlockTimestampStore timestampEvm balance0 balance1 }
      evm (.var "balance0") = .ok (uniswapUint256Value balance0) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [syncBlockTimestampStore_balance0]

theorem evalExpr_sync_balance1_afterTimestamp (evm timestampEvm : EVM.State)
    (balance0 balance1 : UInt256) :
    evalExpr? config
      { contract := contract, locals := syncBlockTimestampStore timestampEvm balance0 balance1 }
      evm (.var "balance1") = .ok (uniswapUint256Value balance1) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [syncBlockTimestampStore_balance1]

theorem evalExpr_sync_blockTimestamp_var (evm timestampEvm : EVM.State)
    (balance0 balance1 : UInt256) :
    evalExpr? config
      { contract := contract, locals := syncBlockTimestampStore timestampEvm balance0 balance1 }
      evm (.var "blockTimestamp") = .ok (syncBlockTimestampValue timestampEvm) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [syncBlockTimestampStore_blockTimestamp]

abbrev syncBalanceCallsBody : List Stmt :=
  pairBalanceOfThisStmts "balance0" "balance1"

abbrev syncToken0GuardTrue (evm : EVM.State) : Prop :=
  evalExpr? config { contract := contract, locals := ∅ } (uniswapLockEnteredState evm)
    (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true)

abbrev syncToken0GuardFalse (evm : EVM.State) : Prop :=
  evalExpr? config { contract := contract, locals := ∅ } (uniswapLockEnteredState evm)
    (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool false)

abbrev syncToken1GuardTrue (evm0 : EVM.State) (balance0 : Value) : Prop :=
  evalExpr? config { contract := contract, locals := (∅ : Store).insert "balance0" balance0 }
    evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true)

theorem syncToken0GuardFalse_initState_of_noCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩) :
    syncToken0GuardFalse (initState cA gh bl σ_solm σ₀ g A I) := by
  let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
  let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
  let token0WordE := uniswapSlotWord ⟨6⟩ σLockE I
  let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
  have hLockAccounts : accountMapEquiv σLockE σLockS := by
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
  have hslot : token0WordE = token0WordS := by
    simpa [σLockE, σLockS, token0WordE, token0WordS] using
      accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hnoSolm :
      uniswapExtCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) = ⟨0⟩ := by
    have hsame :=
      uniswapExtCodeSizeWord_accountMapEquiv hLockAccounts
        (UInt256.land solcAddrMask token0WordE)
    have hnoE :
        uniswapExtCodeSizeWord σLockE (UInt256.land solcAddrMask token0WordE) = ⟨0⟩ := by
      simpa [σLockE, token0WordE] using htoken0NoCode
    rw [← hslot]
    rw [← hsame]
    exact hnoE
  unfold syncToken0GuardFalse
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmL := uniswapLockEnteredState evmS
  have hstorage :
      evalExpr? config { contract := contract, locals := ∅ } evmL
        (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    exact evalExpr_uniswap_storage_address evmL ∅
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hnoSource :
      (evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) =
        ⟨0⟩ := by
    have hnoSolmRight :
        uniswapExtCodeSizeWord σLockS (UInt256.land token0WordS solcAddrMask) = ⟨0⟩ := by
      simpa [u256_land_comm] using hnoSolm
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap, storageStore_executionEnv, State.lookupAccount, Solm.EVM.storageLoad,
      Account.lookupStorage, uniswapAddressAtSlot, uniswapExtCodeSizeWord, uniswapSlotWord, σLockS,
      token0WordS, accountAddress_ofUInt256_eq_ofNat_toNat] using hnoSolmRight
  have hnoSourceWord :
      EVM.Word.ofNat
          ((evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option 0
            (fun acc => acc.code.size)) =
        ⟨0⟩ := by
    cases hacc : evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩) with
    | none =>
        exact UInt256_ofNat_0
    | some acc =>
        simpa [hacc, Option.option] using hnoSource
  change
    evalExpr? config { contract := contract, locals := ∅ } evmL
      (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
        .ok (.bool false)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hnoSourceWord]

theorem uniswapSyncLockEnterPrefix (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := ∅ } evm lockEnter
      (.ok { contract := contract, locals := ∅ } (uniswapLockEnteredState evm)) := by
  exact uniswapLockEnterPrefix evm ∅ hwv (by simp) hunlocked

theorem uniswapSyncNonpayableSource (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hlock := uniswapLockEnterNonpayableRevert evm ∅ hwv
  simpa [syncTransition, List.append_assoc] using
    (execBlock_append_term
      (s2 := syncBalanceCallsBody ++
        updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hlock (by intro f e h; cases h))

theorem uniswapSyncLockedSource (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hlock := uniswapLockEnterLockedRevert evm ∅ hwv (by simp) hlocked
  simpa [syncTransition, List.append_assoc] using
    (execBlock_append_term
      (s2 := syncBalanceCallsBody ++
        updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hlock (by intro f e h; cases h))

theorem uniswapSyncBalanceOfCallsPrefix (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some [balance1]) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody)
      (.ok (uniswapBalanceOfFrame ∅ balance0 balance1) evm1) := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hcalls := uniswapCheckedTokenBalanceOfThisCallsPrefix
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := ∅)
    (balance0 := balance0) (balance1 := balance1)
    hguard0 hguard1 (by simp) (by simp) hcall0 hdec0 hcall1 hdec1
  simpa [syncBalanceCallsBody] using execBlock_append hlock hcalls

theorem uniswapSyncBalanceOfFirstCallFailure (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0) false) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := ∅)
    hguard0 (by simp) hcall0
  simpa [syncBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfFirstCallNoCode (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardFalse evm) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallNoCode
    (evm := uniswapLockEnteredState evm) (locals := ∅) hguard0
  simpa [syncBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfFirstCallDecodeRevert (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := ∅)
    hguard0 (by simp) hcall0 hdec0
  simpa [syncBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfSecondCallFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1) false) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisSecondCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := ∅)
    (balance0 := balance0)
    hguard0 hguard1 (by simp) (by simp) hcall0 hdec0 hcall1
  simpa [syncBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfSecondCallDecodeRevert (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisSecondCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := ∅)
    (balance0 := balance0)
    hguard0 hguard1 (by simp) (by simp) hcall0 hdec0 hcall1 hdec1
  simpa [syncBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSyncFirstCallFailureSource (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0) false) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfFirstCallFailure evm evm0 hwv hunlocked hguard0 hcall0
  simpa [syncTransition, syncBalanceCallsBody, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncFirstCallNoCodeSource (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardFalse evm) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfFirstCallNoCode evm hwv hunlocked hguard0
  simpa [syncTransition, syncBalanceCallsBody, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncFirstCallDecodeRevertSource (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix :=
    uniswapSyncBalanceOfFirstCallDecodeRevert evm evm0 hwv hunlocked hguard0 hcall0 hdec0
  simpa [syncTransition, syncBalanceCallsBody, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncSecondCallFailureSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1) false) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix :=
    uniswapSyncBalanceOfSecondCallFailure evm evm0 evm1 hwv hunlocked
      hguard0 hcall0 hdec0 hguard1 hcall1
  simpa [syncTransition, syncBalanceCallsBody, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncSecondCallDecodeRevertSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfSecondCallDecodeRevert
    evm evm0 evm1 hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  simpa [syncTransition, syncBalanceCallsBody, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncFirstBoundFailureSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : maxUint112 < Int.ofNat balance0.toNat) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  have hupdate :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        (updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit) .reverted := by
    exact ExecBlock.consRevert
      (uniswapSyncUpdateCallReverts_firstBound evm1 balance0 balance1 hbound0)
  simpa [syncTransition, syncBalanceCallsBody, updateReservesStmts, List.append_assoc] using
    execBlock_append hbalances hupdate

theorem uniswapSyncSecondBoundFailureSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  have hupdate :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        (updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit) .reverted := by
    exact ExecBlock.consRevert
      (uniswapSyncUpdateCallReverts_secondBound evm1 balance0 balance1 hbound0 hbound1)
  simpa [syncTransition, syncBalanceCallsBody, updateReservesStmts, List.append_assoc] using
    execBlock_append hbalances hupdate

/-! ## `sync()` source-body wrappers -/

theorem uniswapSyncBodyReverts_nonpayable (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (uniswapSyncNonpayableSource evm hwv)

theorem uniswapSyncBodyReverts_locked (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (uniswapSyncLockedSource evm hwv hlocked)

theorem uniswapSyncBodyReverts_firstNoCode (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardFalse evm) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncFirstCallNoCodeSource evm hwv hunlocked hguard0)

theorem uniswapSyncBodyReverts_firstCallFailure (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0) false) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncFirstCallFailureSource evm evm0 hwv hunlocked hguard0 hcall0)

theorem uniswapSyncBodyReverts_firstCallDecode (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncFirstCallDecodeRevertSource evm evm0 hwv hunlocked hguard0 hcall0 hdec0)

theorem uniswapSyncBodyReverts_secondCallFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1) false) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondCallFailureSource evm evm0 evm1 hwv hunlocked
      hguard0 hcall0 hdec0 hguard1 hcall1)

theorem uniswapSyncBodyReverts_secondCallDecode (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondCallDecodeRevertSource evm evm0 evm1 hwv hunlocked hguard0 hcall0 hdec0
      hguard1 hcall1 hdec1)

theorem uniswapSyncBodyReverts_firstBoundFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : maxUint112 < Int.ofNat balance0.toNat) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncFirstBoundFailureSource evm evm0 evm1 hwv hunlocked hguard0 hcall0 hdec0
      hguard1 hcall1 hdec1 hbound0)

theorem uniswapSyncBodyReverts_secondBoundFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondBoundFailureSource evm evm0 evm1 hwv hunlocked hguard0 hcall0 hdec0
      hguard1 hcall1 hdec1 hbound0 hbound1)

theorem uniswapSyncBodyReturns_conditionFalse (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (hcond :
      evalExpr? config
        { contract := contract, locals := syncUpdateTimeElapsedStore evm1 balance0 balance1 }
        evm1
        (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false)) :
    ∃ evm2 : EVM.State,
      ExecTransitionBody config contract evm ∅ syncTransition.body
        (.returned
          (syncAfterUpdateFrame balance0 balance1)
          (uniswapLockExitedState evm2) none) := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  obtain ⟨evm2, hupdateStmt⟩ :=
    uniswapSyncUpdateCallReturns_conditionFalse evm1 balance0 balance1 hbound0 hbound1 hcond
  have hupdateBlock :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        (updateReservesStmts (.var "balance0") (.var "balance1"))
        (.ok (syncAfterUpdateFrame balance0 balance1) evm2) := by
    simpa [updateReservesStmts] using
      (ExecBlock.consNormal hupdateStmt ExecBlock.nil)
  have hlock := uniswapLockExitSuffix evm2 (syncAfterUpdateStore balance0 balance1)
    (by simp [syncAfterUpdateStore, syncBalanceStore, uniswapBalanceOfStore])
  have htail := execBlock_append hupdateBlock hlock
  have hbody := execBlock_append hbalances htail
  refine ⟨evm2, ExecFuncBody.execBlockOK ?_⟩
  simpa [syncTransition, syncBalanceCallsBody, updateReservesStmts, List.append_assoc] using hbody

theorem uniswapSyncBodyReturns_elapsedZero (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : syncTimeElapsedInt evm1 = 0) :
    ∃ evm2 : EVM.State,
      ExecTransitionBody config contract evm ∅ syncTransition.body
        (.returned
          (syncAfterUpdateFrame balance0 balance1)
          (uniswapLockExitedState evm2) none) := by
  exact uniswapSyncBodyReturns_conditionFalse evm evm0 evm1 hwv hunlocked hguard0 hcall0
    hdec0 hguard1 hcall1 hdec1 hbound0 hbound1
    (evalExpr_sync_update_condition_false_elapsed_zero evm1 balance0 balance1 helapsed)

theorem uniswapSyncBodyReturns_conditionTrue (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm1)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm1).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm1).toNat ≠ 0) :
    ∃ evm2 : EVM.State,
      ExecTransitionBody config contract evm ∅ syncTransition.body
        (.returned
          (syncAfterUpdateFrame balance0 balance1)
          (uniswapLockExitedState evm2) none) := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  obtain ⟨evm2, hupdateStmt⟩ :=
    uniswapSyncUpdateCallReturns_conditionTrue evm1 balance0 balance1 hbound0 hbound1
      helapsed hreserve0 hreserve1
  have hupdateBlock :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        (updateReservesStmts (.var "balance0") (.var "balance1"))
        (.ok (syncAfterUpdateFrame balance0 balance1) evm2) := by
    simpa [updateReservesStmts] using
      (ExecBlock.consNormal hupdateStmt ExecBlock.nil)
  have hlock := uniswapLockExitSuffix evm2 (syncAfterUpdateStore balance0 balance1)
    (by simp [syncAfterUpdateStore, syncBalanceStore, uniswapBalanceOfStore])
  have htail := execBlock_append hupdateBlock hlock
  have hbody := execBlock_append hbalances htail
  refine ⟨evm2, ExecFuncBody.execBlockOK ?_⟩
  simpa [syncTransition, syncBalanceCallsBody, updateReservesStmts, List.append_assoc] using hbody

theorem uniswapSyncBodyReturns (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some [uniswapUint256Value balance0])
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some [uniswapUint256Value balance1])
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ∃ evm2 : EVM.State,
      ExecTransitionBody config contract evm ∅ syncTransition.body
        (.returned
          (syncAfterUpdateFrame balance0 balance1)
          (uniswapLockExitedState evm2) none) := by
  by_cases helapsed : syncTimeElapsedInt evm1 = 0
  · exact uniswapSyncBodyReturns_elapsedZero evm evm0 evm1 hwv hunlocked hguard0 hcall0
      hdec0 hguard1 hcall1 hdec1 hbound0 hbound1 helapsed
  · by_cases hreserve0 : Int.ofNat (uniswapReserve0Word evm1).toNat = 0
    · exact uniswapSyncBodyReturns_conditionFalse evm evm0 evm1 hwv hunlocked hguard0
        hcall0 hdec0 hguard1 hcall1 hdec1 hbound0 hbound1
        (evalExpr_sync_update_condition_false_reserve0_zero evm1 balance0 balance1 hreserve0)
    · by_cases hreserve1 : Int.ofNat (uniswapReserve1Word evm1).toNat = 0
      · exact uniswapSyncBodyReturns_conditionFalse evm evm0 evm1 hwv hunlocked hguard0
          hcall0 hdec0 hguard1 hcall1 hdec1 hbound0 hbound1
          (evalExpr_sync_update_condition_false_reserve1_zero evm1 balance0 balance1 hreserve1)
      · have helapsedNonneg : 0 ≤ syncTimeElapsedInt evm1 := by
          unfold syncTimeElapsedInt
          exact Int.emod_nonneg _ (by norm_num [twoPow32])
        have helapsedPos : 0 < syncTimeElapsedInt evm1 := by omega
        exact uniswapSyncBodyReturns_conditionTrue evm evm0 evm1 hwv hunlocked hguard0
          hcall0 hdec0 hguard1 hcall1 hdec1 hbound0 hbound1
          helapsedPos hreserve0 hreserve1

/-! ## `sync()` refinement slices -/

theorem uniswapSyncBodyCoreRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩ := by
    simpa [evmS] using
      (initState_codeOwner_storageLoad_ne_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot := ⟨12⟩) (val := ⟨1⟩) hAccounts hlocked)
  have hdecode := uniswapDecode_sync (I := I) hsz4
  have hbody :
      ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
    exact uniswapSyncBodyReverts_locked evmS
      (by simp only [evmS, initState]; exact hwv)
      hlockedSolm
  exact (uniswapSyncX_locked (g := Sat256.ofUInt256 g) hlocked hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSyncBodyCoreRevert_firstNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hunlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
    have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
    simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using (hword ▸ hunlocked)
  have hguard0 : syncToken0GuardFalse evmS :=
    syncToken0GuardFalse_initState_of_noCode hAccounts htoken0NoCode
  have hbody :
      ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
    exact uniswapSyncBodyReverts_firstNoCode evmS
      (by simp only [evmS, initState]; exact hwv)
      hunlockedSolm hguard0
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩ rfl hsel
  exact (uniswapSyncRuntimeFirstBalanceOfMissingCodeReverts
      (g := g) hcode hsize hwv hsel hperm hunlocked htoken0NoCode)
    |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_sync hsz4) hbody

/-- Locked-revert `sync()` refinement slice, packaged from selector dispatch through the body
core. -/
theorem uniswapSyncBodyRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩ rfl hsel
  exact uniswapSyncBodyCoreRevert_locked hcode hwv hsz4 hlocked hdispatch
    (uniswapReachSyncBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

theorem uniswapSyncBodyRevert_firstNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact uniswapSyncBodyCoreRevert_firstNoCode hcode hsize hperm hwv hsel
    hunlocked htoken0NoCode hdispatch hAccounts

theorem uniswapSyncBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩
  · exact uniswapSyncBodyRevert_locked hcode hsize hwv hsel hlocked hdispatch hAccounts
  · have hunlocked :
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
          ⟨1⟩ := by
      exact not_not.mp hlocked
    by_cases htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩
    · exact uniswapSyncBodyRevert_firstNoCode hcode hsize hperm hwv hsel
        hunlocked htoken0NoCode hdispatch hAccounts
    · sorry

end UniswapV2Pair
