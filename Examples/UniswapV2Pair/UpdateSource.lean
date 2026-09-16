import Examples.UniswapV2Pair.SyncRuntime
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `sync()` source/ABI prefix -/

private theorem valueInt_beq_false_of_ne {x y : Int} (h : x ≠ y) :
    (Value.int x == Value.int y) = false := by
  rw [beq_eq_false_iff_ne]
  intro hv
  cases hv
  exact h rfl

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

abbrev syncUpdateCallArgValsWith
    (balance0 balance1 reserve0 reserve1 : UInt256) : List Value :=
  [ uniswapUint256Value balance0,
    uniswapUint256Value balance1,
    .int (Int.ofNat reserve0.toNat),
    .int (Int.ofNat reserve1.toNat) ]

abbrev syncUpdateCallStore (evm : EVM.State) (balance0 balance1 : UInt256) : Store :=
  ((((∅ : Store).insert "_reserve1" (.int (Int.ofNat (uniswapReserve1Word evm).toNat))).insert
      "_reserve0" (.int (Int.ofNat (uniswapReserve0Word evm).toNat))).insert
      "balance1" (uniswapUint256Value balance1)).insert
      "balance0" (uniswapUint256Value balance0)

abbrev syncUpdateCallStoreWith
    (balance0 balance1 reserve0 reserve1 : UInt256) : Store :=
  ((((∅ : Store).insert "_reserve1" (.int (Int.ofNat reserve1.toNat))).insert
      "_reserve0" (.int (Int.ofNat reserve0.toNat))).insert
      "balance1" (uniswapUint256Value balance1)).insert
      "balance0" (uniswapUint256Value balance0)

abbrev syncUpdateCallFrame (evm : EVM.State) (balance0 balance1 : UInt256) : Frame :=
  { contract := contract, locals := syncUpdateCallStore evm balance0 balance1 }

abbrev syncUpdateCallFrameWith
    (balance0 balance1 reserve0 reserve1 : UInt256) : Frame :=
  { contract := contract, locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1 }

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

theorem syncUpdateCallStoreWith_balance0
    (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1).get? "balance0" =
      some (uniswapUint256Value balance0) := by
  rw [syncUpdateCallStoreWith, store_get_self]

theorem syncUpdateCallStoreWith_balance1
    (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1).get? "balance1" =
      some (uniswapUint256Value balance1) := by
  rw [syncUpdateCallStoreWith, store_get_ne _ _ (by decide), store_get_self]

theorem syncUpdateCallStoreWith_reserve0
    (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1).get? "_reserve0" =
      some (.int (Int.ofNat reserve0.toNat)) := by
  rw [syncUpdateCallStoreWith, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem syncUpdateCallStoreWith_reserve1
    (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1).get? "_reserve1" =
      some (.int (Int.ofNat reserve1.toNat)) := by
  rw [syncUpdateCallStoreWith, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

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
  have hb0 : decide (Int.ofNat balance0.toNat ≤ maxUint112) = true :=
    decide_eq_true hbound0
  have hb1 : decide (Int.ofNat balance1.toNat ≤ maxUint112) = true :=
    decide_eq_true hbound1
  simp only [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?, pure, hb0, hb1]

theorem evalExpr_sync_update_bounds_true_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    evalExpr? config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1) evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStoreWith_balance0, syncUpdateCallStoreWith_balance1]
  have hb0 : decide (Int.ofNat balance0.toNat ≤ maxUint112) = true :=
    decide_eq_true hbound0
  have hb1 : decide (Int.ofNat balance1.toNat ≤ maxUint112) = true :=
    decide_eq_true hbound1
  simp only [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?, pure, hb0, hb1]

theorem evalExpr_sync_update_bounds_false_first (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool false) := by
  have hnot : ¬ Int.ofNat balance0.toNat ≤ maxUint112 := by omega
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance0, syncUpdateCallStore_balance1]
  have hb0 : decide (Int.ofNat balance0.toNat ≤ maxUint112) = false :=
    decide_eq_false hnot
  simp only [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?, pure, hb0]

theorem evalExpr_sync_update_bounds_false_first_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    evalExpr? config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1)
      evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool false) := by
  have hnot : ¬ Int.ofNat balance0.toNat ≤ maxUint112 := by omega
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStoreWith_balance0, syncUpdateCallStoreWith_balance1]
  have hb0 : decide (Int.ofNat balance0.toNat ≤ maxUint112) = false :=
    decide_eq_false hnot
  simp only [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?, pure, hb0]

theorem evalExpr_sync_update_bounds_false_second (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    evalExpr? config (syncUpdateCallFrame evm balance0 balance1) evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStore_balance0, syncUpdateCallStore_balance1]
  have hb0 : decide (Int.ofNat balance0.toNat ≤ maxUint112) = true :=
    decide_eq_true hbound0
  have hb1 : decide (Int.ofNat balance1.toNat ≤ maxUint112) = false :=
    decide_eq_false (by omega)
  simp only [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?, pure, hb0, hb1]

theorem evalExpr_sync_update_bounds_false_second_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    evalExpr? config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1)
      evm
      (.binary .and
        (.binary .le (.var "balance0") (.intLit maxUint112))
        (.binary .le (.var "balance1") (.intLit maxUint112))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [syncUpdateCallStoreWith_balance0, syncUpdateCallStoreWith_balance1]
  have hb0 : decide (Int.ofNat balance0.toNat ≤ maxUint112) = true :=
    decide_eq_true hbound0
  have hb1 : decide (Int.ofNat balance1.toNat ≤ maxUint112) = false :=
    decide_eq_false (by omega)
  simp only [EvalResult.ofOption, uniswapUint256Value, evalBinaryOp?, pure, hb0, hb1]

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

theorem bindParams_sync_update_call_with
    (balance0 balance1 reserve0 reserve1 : UInt256) :
    bindParams? updateFunction.params
        (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1) =
      some (syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1) := by
  simp [bindParams?, updateFunction, syncUpdateCallArgValsWith, syncUpdateCallStoreWith]

theorem uniswapUpdateFunctionReverts_firstBound
    (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    ExecFuncBody config (syncUpdateCallFrame evm balance0 balance1) evm
      updateFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_sync_update_bounds_false_first evm balance0 balance1 hbound)))

theorem uniswapUpdateFunctionReverts_firstBound_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    ExecFuncBody config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1) evm
      updateFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_sync_update_bounds_false_first_with
          evm balance0 balance1 reserve0 reserve1 hbound)))

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

theorem uniswapUpdateFunctionReverts_secondBound_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecFuncBody config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1) evm
      updateFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_sync_update_bounds_false_second_with
          evm balance0 balance1 reserve0 reserve1 hbound0 hbound1)))

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

abbrev syncUpdateBlockTimestampStoreWith
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) : Store :=
  (syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1).insert "blockTimestamp"
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

abbrev syncUpdateTimeElapsedStoreWith
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) : Store :=
  (syncUpdateBlockTimestampStoreWith evm balance0 balance1 reserve0 reserve1).insert
    "timeElapsed" (syncTimeElapsedValue evm)

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

theorem syncUpdateBlockTimestampStoreWith_balance0
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateBlockTimestampStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "balance0" = some (uniswapUint256Value balance0) := by
  rw [syncUpdateBlockTimestampStoreWith, store_get_ne _ _ (by decide),
    syncUpdateCallStoreWith_balance0]

theorem syncUpdateBlockTimestampStoreWith_balance1
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateBlockTimestampStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "balance1" = some (uniswapUint256Value balance1) := by
  rw [syncUpdateBlockTimestampStoreWith, store_get_ne _ _ (by decide),
    syncUpdateCallStoreWith_balance1]

theorem syncUpdateBlockTimestampStoreWith_blockTimestamp
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateBlockTimestampStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "blockTimestamp" = some (syncBlockTimestampValue evm) := by
  rw [syncUpdateBlockTimestampStoreWith, store_get_self]

theorem syncUpdateBlockTimestampStore_blockTimestampLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateBlockTimestampStore evm balance0 balance1).get? "blockTimestampLast" =
      none := by
  rw [syncUpdateBlockTimestampStore, store_get_ne _ _ (by decide)]
  simp [syncUpdateCallStore]

theorem syncUpdateBlockTimestampStoreWith_blockTimestampLast_none
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateBlockTimestampStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "blockTimestampLast" = none := by
  rw [syncUpdateBlockTimestampStoreWith, store_get_ne _ _ (by decide)]
  simp [syncUpdateCallStoreWith]

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

theorem syncUpdateTimeElapsedStoreWith_balance0
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "balance0" = some (uniswapUint256Value balance0) := by
  rw [syncUpdateTimeElapsedStoreWith, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStoreWith_balance0]

theorem syncUpdateTimeElapsedStoreWith_balance1
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "balance1" = some (uniswapUint256Value balance1) := by
  rw [syncUpdateTimeElapsedStoreWith, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStoreWith_balance1]

theorem syncUpdateTimeElapsedStoreWith_blockTimestamp
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "blockTimestamp" = some (syncBlockTimestampValue evm) := by
  rw [syncUpdateTimeElapsedStoreWith, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStoreWith_blockTimestamp]

theorem syncUpdateTimeElapsedStoreWith_timeElapsed
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "timeElapsed" = some (syncTimeElapsedValue evm) := by
  rw [syncUpdateTimeElapsedStoreWith, store_get_self]

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

theorem syncUpdateTimeElapsedStoreWith_reserve0
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
  rw [syncUpdateTimeElapsedStoreWith, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStoreWith, store_get_ne _ _ (by decide),
    syncUpdateCallStoreWith_reserve0]

theorem syncUpdateTimeElapsedStoreWith_reserve1
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
  rw [syncUpdateTimeElapsedStoreWith, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStoreWith, store_get_ne _ _ (by decide),
    syncUpdateCallStoreWith_reserve1]

theorem syncUpdateTimeElapsedStore_reserve0_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "reserve0" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem syncUpdateTimeElapsedStore_reserve1_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "reserve1" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem syncUpdateTimeElapsedStoreWith_reserve0_none
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get? "reserve0" =
      none := by
  simp [syncUpdateTimeElapsedStoreWith, syncUpdateBlockTimestampStoreWith,
    syncUpdateCallStoreWith]

theorem syncUpdateTimeElapsedStoreWith_reserve1_none
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get? "reserve1" =
      none := by
  simp [syncUpdateTimeElapsedStoreWith, syncUpdateBlockTimestampStoreWith,
    syncUpdateCallStoreWith]

theorem syncUpdateTimeElapsedStore_blockTimestampLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "blockTimestampLast" = none := by
  rw [syncUpdateTimeElapsedStore, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStore_blockTimestampLast_none]

theorem syncUpdateTimeElapsedStoreWith_blockTimestampLast_none
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "blockTimestampLast" = none := by
  rw [syncUpdateTimeElapsedStoreWith, store_get_ne _ _ (by decide),
    syncUpdateBlockTimestampStoreWith_blockTimestampLast_none]

theorem syncUpdateTimeElapsedStore_price0CumulativeLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "price0CumulativeLast" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem syncUpdateTimeElapsedStore_price1CumulativeLast_none
    (evm : EVM.State) (balance0 balance1 : UInt256) :
    (syncUpdateTimeElapsedStore evm balance0 balance1).get? "price1CumulativeLast" = none := by
  simp [syncUpdateTimeElapsedStore, syncUpdateBlockTimestampStore, syncUpdateCallStore]

theorem syncUpdateTimeElapsedStoreWith_price0CumulativeLast_none
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "price0CumulativeLast" = none := by
  simp [syncUpdateTimeElapsedStoreWith, syncUpdateBlockTimestampStoreWith,
    syncUpdateCallStoreWith]

theorem syncUpdateTimeElapsedStoreWith_price1CumulativeLast_none
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    (syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1).get?
        "price1CumulativeLast" = none := by
  simp [syncUpdateTimeElapsedStoreWith, syncUpdateBlockTimestampStoreWith,
    syncUpdateCallStoreWith]

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

theorem evalExpr_sync_update_blockTimestamp_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    evalExpr? config (syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1) evm
      (u32 (.binary .mod now (.intLit twoPow32))) = .ok (syncBlockTimestampValue evm) := by
  simpa [u32, now, syncBlockTimestampValue, syncBlockTimestampInt, twoPow32, uint32Int] using
    evalExpr_timestampModUint32
      (cfg := config)
      (solm := syncUpdateCallFrameWith balance0 balance1 reserve0 reserve1) evm

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

theorem evalExpr_sync_update_timeElapsed_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateBlockTimestampStoreWith evm balance0 balance1 reserve0 reserve1 }
      evm
      (u32 (.binary .mod
        (.binary .add
          (.binary .sub (.var "blockTimestamp") (.storage blockTimestampLastRef))
          (.intLit twoPow32))
        (.intLit twoPow32))) = .ok (syncTimeElapsedValue evm) := by
  unfold u32 syncTimeElapsedValue syncTimeElapsedInt
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind,
    syncUpdateBlockTimestampStoreWith_blockTimestamp,
    evalExpr_sync_blockTimestampLast evm
      (syncUpdateBlockTimestampStoreWith evm balance0 balance1 reserve0 reserve1)
      (syncUpdateBlockTimestampStoreWith_blockTimestampLast_none evm balance0 balance1
        reserve0 reserve1)]
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
  simp [evalBinaryOp?, pure]

theorem evalExpr_sync_update_condition_false_elapsed_zero_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (helapsed : syncTimeElapsedInt evm = 0) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
      evm
      (.binary .and
        (.binary .gt (.var "timeElapsed") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "_reserve0") (.intLit 0))
          (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStoreWith_timeElapsed, syncUpdateTimeElapsedStoreWith_reserve0,
    syncUpdateTimeElapsedStoreWith_reserve1]
  unfold syncTimeElapsedValue
  rw [helapsed]
  simp [evalBinaryOp?, pure]

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
  by_cases helapsed : 0 < syncTimeElapsedInt evm
  · have htime : decide (0 < syncTimeElapsedInt evm) = true := decide_eq_true helapsed
    simp only [evalBinaryOp?, pure, syncTimeElapsedInt, htime, hreserve0]
    rfl
  · have htime : decide (0 < syncTimeElapsedInt evm) = false := decide_eq_false helapsed
    simp only [evalBinaryOp?, pure, syncTimeElapsedInt, htime]

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
  by_cases helapsed : 0 < syncTimeElapsedInt evm
  · have htime : decide (0 < syncTimeElapsedInt evm) = true := decide_eq_true helapsed
    by_cases hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat = 0
    · simp only [evalBinaryOp?, pure, syncTimeElapsedInt, htime, hreserve0, hreserve1]
      rfl
    · have hne0 :
          (Value.int (Int.ofNat (uniswapReserve0Word evm).toNat) == Value.int 0) = false :=
        valueInt_beq_false_of_ne hreserve0
      simp only [evalBinaryOp?, pure, syncTimeElapsedInt, htime, hreserve1, hne0]
      rfl
  · have htime : decide (0 < syncTimeElapsedInt evm) = false := decide_eq_false helapsed
    simp only [evalBinaryOp?, pure, syncTimeElapsedInt, htime]

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
  have htime : decide (0 < syncTimeElapsedInt evm) = true := decide_eq_true helapsed
  have hne0 :
      (Value.int (Int.ofNat (uniswapReserve0Word evm).toNat) == Value.int 0) = false :=
    valueInt_beq_false_of_ne hreserve0
  have hne1 :
      (Value.int (Int.ofNat (uniswapReserve1Word evm).toNat) == Value.int 0) = false :=
    valueInt_beq_false_of_ne hreserve1
  simp only [evalBinaryOp?, pure, syncTimeElapsedInt, htime, hne0, hne1]
  rfl

theorem evalExpr_sync_update_condition_true_with
    (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat reserve0.toNat ≠ 0)
    (hreserve1 : Int.ofNat reserve1.toNat ≠ 0) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
      evm
      (.binary .and
        (.binary .gt (.var "timeElapsed") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "_reserve0") (.intLit 0))
          (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStoreWith_timeElapsed, syncUpdateTimeElapsedStoreWith_reserve0,
    syncUpdateTimeElapsedStoreWith_reserve1]
  unfold syncTimeElapsedValue
  have htime : decide (0 < syncTimeElapsedInt evm) = true := decide_eq_true helapsed
  have hne0 :
      (Value.int (Int.ofNat reserve0.toNat) == Value.int 0) = false :=
    valueInt_beq_false_of_ne hreserve0
  have hne1 :
      (Value.int (Int.ofNat reserve1.toNat) == Value.int 0) = false :=
    valueInt_beq_false_of_ne hreserve1
  simp only [evalBinaryOp?, pure, syncTimeElapsedInt, htime, hne0, hne1]
  rfl

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

theorem evalExpr_sync_update_u112_balance0_with
    (evm evalEvm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound : Int.ofNat balance0.toNat ≤ maxUint112) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
      evalEvm (u112 (.var "balance0")) = .ok (uniswapUint256Value balance0) := by
  have hltInt : Int.ofNat balance0.toNat < Int.ofNat (2 ^ 112) := by
    norm_num [maxUint112] at hbound ⊢
    omega
  unfold u112 uniswapUint256Value
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStoreWith_balance0]
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

theorem evalExpr_sync_update_u112_balance1_with
    (evm evalEvm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbound : Int.ofNat balance1.toNat ≤ maxUint112) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 }
      evalEvm (u112 (.var "balance1")) = .ok (uniswapUint256Value balance1) := by
  have hltInt : Int.ofNat balance1.toNat < Int.ofNat (2 ^ 112) := by
    norm_num [maxUint112] at hbound ⊢
    omega
  unfold u112 uniswapUint256Value
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [syncUpdateTimeElapsedStoreWith_balance1]
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

theorem evalExpr_sync_update_blockTimestamp_var_with
    (evm timestampEvm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256) :
    evalExpr? config
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith timestampEvm balance0 balance1 reserve0
          reserve1 }
      evm (.var "blockTimestamp") = .ok (syncBlockTimestampValue timestampEvm) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [syncUpdateTimeElapsedStoreWith_blockTimestamp]

theorem syncBlockTimestampValue_eq_updateTimestampWord (evm : EVM.State) :
    syncBlockTimestampValue evm =
      uniswapUint256Value (uniswapUpdateTimestampWord evm.executionEnv) := by
  unfold syncBlockTimestampValue syncBlockTimestampInt uniswapUint256Value uint256Value
  unfold uniswapUpdateTimestampWord
  rw [u256_land_toNat]
  have hmask : reserve32Mask.toNat = 2 ^ 32 - 1 := by native_decide
  rw [hmask, nat_land_comm, nat_land_mask_eq_mod]
  have hsmall :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat % 2 ^ 32 < UInt256.size := by
    exact lt_trans (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 32))
      (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hsmall]
  norm_num [twoPow32]

theorem uint32MaskedSub_toInt (a b : UInt256)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    Int.ofNat (UInt256.land (UInt256.sub a b) reserve32Mask).toNat =
      (Int.ofNat a.toNat - Int.ofNat b.toNat + twoPow32) % twoPow32 := by
  by_cases hle : b.toNat ≤ a.toNat
  · rw [u256_land_toNat]
    rw [usub_toNat hle]
    have hmask : reserve32Mask.toNat = 2 ^ 32 - 1 := by native_decide
    rw [hmask, nat_land_mask_eq_mod]
    have hlt : a.toNat - b.toNat < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    rw [Nat.mod_eq_of_lt (by
      norm_num [UInt256.size]
      omega)]
    rw [show Int.ofNat a.toNat - Int.ofNat b.toNat + twoPow32 =
      Int.ofNat (a.toNat - b.toNat) + twoPow32 by
        norm_num [twoPow32]
        omega]
    rw [Int.add_emod_right]
    have hnonneg : (0 : Int) ≤ Int.ofNat (a.toNat - b.toNat) := Int.natCast_nonneg _
    have hsmall : Int.ofNat (a.toNat - b.toNat) < twoPow32 := by
      norm_num [twoPow32]
      omega
    exact (Int.emod_eq_of_lt hnonneg hsmall).symm
  · have hltba : a.toNat < b.toNat := by omega
    rw [u256_land_toNat]
    rw [usub_toNat_underflow hltba]
    have hmask : reserve32Mask.toNat = 2 ^ 32 - 1 := by native_decide
    rw [hmask, nat_land_mask_eq_mod]
    have hsplit :
        UInt256.size + a.toNat - b.toNat =
          (UInt256.size - 2 ^ 32) + (2 ^ 32 + a.toNat - b.toNat) := by
      norm_num [UInt256.size]
      omega
    rw [hsplit]
    have hleft : (UInt256.size - 2 ^ 32) % 2 ^ 32 = 0 := by
      norm_num [UInt256.size]
    have hrightLt : 2 ^ 32 + a.toNat - b.toNat < 2 ^ 32 := by omega
    rw [Nat.add_mod, hleft, Nat.mod_eq_of_lt hrightLt]
    simp only [zero_add]
    rw [Nat.mod_eq_of_lt hrightLt]
    rw [Nat.mod_eq_of_lt (by
      norm_num [UInt256.size]
      omega)]
    rw [show Int.ofNat a.toNat - Int.ofNat b.toNat + twoPow32 =
      Int.ofNat (2 ^ 32 + a.toNat - b.toNat) by
        norm_num [twoPow32]
        omega]
    have hnonneg : (0 : Int) ≤ Int.ofNat (2 ^ 32 + a.toNat - b.toNat) :=
      Int.natCast_nonneg _
    have hsmall : Int.ofNat (2 ^ 32 + a.toNat - b.toNat) < twoPow32 := by
      norm_num [twoPow32]
      omega
    exact (Int.emod_eq_of_lt hnonneg hsmall).symm

theorem syncBlockTimestampInt_eq_updateTimestampWord_toNat (evm : EVM.State) :
    syncBlockTimestampInt evm =
      Int.ofNat (uniswapUpdateTimestampWord evm.executionEnv).toNat := by
  have h := syncBlockTimestampValue_eq_updateTimestampWord evm
  simpa [syncBlockTimestampValue, uniswapUint256Value, uint256Value] using h

theorem syncTimeElapsedInt_eq_updateElapsedWord_toNat (evm : EVM.State) :
    syncTimeElapsedInt evm =
      Int.ofNat
        (UInt256.land
          (uniswapUpdateElapsedWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
            evm.executionEnv)
          reserve32Mask).toNat := by
  rw [syncTimeElapsedInt]
  rw [syncBlockTimestampInt_eq_updateTimestampWord_toNat evm]
  symm
  have ha : (uniswapUpdateTimestampWord evm.executionEnv).toNat < 2 ^ 32 := by
    simpa [uniswapUpdateTimestampWord, u256_land_comm] using
      uniswapUint32Masked_lt (UInt256.ofNat evm.executionEnv.header.timestamp)
  have hb : (syncBlockTimestampLastWord evm).toNat < 2 ^ 32 := by
    simpa [syncBlockTimestampLastWord, u256_land_comm] using
      uniswapUint32Masked_lt
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
          reserve224Shift)
  have hsub :=
    uint32MaskedSub_toInt (uniswapUpdateTimestampWord evm.executionEnv)
      (syncBlockTimestampLastWord evm) ha hb
  simpa [syncBlockTimestampLastWord, uniswapUpdateElapsedWord, u256_land_comm] using hsub

abbrev syncUpdatePackedReserveState
    (evm : EVM.State) (balance0 balance1 : UInt256) : EVM.State :=
  let evm0 :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) balance0)
  let evm1 :=
    Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨8⟩
      (setUint112Offset14Word
        (Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩) balance1)
  Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner ⟨8⟩
    (setUint32Offset28Word
      (Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨8⟩)
      (uniswapUpdateTimestampWord evm.executionEnv))

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

end UniswapV2Pair
