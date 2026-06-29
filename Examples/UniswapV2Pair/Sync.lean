import Examples.UniswapV2Pair.SyncRuntime
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `sync()` source/ABI prefix -/

theorem uniswapDecode_sync {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (syncTransition.params.map Param.name)
      (transitionSignature syncTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
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

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source evaluator for
-- `uint32(block.timestamp % 2^32)`, parameterized by target width and modulus.
theorem evalExpr_sync_blockTimestamp (evm : EVM.State) (balance0 balance1 : UInt256) :
    evalExpr? config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm
      (u32 (.binary .mod now (.intLit twoPow32))) = .ok (syncBlockTimestampValue evm) := by
  unfold u32 now syncBlockTimestampValue syncBlockTimestampInt
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  norm_num [twoPow32, uint32Int]
  intro _hbad
  have hnonneg :
      0 ≤ Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
        (4294967296 : Int) := by
    exact Int.emod_nonneg _ (by norm_num)
  have hlt :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
          (4294967296 : Int) <
        4294967296 := by
    exact Int.emod_lt_of_pos _ (by norm_num)
  omega

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

abbrev syncUpdateBoundsBody : List Stmt :=
  [ .require (.binary .le (.var "balance0") (.intLit maxUint112)),
    .require (.binary .le (.var "balance1") (.intLit maxUint112)) ]

abbrev syncUpdateTimestampBody : List Stmt :=
  syncUpdateBoundsBody ++
    [ .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))) ]

abbrev syncUpdateRemainderBody : List Stmt :=
  [ .letDecl "blockTimestamp" (some uint32) (u32 (.binary .mod now (.intLit twoPow32))),
    .assign .storage reserve0Ref (.var "balance0"),
    .assign .storage reserve1Ref (.var "balance1"),
    .assign .storage blockTimestampLastRef (.var "blockTimestamp") ]

abbrev syncBalanceCallsBody : List Stmt :=
  pairBalanceOfThisStmts "balance0" "balance1"

abbrev syncToken0GuardTrue (evm : EVM.State) : Prop :=
  evalExpr? config { contract := contract, locals := ∅ } (uniswapLockEnteredState evm)
    (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true)

abbrev syncToken1GuardTrue (evm0 : EVM.State) (balance0 : Value) : Prop :=
  evalExpr? config { contract := contract, locals := (∅ : Store).insert "balance0" balance0 }
    evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true)

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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some balance1) :
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
      (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := ∅)
    hguard0 (by simp) hcall0
  simpa [syncBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfFirstCallDecodeRevert (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
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
      (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfFirstCallFailure evm evm0 hwv hunlocked hguard0 hcall0
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
      (true, evm0, out0))
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfSecondCallDecodeRevert
    evm evm0 evm1 hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  simpa [syncTransition, syncBalanceCallsBody, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncUpdateBoundsPrefix (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody ++ syncUpdateBoundsBody)
      (.ok { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1) := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  have hbounds :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        syncUpdateBoundsBody
        (.ok { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1) := by
    change ExecBlock config
      { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
      [ .require (.binary .le (.var "balance0") (.intLit maxUint112)),
        .require (.binary .le (.var "balance1") (.intLit maxUint112)) ]
      (.ok { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1)
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_sync_balance0_le_max_true evm1 balance0 balance1 hbound0))
      ?_
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_sync_balance1_le_max_true evm1 balance0 balance1 hbound1))
      ExecBlock.nil
  simpa [syncBalanceStore] using execBlock_append hbalances hbounds

theorem uniswapSyncFirstBoundFailureSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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

theorem uniswapSyncUpdateTimestampPrefix (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody ++ syncUpdateTimestampBody)
      (.ok { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
        evm1) := by
  have hprefix := uniswapSyncUpdateBoundsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := balance0) (balance1 := balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1 hbound0 hbound1
  have htimestamp :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        [ .letDecl "blockTimestamp" (some uint32)
            (u32 (.binary .mod now (.intLit twoPow32))) ]
        (.ok { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
          evm1) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_sync_blockTimestamp evm1 balance0 balance1))
      ExecBlock.nil
  simpa [syncUpdateTimestampBody, List.append_assoc] using execBlock_append hprefix htimestamp

theorem uniswapSyncUpdateReservesPrefix (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ∃ evm2 : EVM.State,
      ExecBlock config { contract := contract, locals := ∅ } evm
          (lockEnter ++ syncBalanceCallsBody ++
            updateReservesStmts (.var "balance0") (.var "balance1"))
          (.ok (syncAfterUpdateFrame balance0 balance1) evm2) := by
  sorry

theorem uniswapSyncSuccessSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ∃ evm2 : EVM.State,
      ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body
        (.ok (syncAfterUpdateFrame balance0 balance1) (uniswapLockExitedState evm2)) := by
  sorry

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

theorem uniswapSyncBodyReverts_firstCallFailure (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0)) :
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
      (true, evm0, out0))
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : syncToken1GuardTrue evm0 balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondBoundFailureSource evm evm0 evm1 hwv hunlocked hguard0 hcall0 hdec0
      hguard1 hcall1 hdec1 hbound0 hbound1)

theorem uniswapSyncBodyReturns (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ∃ evm2 : EVM.State,
      ExecTransitionBody config contract evm ∅ syncTransition.body
        (.returned
          (syncAfterUpdateFrame balance0 balance1)
          (uniswapLockExitedState evm2) none) := by
  sorry

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
  · sorry

end UniswapV2Pair
