import Examples.UniswapV2Pair.SyncCumulative

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
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
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
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
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
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
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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

theorem uniswapSyncBodyReturns_conditionFalse_packed (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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
    ExecTransitionBody config contract evm ∅ syncTransition.body
      (.returned (syncAfterUpdateFrame balance0 balance1)
        (uniswapLockExitedState (syncUpdatePackedReserveState evm1 balance0 balance1))
        none) := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  have hupdateStmt :=
    uniswapSyncUpdateCallReturns_conditionFalse_packed evm1 balance0 balance1
      hbound0 hbound1 hcond
  have hupdateBlock :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        (updateReservesStmts (.var "balance0") (.var "balance1"))
        (.ok (syncAfterUpdateFrame balance0 balance1)
          (syncUpdatePackedReserveState evm1 balance0 balance1)) := by
    simpa [updateReservesStmts] using
      (ExecBlock.consNormal hupdateStmt ExecBlock.nil)
  have hlock :=
    uniswapLockExitSuffix (syncUpdatePackedReserveState evm1 balance0 balance1)
      (syncAfterUpdateStore balance0 balance1)
      (by simp [syncAfterUpdateStore, syncBalanceStore, uniswapBalanceOfStore])
  have htail := execBlock_append hupdateBlock hlock
  have hbody := execBlock_append hbalances htail
  exact ExecFuncBody.execBlockOK
    (by
      simpa [syncTransition, syncBalanceCallsBody, updateReservesStmts, List.append_assoc]
        using hbody)

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
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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
      some (uniswapUint256Value balance0))
    (hguard1 : syncToken1GuardTrue evm0 (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
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

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` first `balanceOf` slice for the call-depth limit.

At depth 1024 the `STATICCALL` is not made, pushes status `0`, and the high-level
call-success guard reverts. -/
theorem uniswapSyncRuntimeFirstBalanceOfStaticcallDepthReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ}
    {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (rd6175 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6175⟩
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (hdepth : I.depth = 1024)
    (hovStatic : t.length + 1 ≤ 1024)
    (hovGuard : t.length + 5 ≤ 1024) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd6176⟩ :=
    RD.uniswapStaticcallDepthLimit rd6175 (by native_decide) hdepth hovStatic
  have rdRev :=
    RD.uniswapCallSuccessGuardMissing (okPc := ⟨6192⟩) rd6176 rfl
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by decide)
      hovGuard
  simpa using rdRev

theorem uniswapSyncBodyCoreRevert_firstCallDepth
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (syncTransition.params.map Param.name)
        (transitionSignature syncTransition).paramTypes I.calldata = some ∅)
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let target := EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)
  have hunlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
    have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
    simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using (hword ▸ hunlocked)
  have hguard0 : syncToken0GuardTrue evmS :=
    syncToken0GuardTrue_initState_of_code hAccounts htoken0Code
  have hdepthSolm : evmL.executionEnv.depth = 1024 := by
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using hdepth
  have hcall0 : typedCallViaEVM config evmL target "balanceOf" 0
      [.address evmL.executionEnv.codeOwner]
      (false, { evmL with substate := (evmL.addAccessedAccount target).substate },
        ByteArray.empty) false := by
    exact callNotMade_depthLimit
      (cfg := config) (evm := evmL) (tgt := target)
      (name := "balanceOf") (args := [.address evmL.executionEnv.codeOwner])
      (callPerm := false)
      (balanceOfThisCalldataMem_encode evmL.executionEnv.codeOwner)
      hdepthSolm
  have hbody :
      ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
    exact uniswapSyncBodyReverts_firstCallFailure evmS
      { evmL with substate := (evmL.addAccessedAccount target).substate }
      (by simp only [evmS, initState]; exact hwv)
      hunlockedSolm hguard0 hcall0
  exact hRuntime.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSyncBodyRevert_firstCallDepth
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some syncTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    obtain ⟨_, _, _, rd6175⟩ :=
      uniswapSyncRuntimeFirstBalanceOfStaticcallEntry
        (g := g) hcode hsize hwv hsel hperm hunlocked htoken0Code
    exact uniswapSyncRuntimeFirstBalanceOfStaticcallDepthReverts
      rd6175 hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩ rfl hsel
  exact uniswapSyncBodyCoreRevert_firstCallDepth hcode hwv hdepth hunlocked
    htoken0Code hdispatch (uniswapDecode_sync hsz4) hRuntime hAccounts

theorem syncToken1GuardFalse_of_noCode {σ : AccountMap}
    {evm0 : EVM.State} {I : ExecutionEnv} {balance0 : Value}
    (hPost : accountMapEquiv σ evm0.accountMap)
    (henv : evm0.executionEnv = I)
    (htoken1NoCode :
      uniswapExtCodeSizeWord σ (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ I)) =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store).insert "balance0" balance0 }
      evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
        .ok (.bool false) := by
  let token1WordS := uniswapSlotWord ⟨7⟩ σ I
  let token1WordE := uniswapSlotWord ⟨7⟩ evm0.accountMap evm0.executionEnv
  have hslot : token1WordS = token1WordE := by
    have hword := accountMapEquiv_storage_findD hPost I.codeOwner ⟨7⟩ ⟨0⟩
    simpa [token1WordS, token1WordE, uniswapSlotWord, henv] using hword
  have hcodeEvm :
      uniswapExtCodeSizeWord evm0.accountMap (UInt256.land solcAddrMask token1WordE) =
        ⟨0⟩ := by
    have hsame :=
      uniswapExtCodeSizeWord_accountMapEquiv hPost (UInt256.land solcAddrMask token1WordS)
    rw [← hslot]
    rw [← hsame]
    simpa [token1WordS] using htoken1NoCode
  have hstorage :
      evalExpr? config { contract := contract, locals := (∅ : Store).insert "balance0" balance0 }
        evm0 (.storage token1Ref) = .ok (.address (uniswapAddressAtSlot evm0 ⟨7⟩)) := by
    exact evalExpr_uniswap_storage_address evm0 ((∅ : Store).insert "balance0" balance0)
      (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (by rw [store_get_ne _ _ (by decide)]; simp)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hcodeSource :
      (evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) =
        ⟨0⟩ := by
    have hcodeEvmRight :
        uniswapExtCodeSizeWord evm0.accountMap (UInt256.land token1WordE solcAddrMask) =
          ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeEvm
    simpa [State.lookupAccount, Solm.EVM.storageLoad, Account.lookupStorage,
      uniswapAddressAtSlot, uniswapExtCodeSizeWord, uniswapSlotWord, token1WordE,
      accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeEvmRight
  have hcodeSourceWord :
      EVM.Word.ofNat
          ((evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩)).option 0
            (fun acc => acc.code.size)) =
        ⟨0⟩ := by
    cases hacc : evm0.lookupAccount (uniswapAddressAtSlot evm0 ⟨7⟩) with
    | none =>
        exact UInt256_ofNat_0
    | some acc =>
        simpa [hacc, Option.option] using hcodeSource
  change
    evalExpr? config { contract := contract, locals := (∅ : Store).insert "balance0" balance0 }
      evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
        .ok (.bool false)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hcodeSourceWord]

theorem uniswapSyncBalanceOfSecondCallNoCode (evm evm0 : EVM.State)
    {out0 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := ((∅ : Store).insert "balance0" (uniswapUint256Value balance0)) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++ syncBalanceCallsBody) .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisSecondCallNoCode
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := ∅)
    (balance0 := uniswapUint256Value balance0)
    hguard0 hguard1 (by simp) hcall0 hdec0
  simpa [syncBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSyncSecondCallNoCodeSource (evm evm0 : EVM.State)
    {out0 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := ((∅ : Store).insert "balance0" (uniswapUint256Value balance0)) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix :=
    uniswapSyncBalanceOfSecondCallNoCode evm evm0 hwv hunlocked hguard0 hcall0 hdec0 hguard1
  simpa [syncTransition, syncBalanceCallsBody, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncBodyReverts_secondNoCode (evm evm0 : EVM.State)
    {out0 : ByteArray} {balance0 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : syncToken0GuardTrue evm)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := ((∅ : Store).insert "balance0" (uniswapUint256Value balance0)) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondCallNoCodeSource evm evm0 hwv hunlocked hguard0 hcall0 hdec0 hguard1)

set_option maxRecDepth 100000000 in
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
    · by_cases hdepth : I.depth.val < 1024
      · obtain ⟨cA', σ', z, o, A_in, callGas, _kExt, _CExt, hΘ, rd6176,
            hsecondExt, hoSize⟩ :=
          uniswapSyncRuntimeSecondBalanceOfExtcodesize
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hsize hwv hsel hperm hdepth
            hunlocked htoken0NoCode
        have hrev :
            z = false →
              RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
          intro hz
          have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
            simp [hz]
          exact RD.uniswapCallSuccessGuardMissing (okPc := ⟨6192⟩) rd6176 hstatus
            (by native_decide) (by native_decide) (by native_decide) (by native_decide)
            (by native_decide) (by native_decide) (by native_decide)
            (by native_decide) (by native_decide) (by native_decide) (by native_decide)
            (by native_decide) hoSize
            (by simp only [List.length_cons, List.length_nil]; omega)
        have hrevShort :
            z = true → o.size < 32 →
              RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
          intro hz hshort
          have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
            rw [hz]
            decide
          obtain ⟨_, _, rd6194⟩ :=
            RD.uniswapCallSuccessGuardOk (okPc := ⟨6192⟩) rd6176 hstatus
              (by native_decide) (by native_decide) (by native_decide) (by native_decide)
              (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
              (by simp only [List.length_cons, List.length_nil]; omega)
          exact RD.uniswapBalanceOfReturnWordDecodeShortReverts
            (pc := ⟨6194⟩) (okPc := ⟨6214⟩) (self := UInt256.ofNat I.codeOwner.val)
            rd6194 hshort hoSize
            (by native_decide) (by native_decide) (by native_decide) (by native_decide)
            (by native_decide) (by native_decide) (by native_decide) (by native_decide)
            (by native_decide) (by native_decide) (by native_decide) (by native_decide)
            (by native_decide) (by native_decide) (by native_decide)
            (by simp only [List.length_cons, List.length_nil]; omega)
        obtain ⟨evm0S, hcallAll, hPostAccounts0, hcreated0, hσ0, hgenesis0,
            hblocks0, henv0⟩ :=
          uniswapSkimFirstBalanceTypedCall_source
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (cA' := cA') (σ' := σ') (z := z) (o := o)
            (A_in := A_in) (callGas := callGas) hAccounts hdepth hΘ
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have henv0I : evm0S.executionEnv = I := by
          simpa [evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
            storageStore_executionEnv] using henv0
        have hunlockedSolm :
            Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
          have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
          simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage] using (hword ▸ hunlocked)
        have hguard0 : syncToken0GuardTrue evmS :=
          syncToken0GuardTrue_initState_of_code hAccounts htoken0NoCode
        have hsz4 : 4 ≤ I.calldata.size :=
          calldata_size_ge_of_selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩ rfl hsel
        by_cases hz : z = false
        · exact (hrev hz).reEquivExecutionRevert hcode hdispatch
            (uniswapDecode_sync hsz4) (by
              have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                  (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                  "balanceOf" 0
                  [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                  (false, evm0S, o) false := by
                simpa [evmS, hz] using hcallAll
              exact uniswapSyncBodyReverts_firstCallFailure evmS evm0S
                (by simp only [evmS, initState]; exact hwv)
                hunlockedSolm hguard0 hcall0)
        · by_cases hshort : o.size < 32
          · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
            have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                "balanceOf" 0
                [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                (true, evm0S, o) false := by
              simpa [evmS, hzTrue] using hcallAll
            have hdec0 : config.externalABI.decode? "balanceOf" o = none := by
              change uniswapExternalABI.decode? "balanceOf" o = none
              simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                (decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o)
                  hshort)
            have hbody :
                ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
              exact uniswapSyncBodyReverts_firstCallDecode evmS evm0S
                (by simp only [evmS, initState]; exact hwv)
                hunlockedSolm hguard0 hcall0 hdec0
            exact (hrevShort hzTrue hshort).reEquivExecutionRevert hcode hdispatch
              (uniswapDecode_sync hsz4) hbody
          · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
            have ho32 : 32 ≤ o.size := not_lt.mp hshort
            let balance0 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
            have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                "balanceOf" 0
                [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                (true, evm0S, o) false := by
              simpa [evmS, hzTrue] using hcallAll
            have hdec0 :
                config.externalABI.decode? "balanceOf" o =
                  some (uniswapUint256Value balance0) := by
              simpa [balance0, skimBalanceValue, uniswapUint256Value] using
                uniswapSkimBalanceOfDecode_ok (returndata := o) ho32
            obtain ⟨_, _, rd6279⟩ := hsecondExt hzTrue ho32
            by_cases htoken1NoCode :
              uniswapExtCodeSizeWord σ'
                (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) = ⟨0⟩
            · have rdRev :=
                RD.uniswapExtcodesizeGuardMissing (okPc := ⟨6291⟩) rd6279 htoken1NoCode
                  (by native_decide) (by native_decide) (by native_decide)
                  (by native_decide) (by native_decide) (by native_decide)
                  (by native_decide) (by native_decide) (by native_decide)
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hguard1 :
                  evalExpr? config
                    { contract := contract,
                      locals := ((∅ : Store).insert "balance0"
                        (uniswapUint256Value balance0)) } evm0S
                    (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
                      .ok (.bool false) := by
                exact syncToken1GuardFalse_of_noCode hPostAccounts0 henv0I htoken1NoCode
              have hbody :
                  ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
                exact uniswapSyncBodyReverts_secondNoCode evmS evm0S
                  (by simp only [evmS, initState]; exact hwv)
                  hunlockedSolm hguard0 hcall0 hdec0 hguard1
              exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_sync hsz4) hbody
            · have hguard1 :
                  syncToken1GuardTrue evm0S (uniswapUint256Value balance0) :=
                syncToken1GuardTrue_of_code hPostAccounts0 henv0I htoken1NoCode
              obtain ⟨_, _, _, rd6294⟩ :=
                RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨6291⟩) rd6279 htoken1NoCode
                  (by native_decide) (by native_decide) (by native_decide)
                  (by native_decide) (by native_decide) (by native_decide)
                  (by jump_dest) (by native_decide) (by native_decide)
                  (by native_decide)
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, _, _, hΘ1, rd6295,
                  ho1Size⟩ :=
                RD.uniswapStaticcall rd6294 (by native_decide) hdepth
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨evm1S, hcall1All, hPostAccounts1, hcreated1, hσ01,
                  hgenesis1, hblocks1, henv1⟩ :=
                uniswapSyncSecondBalanceTypedCall_source
                  (cA1 := cA') (gh := gh) (bl := bl) (σ1 := σ') (σ₀ := σ₀)
                  (I := I) (evm0S := evm0S) (cA2 := cA'') (σ2 := σ'')
                  (z2 := z1) (out2 := o1) (A_in2 := A_in1)
                  (callGas2 := callGas1) (o := o)
                  hPostAccounts0 hcreated0 hσ0 hgenesis0 hblocks0 henv0I hdepth
                  ho32 hoSize
                  (by simpa [balanceOfThisRebuiltStaticcallMem, initState] using hΘ1)
              have hsecondGuards :=
                uniswapSyncRuntimeSecondBalanceOfStaticcallFailureGuard
                  (hprevlo := ho32) (hprevhi := hoSize) (rd6295 := rd6295)
                  (ho1Size := ho1Size)
                  (hov := by simp only [List.length_cons, List.length_nil]; omega)
              by_cases hz1 : z1 = false
              · have hcall1 : typedCallViaEVM config evm0S
                    (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
                    [.address evm0S.executionEnv.codeOwner] (false, evm1S, o1) false := by
                  simpa [hz1] using hcall1All
                have hbody :
                    ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
                  exact uniswapSyncBodyReverts_secondCallFailure evmS evm0S evm1S
                    (by simp only [evmS, initState]; exact hwv)
                    hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1
                exact (hsecondGuards.1 hz1).reEquivExecutionRevert hcode hdispatch
                  (uniswapDecode_sync hsz4) hbody
              · by_cases hshort1 : o1.size < 32
                · have hz1True : z1 = true := Bool.eq_true_of_not_eq_false hz1
                  have hcall1 : typedCallViaEVM config evm0S
                      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
                      [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false := by
                    simpa [hz1True] using hcall1All
                  have hdec1 : config.externalABI.decode? "balanceOf" o1 = none := by
                    change uniswapExternalABI.decode? "balanceOf" o1 = none
                    simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                      (decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o1)
                        hshort1)
                  have hbody :
                      ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
                    exact uniswapSyncBodyReverts_secondCallDecode evmS evm0S evm1S
                      (by simp only [evmS, initState]; exact hwv)
                      hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                  exact (hsecondGuards.2.1 hz1True hshort1).reEquivExecutionRevert hcode
                    hdispatch (uniswapDecode_sync hsz4) hbody
                · have hz1True : z1 = true := Bool.eq_true_of_not_eq_false hz1
                  have ho132 : 32 ≤ o1.size := not_lt.mp hshort1
                  let balance1 := UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32))
                  have hcall1 : typedCallViaEVM config evm0S
                      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
                      [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false := by
                    simpa [hz1True] using hcall1All
                  have hdec1 :
                      config.externalABI.decode? "balanceOf" o1 =
                        some (uniswapUint256Value balance1) := by
                    simpa [balance1, skimBalanceValue, uniswapUint256Value] using
                      uniswapSkimBalanceOfDecode_ok (returndata := o1) ho132
                  obtain ⟨_, _, rd6336⟩ := hsecondGuards.2.2 hz1True ho132
                  obtain ⟨_, _, rd6959⟩ := uniswapSyncReserveSlotUnpack rd6336
                    (by simp only [List.length_cons, List.length_nil]; omega)
                  have hmemSize :
                      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).size =
                        164 := by
                    exact balanceOfThisRebuiltStaticcallMem_size_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size
                  have hmemRead64 :
                      (balanceOfThisRebuiltStaticcallMem
                        (UInt256.ofNat I.codeOwner.val) o o1).readWithPadding 64 32 =
                        UInt256.toByteArray ⟨128⟩ := by
                    exact balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size
                  have hreserve112MaskNat : reserve112Mask.toNat = 2 ^ 112 - 1 := by
                    native_decide
                  by_cases hfit0 : balance0.toNat ≤ reserve112Mask.toNat
                  · by_cases hfit1 : balance1.toNat ≤ reserve112Mask.toNat
                    · have hbound0 : Int.ofNat balance0.toNat ≤ maxUint112 := by
                        rw [hreserve112MaskNat] at hfit0
                        norm_num [maxUint112] at hfit0 ⊢
                        omega
                      have hbound1 : Int.ofNat balance1.toNat ≤ maxUint112 := by
                        rw [hreserve112MaskNat] at hfit1
                        norm_num [maxUint112] at hfit1 ⊢
                        omega
                      obtain ⟨_, _, rd7060⟩ :=
                        RD.uniswapUpdateOverflowGuardOk
                          (by simpa [balanceOfThisStaticcallActiveWords] using rd6959)
                          hfit0 hfit1
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      have henv1I : evm1S.executionEnv = I := henv1.trans henv0I
                      have hslotWordSource :
                          Solm.EVM.storageLoad evm1S evm1S.executionEnv.codeOwner ⟨8⟩ =
                            uniswapSlotWord ⟨8⟩ σ'' I := by
                        have hslot :=
                          accountMapEquiv_storage_findD hPostAccounts1 I.codeOwner ⟨8⟩ ⟨0⟩
                        simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                          uniswapSlotWord, henv1I] using hslot.symm
                      by_cases helapsed0 :
                          UInt256.land
                            (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ'' I) I)
                            reserve32Mask = ⟨0⟩
                      · have hsourceElapsed : syncTimeElapsedInt evm1S = 0 := by
                          rw [syncTimeElapsedInt_eq_updateElapsedWord_toNat evm1S]
                          rw [hslotWordSource, henv1I, helapsed0]
                          rfl
                        have hbody :
                            ExecTransitionBody config contract evmS ∅ syncTransition.body
                              (.returned (syncAfterUpdateFrame balance0 balance1)
                                (uniswapLockExitedState
                                  (syncUpdatePackedReserveState evm1S balance0 balance1))
                                none) := by
                          exact uniswapSyncBodyReturns_conditionFalse_packed evmS evm0S evm1S
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                            hbound0 hbound1
                            (evalExpr_sync_update_condition_false_elapsed_zero evm1S balance0
                              balance1 hsourceElapsed)
                        obtain ⟨_, _, rd7241⟩ :=
                          RD.uniswapUpdateElapsedZeroSkipsCumulatives rd7060
                            (by
                              simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
                                uniswapSlotWord] using helapsed0)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        obtain ⟨_, _, rd7339⟩ :=
                          RD.uniswapUpdateStorePackedReserves
                            (by
                              simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
                                uniswapSlotWord] using rd7241)
                            hperm
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        let packed :=
                          uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σ'' I)
                            (uniswapUpdateTimestampWord I) balance1 balance0
                        let mem0 :=
                          balanceOfThisRebuiltStaticcallMem
                            (UInt256.ofNat I.codeOwner.val) o o1
                        have hmemSize128 : 128 ≤ mem0.size := by
                          change 128 ≤
                            (balanceOfThisRebuiltStaticcallMem
                              (UInt256.ofNat I.codeOwner.val) o o1).size
                          rw [hmemSize]
                          omega
                        have hmemRead64Local :
                            mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
                          simpa [mem0] using hmemRead64
                        obtain ⟨_, _, rd6363⟩ :=
                          RD.uniswapUpdateEmitSyncAndJump
                            (packed := packed) (ret := ⟨6363⟩)
                            (R := [⟨570⟩, uniswapSelWord I])
                            (mem := mem0) (aw := balanceOfThisStaticcallActiveWords)
                            (awLoad := balanceOfThisStaticcallActiveWords)
                            (awLog := balanceOfThisStaticcallActiveWords)
                            (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
                            (mcostLoadLog := 0) (mcostLog := 0)
                            (by
                              simpa [packed, mem0, uniswapUpdateElapsedWord,
                                uniswapUpdateTimestampWord, uniswapSlotWord] using rd7339)
                            (by
                              intro s haw hstk
                              simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                hstk]
                              native_decide)
                            (by
                              simpa [mem0] using
                                balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
                                  (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132
                                  ho1Size)
                            (by native_decide)
                            (by
                              intro s haw hstk
                              simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                hstk]
                              native_decide)
                            (by native_decide)
                            (by
                              intro s haw hstk
                              simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                hstk]
                              native_decide)
                            (by native_decide)
                            (by
                              intro s haw hstk
                              simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                hstk]
                              native_decide)
                            (by
                              simpa [mem0] using
                                uniswapSyncLogMem_mload64 packed mem0 hmemSize128
                                  hmemRead64Local)
                            (by native_decide)
                            (by
                              intro s haw hstk
                              simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                hstk]
                              native_decide)
                            (by native_decide) hperm (by jump_dest)
                            (by simp only [List.length_cons, List.length_nil]; omega)
                        have rdRet := RD.uniswapSyncAfterUpdateToReturn rd6363 hperm
                        have hCreatedRet :
                            cA'' =
                              (uniswapLockExitedState
                                (syncUpdatePackedReserveState evm1S balance0 balance1)).createdAccounts := by
                          simp [uniswapLockExitedState, uniswapUnlockedState,
                            syncUpdatePackedReserveState, storageStore_createdAccounts,
                            hcreated1]
                        have hPackedAccounts :
                            accountMapEquiv
                              (sstoreAccountMap I.codeOwner σ'' ⟨8⟩ packed)
                              (syncUpdatePackedReserveState evm1S balance0 balance1).accountMap := by
                          let v0 :=
                            setUint112Offset0Word (uniswapSlotWord ⟨8⟩ σ'' I) balance0
                          let v1 := setUint112Offset14Word v0 balance1
                          have hpacked :
                              packed = setUint32Offset28Word v1 (uniswapUpdateTimestampWord I) := by
                            simp [packed, v0, v1, uniswapUpdatePackedReserveWord_eq_setters]
                          by_cases haccExists :
                              ∃ acc, evm1S.accountMap.find? I.codeOwner = some acc
                          · obtain ⟨acc, hacc⟩ := haccExists
                            have hload0 :
                                Solm.EVM.storageLoad evm1S I.codeOwner ⟨8⟩ =
                                  uniswapSlotWord ⟨8⟩ σ'' I := by
                              simpa [henv1I] using hslotWordSource
                            have hload1 :
                                Solm.EVM.storageLoad
                                    (Solm.EVM.storageStore evm1S I.codeOwner ⟨8⟩ v0)
                                    I.codeOwner ⟨8⟩ =
                                  v0 := by
                              exact storageLoad_storageStore_same_present evm1S I.codeOwner
                                hacc ⟨8⟩ v0
                            obtain ⟨acc0, hacc0⟩ :
                                ∃ acc0,
                                  (Solm.EVM.storageStore evm1S I.codeOwner ⟨8⟩ v0).accountMap.find?
                                      I.codeOwner =
                                    some acc0 := by
                              refine ⟨Account.updateStorage acc ⟨8⟩ v0, ?_⟩
                              simpa [Solm.EVM.storageStore, State.lookupAccount, hacc,
                                State.setAccount, Option.option] using
                                accountMap_find_insert_self evm1S.accountMap I.codeOwner
                                  (Account.updateStorage acc ⟨8⟩ v0)
                            have hload2 :
                                Solm.EVM.storageLoad
                                    (Solm.EVM.storageStore
                                      (Solm.EVM.storageStore evm1S I.codeOwner ⟨8⟩ v0)
                                      I.codeOwner ⟨8⟩ v1)
                                    I.codeOwner ⟨8⟩ =
                                  v1 := by
                              exact storageLoad_storageStore_same_present
                                (Solm.EVM.storageStore evm1S I.codeOwner ⟨8⟩ v0)
                                I.codeOwner hacc0 ⟨8⟩ v1
                            have hbase :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner σ'' ⟨8⟩ packed)
                                  (sstoreAccountMap I.codeOwner evm1S.accountMap ⟨8⟩ packed) :=
                              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ packed
                                hPostAccounts1
                            have hsingle :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner evm1S.accountMap ⟨8⟩ packed)
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner evm1S.accountMap ⟨8⟩ v1)
                                    ⟨8⟩ packed) :=
                              accountMapEquiv_sstoreAccountMap_self_update evm1S.accountMap
                                I.codeOwner ⟨8⟩ v1 packed
                            have hupdate01 :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner evm1S.accountMap ⟨8⟩ v1)
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner evm1S.accountMap ⟨8⟩ v0)
                                    ⟨8⟩ v1) :=
                              accountMapEquiv_sstoreAccountMap_self_update evm1S.accountMap
                                I.codeOwner ⟨8⟩ v0 v1
                            have hdouble :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner evm1S.accountMap ⟨8⟩ v1)
                                    ⟨8⟩ packed)
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner
                                      (sstoreAccountMap I.codeOwner evm1S.accountMap ⟨8⟩ v0)
                                      ⟨8⟩ v1)
                                    ⟨8⟩ packed) :=
                              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ packed hupdate01
                            have hchain := (hbase.trans hsingle).trans hdouble
                            simpa [syncUpdatePackedReserveState, storageStore_accountMap,
                              storageStore_executionEnv, hload0, hload1, hload2, henv1I,
                              hpacked, v0, v1] using hchain
                          · have hmissing :
                                evm1S.accountMap.find? I.codeOwner = none := by
                              cases hfind : evm1S.accountMap.find? I.codeOwner with
                              | none => rfl
                              | some acc => exact False.elim (haccExists ⟨acc, hfind⟩)
                            have hmissingSource :
                                σ''.find? I.codeOwner = none :=
                              accountMapEquiv_find?_none hPostAccounts1.symm hmissing
                            have hleft :
                                sstoreAccountMap I.codeOwner σ'' ⟨8⟩ packed = σ'' :=
                              sstoreAccountMap_absent_same hmissingSource
                            have hmissingOwner :
                                evm1S.accountMap.find? evm1S.executionEnv.codeOwner = none := by
                              simpa [henv1I] using hmissing
                            have hright :
                                (syncUpdatePackedReserveState evm1S balance0 balance1).accountMap =
                                  evm1S.accountMap := by
                              simp [syncUpdatePackedReserveState,
                                storageStore_absent evm1S evm1S.executionEnv.codeOwner
                                  hmissingOwner]
                            simpa [hleft, hright] using hPostAccounts1
                        have hAccountsRet :
                            accountMapEquiv
                              (sstoreAccountMap I.codeOwner
                                (sstoreAccountMap I.codeOwner σ'' ⟨8⟩ packed) ⟨12⟩ ⟨1⟩)
                              (uniswapLockExitedState
                                (syncUpdatePackedReserveState evm1S balance0 balance1)).accountMap := by
                          have hs :=
                            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                              hPackedAccounts
                          simpa [uniswapLockExitedState, uniswapUnlockedState,
                            storageStore_accountMap, storageStore_executionEnv,
                            syncUpdatePackedReserveState, henv1I] using hs
                        exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                          (uniswapDecode_sync hsz4) hbody hCreatedRet hAccountsRet
                          (returnEquiv.void rfl rfl rfl)
                      · have helapsedNe :
                            UInt256.land
                              (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ'' I) I)
                              reserve32Mask ≠ ⟨0⟩ := helapsed0
                        let packed :=
                          uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σ'' I)
                            (uniswapUpdateTimestampWord I) balance1 balance0
                        let mem0 :=
                          balanceOfThisRebuiltStaticcallMem
                            (UInt256.ofNat I.codeOwner.val) o o1
                        have hmemSize128 : 128 ≤ mem0.size := by
                          change 128 ≤
                            (balanceOfThisRebuiltStaticcallMem
                              (UInt256.ofNat I.codeOwner.val) o o1).size
                          rw [hmemSize]
                          omega
                        have hmemRead64Local :
                            mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
                          simpa [mem0] using hmemRead64
                        have finishPacked
                            {k7241 C7241 : ℕ} {rdata7241 : ByteArray}
                            (rd7241 :
                              RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                ⟨7241⟩
                                (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ'' I) I ::
                                  uniswapUpdateTimestampWord I ::
                                  UInt256.land
                                    (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift)
                                    reserve112Mask ::
                                  UInt256.land (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Mask ::
                                  balance1 :: balance0 :: [⟨6363⟩, ⟨570⟩, uniswapSelWord I])
                                mem0 balanceOfThisStaticcallActiveWords rdata7241
                                (cA'', σ'') k7241 C7241)
                            (hbody :
                              ExecTransitionBody config contract evmS ∅ syncTransition.body
                                (.returned (syncAfterUpdateFrame balance0 balance1)
                                  (uniswapLockExitedState
                                    (syncUpdatePackedReserveState evm1S balance0 balance1))
                                  none)) :
                            runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
                          obtain ⟨_, _, rd7339⟩ :=
                            RD.uniswapUpdateStorePackedReserves
                              (by
                                simpa [packed, mem0, uniswapUpdateElapsedWord,
                                  uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
                              hperm
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          obtain ⟨_, _, rd6363⟩ :=
                            RD.uniswapUpdateEmitSyncAndJump
                              (packed := packed) (ret := ⟨6363⟩)
                              (R := [⟨570⟩, uniswapSelWord I])
                              (mem := mem0) (aw := balanceOfThisStaticcallActiveWords)
                              (awLoad := balanceOfThisStaticcallActiveWords)
                              (awLog := balanceOfThisStaticcallActiveWords)
                              (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
                              (mcostLoadLog := 0) (mcostLog := 0)
                              (by
                                simpa [packed, mem0, uniswapUpdateElapsedWord,
                                  uniswapUpdateTimestampWord, uniswapSlotWord] using rd7339)
                              (by
                                intro s haw hstk
                                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                  hstk]
                                native_decide)
                              (by
                                simpa [mem0] using
                                  balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
                                    (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132
                                    ho1Size)
                              (by native_decide)
                              (by
                                intro s haw hstk
                                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                  hstk]
                                native_decide)
                              (by native_decide)
                              (by
                                intro s haw hstk
                                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                  hstk]
                                native_decide)
                              (by native_decide)
                              (by
                                intro s haw hstk
                                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                  hstk]
                                native_decide)
                              (by
                                simpa [mem0] using
                                  uniswapSyncLogMem_mload64 packed mem0 hmemSize128
                                    hmemRead64Local)
                              (by native_decide)
                              (by
                                intro s haw hstk
                                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                  hstk]
                                native_decide)
                              (by native_decide) hperm (by jump_dest)
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          have rdRet := RD.uniswapSyncAfterUpdateToReturn rd6363 hperm
                          have hCreatedRet :
                              cA'' =
                                (uniswapLockExitedState
                                  (syncUpdatePackedReserveState evm1S balance0 balance1)).createdAccounts := by
                            simp [uniswapLockExitedState, uniswapUnlockedState,
                              syncUpdatePackedReserveState, storageStore_createdAccounts,
                              hcreated1]
                          have hPackedAccounts :
                              accountMapEquiv
                                (sstoreAccountMap I.codeOwner σ'' ⟨8⟩ packed)
                                (syncUpdatePackedReserveState evm1S balance0 balance1).accountMap :=
                            accountMapEquiv_syncUpdatePackedReserveState hPostAccounts1 henv1I
                              hslotWordSource (by rfl)
                          have hAccountsRet :
                              accountMapEquiv
                                (sstoreAccountMap I.codeOwner
                                  (sstoreAccountMap I.codeOwner σ'' ⟨8⟩ packed) ⟨12⟩ ⟨1⟩)
                                (uniswapLockExitedState
                                  (syncUpdatePackedReserveState evm1S balance0 balance1)).accountMap := by
                            have hs :=
                              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                hPackedAccounts
                            simpa [uniswapLockExitedState, uniswapUnlockedState,
                              storageStore_accountMap, storageStore_executionEnv,
                              syncUpdatePackedReserveState, henv1I] using hs
                          exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                            (uniswapDecode_sync hsz4) hbody hCreatedRet hAccountsRet
                            (returnEquiv.void rfl rfl rfl)
                        let reserve0Word : UInt256 :=
                          UInt256.land (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Mask
                        let reserve1Word : UInt256 :=
                          UInt256.land
                            (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift)
                            reserve112Mask
                        by_cases hreserve0Zero : reserve0Word = (⟨0⟩ : UInt256)
                        · have hsourceReserve0 :
                              Int.ofNat (uniswapReserve0Word evm1S).toNat = 0 := by
                            have hloadI :
                                Solm.EVM.storageLoad evm1S I.codeOwner ⟨8⟩ =
                                  uniswapSlotWord ⟨8⟩ σ'' I := by
                              simpa [henv1I] using hslotWordSource
                            have hword : uniswapReserve0Word evm1S = reserve0Word := by
                              simp [reserve0Word, uniswapReserve0Word, hloadI, henv1I]
                            rw [hword, hreserve0Zero]
                            rfl
                          have hbody :
                              ExecTransitionBody config contract evmS ∅ syncTransition.body
                                (.returned (syncAfterUpdateFrame balance0 balance1)
                                  (uniswapLockExitedState
                                    (syncUpdatePackedReserveState evm1S balance0 balance1))
                                  none) := by
                            exact uniswapSyncBodyReturns_conditionFalse_packed evmS evm0S evm1S
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                              hbound0 hbound1
                              (evalExpr_sync_update_condition_false_reserve0_zero evm1S
                                balance0 balance1 hsourceReserve0)
                          obtain ⟨_, _, rd7241⟩ :=
                            RD.uniswapUpdateReserve0ZeroSkipsCumulatives rd7060
                              (by
                                simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
                                  uniswapSlotWord] using helapsedNe)
                              (by
                                dsimp [reserve0Word] at hreserve0Zero
                                rw [hreserve0Zero]
                                native_decide)
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          exact finishPacked
                            (by
                              simpa [reserve0Word, reserve1Word, mem0, uniswapUpdateElapsedWord,
                                uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
                            hbody
                        · by_cases hreserve1Zero : reserve1Word = (⟨0⟩ : UInt256)
                          · have hsourceReserve1 :
                                Int.ofNat (uniswapReserve1Word evm1S).toNat = 0 := by
                              have hloadI :
                                  Solm.EVM.storageLoad evm1S I.codeOwner ⟨8⟩ =
                                    uniswapSlotWord ⟨8⟩ σ'' I := by
                                simpa [henv1I] using hslotWordSource
                              have hword : uniswapReserve1Word evm1S = reserve1Word := by
                                simp [reserve1Word, uniswapReserve1Word, hloadI, henv1I]
                              rw [hword, hreserve1Zero]
                              rfl
                            have hbody :
                                ExecTransitionBody config contract evmS ∅ syncTransition.body
                                  (.returned (syncAfterUpdateFrame balance0 balance1)
                                    (uniswapLockExitedState
                                      (syncUpdatePackedReserveState evm1S balance0 balance1))
                                    none) := by
                              exact uniswapSyncBodyReturns_conditionFalse_packed evmS evm0S evm1S
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                                hbound0 hbound1
                                (evalExpr_sync_update_condition_false_reserve1_zero evm1S
                                  balance0 balance1 hsourceReserve1)
                            have hreserve0Masked :
                                UInt256.land reserve0Word reserve112Mask = reserve0Word := by
                              dsimp [reserve0Word]
                              exact uint112Mask_idempotent (uniswapSlotWord ⟨8⟩ σ'' I)
                            have hreserve0Ne :
                                UInt256.land reserve0Word reserve112Mask ≠ ⟨0⟩ := by
                              rw [hreserve0Masked]
                              exact hreserve0Zero
                            obtain ⟨_, _, rd7241⟩ :=
                              RD.uniswapUpdateReserve1ZeroSkipsCumulatives rd7060
                                (by
                                  simpa [uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
                                    uniswapSlotWord] using helapsedNe)
                                (by
                                  simpa [reserve0Word, reserve1Word] using hreserve0Ne)
                                (by
                                  dsimp [reserve1Word] at hreserve1Zero
                                  rw [hreserve1Zero]
                                  native_decide)
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            exact finishPacked
                              (by
                                simpa [reserve0Word, reserve1Word, mem0, uniswapUpdateElapsedWord,
                                  uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
                              hbody
                          · have hloadI :
                                Solm.EVM.storageLoad evm1S I.codeOwner ⟨8⟩ =
                                  uniswapSlotWord ⟨8⟩ σ'' I := by
                              simpa [henv1I] using hslotWordSource
                            let elapsedWord : UInt256 := uniswapUpdateElapsedFromStorage σ'' I
                            let timestampWord : UInt256 := uniswapUpdateTimestampWord I
                            let price0Word : UInt256 :=
                              uniswapUpdatePrice0CumulativeWord σ'' I elapsedWord
                                reserve1Word reserve0Word
                            let σP0 : AccountMap :=
                              sstoreAccountMap I.codeOwner σ'' ⟨9⟩ price0Word
                            let price1Word : UInt256 :=
                              uniswapUpdatePrice1CumulativeWord σP0 I elapsedWord
                                reserve0Word reserve1Word
                            let σP1 : AccountMap :=
                              sstoreAccountMap I.codeOwner σP0 ⟨10⟩ price1Word
                            let packedCumulative : UInt256 :=
                              uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σP1 I)
                                timestampWord balance1 balance0
                            have helapsedSource :
                                elapsedWord =
                                  uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σ'' I) I := by
                              simp [elapsedWord, uniswapUpdateElapsedFromStorage,
                                uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
                                uniswapSlotWord]
                            have hsourceElapsedPos : 0 < syncTimeElapsedInt evm1S := by
                              have hsyncElapsed :
                                  syncTimeElapsedInt evm1S =
                                    Int.ofNat (UInt256.land elapsedWord reserve32Mask).toNat := by
                                rw [syncTimeElapsedInt_eq_updateElapsedWord_toNat evm1S]
                                simpa [hloadI, henv1I, helapsedSource]
                              rw [hsyncElapsed, Int.ofNat_eq_natCast]
                              apply Int.natCast_pos.mpr
                              apply Nat.pos_of_ne_zero
                              intro hnat
                              have hword :
                                  UInt256.land elapsedWord reserve32Mask = ⟨0⟩ := by
                                apply u256_inj
                                exact hnat
                              have hne : UInt256.land elapsedWord reserve32Mask ≠ ⟨0⟩ := by
                                simpa [helapsedSource] using helapsedNe
                              exact hne hword
                            have hsourceReserve0 :
                                Int.ofNat (uniswapReserve0Word evm1S).toNat ≠ 0 := by
                              have hword : uniswapReserve0Word evm1S = reserve0Word := by
                                simp [reserve0Word, uniswapReserve0Word, hloadI, henv1I]
                              intro hzero
                              apply hreserve0Zero
                              rw [← hword]
                              apply u256_inj
                              simpa using (Int.ofNat_eq_zero.mp hzero)
                            have hsourceReserve1 :
                                Int.ofNat (uniswapReserve1Word evm1S).toNat ≠ 0 := by
                              have hword : uniswapReserve1Word evm1S = reserve1Word := by
                                simp [reserve1Word, uniswapReserve1Word, hloadI, henv1I]
                              intro hzero
                              apply hreserve1Zero
                              rw [← hword]
                              apply u256_inj
                              simpa using (Int.ofNat_eq_zero.mp hzero)
                            have hbody :
                                ExecTransitionBody config contract evmS ∅ syncTransition.body
                                  (.returned (syncAfterUpdateFrame balance0 balance1)
                                    (uniswapLockExitedState
                                      (syncUpdateCumulativePackedReserveState evm1S
                                        balance0 balance1))
                                    none) := by
                              exact uniswapSyncBodyReturns_conditionTrue_packed evmS evm0S evm1S
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                                hbound0 hbound1 hsourceElapsedPos hsourceReserve0
                                hsourceReserve1
                            exact uniswapSyncBodyCumulativeSuccess
                              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                              (g := g) (cA'' := cA'') (σ'' := σ'') (o := o)
                              (o1 := o1) (evm1S := evm1S) (balance0 := balance0)
                              (balance1 := balance1)
                              hcode hdispatch hsz4 hperm (by simpa [evmS] using hbody)
                              hPostAccounts1 hcreated1 henv1I hslotWordSource rd7060
                              hmemSize hmemRead64 ho32 hoSize ho132 ho1Size helapsedNe
                              (by simpa [reserve0Word] using hreserve0Zero)
                              (by simpa [reserve1Word] using hreserve1Zero)
/-
                            have hreserve0Masked :
                                UInt256.land reserve0Word reserve112Mask = reserve0Word := by
                              dsimp [reserve0Word]
                              exact uint112Mask_idempotent (uniswapSlotWord ⟨8⟩ σ'' I)
                            have hreserve1Masked :
                                UInt256.land reserve1Word reserve112Mask = reserve1Word := by
                              dsimp [reserve1Word]
                              exact uint112Mask_idempotent
                                (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift)
                            have hreserve0Ne :
                                UInt256.land reserve0Word reserve112Mask ≠ ⟨0⟩ := by
                              rw [hreserve0Masked]
                              exact hreserve0Zero
                            have hreserve1Ne :
                                UInt256.land reserve1Word reserve112Mask ≠ ⟨0⟩ := by
                              rw [hreserve1Masked]
                              exact hreserve1Zero
                            obtain ⟨_, _, rd7241⟩ :=
                              RD.uniswapUpdateCumulativesAndJump rd7060
                                (by
                                  simpa [uniswapUpdateElapsedFromStorage,
                                    uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
                                    uniswapSlotWord] using helapsedNe)
                                (by simpa [reserve0Word, reserve1Word] using hreserve0Ne)
                                (by simpa [reserve0Word, reserve1Word] using hreserve1Ne)
                                hperm
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            obtain ⟨_, _, rd7339⟩ :=
                              RD.uniswapUpdateStorePackedReserves
                                (by
                                  simpa [elapsedWord, timestampWord, price0Word, σP0,
                                    price1Word, σP1, reserve0Word, reserve1Word, mem0,
                                    uniswapUpdateElapsedFromStorage, uniswapUpdateElapsedWord,
                                    uniswapUpdateTimestampWord, uniswapSlotWord] using rd7241)
                                hperm
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            obtain ⟨_, _, rd6363⟩ :=
                              RD.uniswapUpdateEmitSyncAndJump
                                (packed := packedCumulative) (ret := ⟨6363⟩)
                                (R := [⟨570⟩, uniswapSelWord I])
                                (mem := mem0) (aw := balanceOfThisStaticcallActiveWords)
                                (awLoad := balanceOfThisStaticcallActiveWords)
                                (awLog := balanceOfThisStaticcallActiveWords)
                                (mcostLoad := 0) (mcostStore0 := 0) (mcostStore1 := 0)
                                (mcostLoadLog := 0) (mcostLog := 0)
                                (by
                                  simpa [packedCumulative, elapsedWord, timestampWord,
                                    price0Word, σP0, price1Word, σP1, reserve0Word,
                                    reserve1Word, mem0, uniswapUpdateElapsedFromStorage,
                                    uniswapUpdateElapsedWord, uniswapUpdateTimestampWord,
                                    uniswapSlotWord] using rd7339)
                                (by
                                  intro s haw hstk
                                  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                    hstk]
                                  native_decide)
                                (by
                                  simpa [mem0] using
                                    balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
                                      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132
                                      ho1Size)
                                (by native_decide)
                                (by
                                  intro s haw hstk
                                  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                    hstk]
                                  native_decide)
                                (by native_decide)
                                (by
                                  intro s haw hstk
                                  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                    hstk]
                                  native_decide)
                                (by native_decide)
                                (by
                                  intro s haw hstk
                                  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                    hstk]
                                  native_decide)
                                (by
                                  simpa [mem0] using
                                    uniswapSyncLogMem_mload64 packedCumulative mem0 hmemSize128
                                      hmemRead64Local)
                                (by native_decide)
                                (by
                                  intro s haw hstk
                                  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw,
                                    hstk]
                                  native_decide)
                                (by native_decide) hperm (by jump_dest)
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            have rdRet := RD.uniswapSyncAfterUpdateToReturn rd6363 hperm
                            let evmP0 :=
                              Solm.EVM.storageStore evm1S I.codeOwner ⟨9⟩
                                (EVM.wordOfInt (syncPrice0CumulativeIntAt evm1S evm1S))
                            have hprice0Nat :
                                syncPrice0CumulativeIntAt evm1S evm1S =
                                  Int.ofNat ((uniswapSlotWord ⟨9⟩ σ'' I).toNat +
                                    (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
                                      (UInt256.land reserve32Mask elapsedWord).toNat) %
                                    twoPow256 := by
                              exact _root_.UniswapV2Pair.syncPrice0CumulativeIntAt_eq_updateWord_nat_form
                                (σStorage := σ'') (σUpdate := σ'')
                                (storageEvm := evm1S) (updateEvm := evm1S)
                                (I := I) (elapsed := elapsedWord)
                                (reserve1 := reserve1Word) (reserve0 := reserve0Word)
                                hPostAccounts1 henv1I henv1I hslotWordSource helapsedSource
                                (by rfl) (by rfl)
                            have hprice0Eq :
                                EVM.wordOfInt (syncPrice0CumulativeIntAt evm1S evm1S) =
                                  price0Word := by
                              let n : Nat := (uniswapSlotWord ⟨9⟩ σ'' I).toNat +
                                (reserve1Word.toNat * 2 ^ 112 / reserve0Word.toNat) *
                                  (UInt256.land reserve32Mask elapsedWord).toNat
                              have hn :
                                  syncPrice0CumulativeIntAt evm1S evm1S =
                                    Int.ofNat n % twoPow256 := by
                                simpa [n] using hprice0Nat
                              rw [hn, _root_.UniswapV2Pair.wordOfInt_nat_mod_twoPow256 n]
                              apply u256_inj
                              rw [uniswapUpdatePrice0CumulativeWord_toNat]
                              · change (Fin.ofNat UInt256.size n).val = n % UInt256.size
                                simp [Fin.ofNat]
                              · dsimp [reserve1Word]
                                exact uniswapUint112Masked_lt _
                              · dsimp [reserve0Word]
                                exact uniswapUint112Masked_lt _
                            have hP0Accounts : accountMapEquiv σP0 evmP0.accountMap := by
                              have hs :=
                                accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩
                                  price0Word hPostAccounts1
                              simpa [σP0, evmP0, storageStore_accountMap, hprice0Eq]
                                using hs
                            have henvP0 : evmP0.executionEnv = I := by
                              simp [evmP0, storageStore_executionEnv, henv1I]
                            let evmP1 :=
                              Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
                                (EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm1S))
                            have hprice1Nat :
                                syncPrice1CumulativeIntAt evmP0 evm1S =
                                  Int.ofNat ((uniswapSlotWord ⟨10⟩ σP0 I).toNat +
                                    (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
                                      (UInt256.land elapsedWord reserve32Mask).toNat) %
                                    twoPow256 := by
                              exact _root_.UniswapV2Pair.syncPrice1CumulativeIntAt_eq_updateWord_nat_form
                                (σStorage := σP0) (σUpdate := σ'')
                                (storageEvm := evmP0) (updateEvm := evm1S)
                                (I := I) (elapsed := elapsedWord)
                                (reserve0 := reserve0Word) (reserve1 := reserve1Word)
                                hP0Accounts henvP0 henv1I hslotWordSource helapsedSource
                                (by rfl) (by rfl)
                            have hprice1Eq :
                                EVM.wordOfInt (syncPrice1CumulativeIntAt evmP0 evm1S) =
                                  price1Word := by
                              let n : Nat := (uniswapSlotWord ⟨10⟩ σP0 I).toNat +
                                (reserve0Word.toNat * 2 ^ 112 / reserve1Word.toNat) *
                                  (UInt256.land elapsedWord reserve32Mask).toNat
                              have hn :
                                  syncPrice1CumulativeIntAt evmP0 evm1S =
                                    Int.ofNat n % twoPow256 := by
                                simpa [n] using hprice1Nat
                              rw [hn, _root_.UniswapV2Pair.wordOfInt_nat_mod_twoPow256 n]
                              apply u256_inj
                              rw [uniswapUpdatePrice1CumulativeWord_toNat]
                              · change (Fin.ofNat UInt256.size n).val = n % UInt256.size
                                simp [Fin.ofNat]
                              · dsimp [reserve0Word]
                                exact uniswapUint112Masked_lt _
                              · dsimp [reserve1Word]
                                exact uniswapUint112Masked_lt _
                            have hP1Accounts : accountMapEquiv σP1 evmP1.accountMap := by
                              have hs :=
                                accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩
                                  price1Word hP0Accounts
                              simpa [σP1, evmP1, storageStore_accountMap, hprice1Eq]
                                using hs
                            have henvP1 : evmP1.executionEnv = I := by
                              simp [evmP1, storageStore_executionEnv, henvP0]
                            have hslot8P1 :
                                Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩ =
                                  uniswapSlotWord ⟨8⟩ σP1 I := by
                              have h :=
                                accountMapEquiv_storage_findD hP1Accounts I.codeOwner ⟨8⟩
                                  ⟨0⟩
                              simp [Solm.EVM.storageLoad, State.lookupAccount,
                                Account.lookupStorage, uniswapSlotWord, henvP1] at h ⊢
                              exact h.symm
                            have hPackedAccounts :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
                                  (syncUpdatePackedReserveState evmP1 balance0 balance1).accountMap :=
                              accountMapEquiv_syncUpdatePackedReserveState hP1Accounts henvP1
                                hslot8P1 (by rfl)
                            have hPackedAccountsCumulative :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
                                  (syncUpdateCumulativePackedReserveState evm1S balance0 balance1).accountMap := by
                              simpa [syncUpdateCumulativePackedReserveState,
                                syncUpdatePackedReserveState, evmP0, evmP1,
                                storageStore_executionEnv, henv1I, henvP0] using
                                hPackedAccounts
                            have hCreatedRet :
                                cA'' =
                                  (uniswapLockExitedState
                                    (syncUpdateCumulativePackedReserveState evm1S
                                      balance0 balance1)).createdAccounts := by
                              simp [uniswapLockExitedState, uniswapUnlockedState,
                                syncUpdateCumulativePackedReserveState,
                                storageStore_createdAccounts, hcreated1]
                            have hAccountsRet :
                                accountMapEquiv
                                  (sstoreAccountMap I.codeOwner
                                    (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
                                    ⟨12⟩ ⟨1⟩)
                                  (uniswapLockExitedState
                                    (syncUpdateCumulativePackedReserveState evm1S
                                      balance0 balance1)).accountMap := by
                              have hs :=
                                accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                  hPackedAccountsCumulative
                              simpa [uniswapLockExitedState, uniswapUnlockedState,
                                storageStore_accountMap, storageStore_executionEnv,
                                syncUpdateCumulativePackedReserveState, henv1I] using hs
                            exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                              (uniswapDecode_sync hsz4) hbody hCreatedRet hAccountsRet
                              (returnEquiv.void rfl rfl rfl)
-/
                    · have hfail1 : reserve112Mask.toNat < balance1.toNat := by omega
                      have hbound0 : Int.ofNat balance0.toNat ≤ maxUint112 := by
                        rw [hreserve112MaskNat] at hfit0
                        norm_num [maxUint112] at hfit0 ⊢
                        omega
                      have hbound1 : maxUint112 < Int.ofNat balance1.toNat := by
                        rw [hreserve112MaskNat] at hfail1
                        norm_num [maxUint112] at hfail1 ⊢
                        omega
                      have hbody :
                          ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
                        exact uniswapSyncBodyReverts_secondBoundFailure evmS evm0S evm1S
                          (by simp only [evmS, initState]; exact hwv)
                          hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                          hbound0 hbound1
                      have rdRev :=
                        RD.uniswapUpdateOverflowGuardSecondReverts
                          (by simpa [balanceOfThisStaticcallActiveWords] using rd6959)
                          hfit0 hfail1 hmemSize hmemRead64
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                        (uniswapDecode_sync hsz4) hbody
                  · have hfail0 : reserve112Mask.toNat < balance0.toNat := by omega
                    have hbound0 : maxUint112 < Int.ofNat balance0.toNat := by
                      rw [hreserve112MaskNat] at hfail0
                      norm_num [maxUint112] at hfail0 ⊢
                      omega
                    have hbody :
                        ExecTransitionBody config contract evmS ∅ syncTransition.body .reverted := by
                      exact uniswapSyncBodyReverts_firstBoundFailure evmS evm0S evm1S
                        (by simp only [evmS, initState]; exact hwv)
                        hunlockedSolm hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
                        hbound0
                    have rdRev :=
                      RD.uniswapUpdateOverflowGuardFirstReverts
                        (by simpa [balanceOfThisStaticcallActiveWords] using rd6959)
                        hfail0 hmemSize hmemRead64
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                      (uniswapDecode_sync hsz4) hbody
      · rw [not_lt] at hdepth
        have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
        exact uniswapSyncBodyRevert_firstCallDepth hcode hsize hperm hwv hsel
          hdepth1024 hunlocked htoken0NoCode hdispatch hAccounts

end UniswapV2Pair
