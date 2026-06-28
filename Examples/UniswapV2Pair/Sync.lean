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
      (s2 :=
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ] ++
        updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hlock (by intro f e h; cases h))

theorem uniswapSyncLockedSource (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hlock := uniswapLockEnterLockedRevert evm ∅ hwv (by simp) hlocked
  simpa [syncTransition, List.append_assoc] using
    (execBlock_append_term
      (s2 :=
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ] ++
        updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hlock (by intro f e h; cases h))

theorem uniswapSyncBalanceOfCallsPrefix (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some balance1) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ])
      (.ok (uniswapBalanceOfFrame ∅ balance0 balance1) evm1) := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hcalls := uniswapTokenBalanceOfThisCallsPrefix
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := ∅)
    (balance0 := balance0) (balance1 := balance1)
    (by simp) (by simp) hcall0 hdec0 hcall1 hdec1
  simpa using execBlock_append hlock hcalls

theorem uniswapSyncBalanceOfFirstCallFailure (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ])
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapTokenBalanceOfThisFirstCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := ∅)
    (by simp) hcall0
  simpa using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfFirstCallDecodeRevert (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ])
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapTokenBalanceOfThisFirstCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := ∅)
    (by simp) hcall0 hdec0
  simpa using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfSecondCallFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ])
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapTokenBalanceOfThisSecondCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := ∅)
    (balance0 := balance0) (by simp) (by simp) hcall0 hdec0 hcall1
  simpa using execBlock_append hlock hfail

theorem uniswapSyncBalanceOfSecondCallDecodeRevert (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ])
      .reverted := by
  have hlock := uniswapSyncLockEnterPrefix evm hwv hunlocked
  have hfail := uniswapTokenBalanceOfThisSecondCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := ∅)
    (balance0 := balance0) (by simp) (by simp) hcall0 hdec0 hcall1 hdec1
  simpa using execBlock_append hlock hfail

theorem uniswapSyncFirstCallFailureSource (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfFirstCallFailure evm evm0 hwv hunlocked hcall0
  simpa [syncTransition, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncFirstCallDecodeRevertSource (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfFirstCallDecodeRevert evm evm0 hwv hunlocked hcall0 hdec0
  simpa [syncTransition, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncSecondCallFailureSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix :=
    uniswapSyncBalanceOfSecondCallFailure evm evm0 evm1 hwv hunlocked hcall0 hdec0 hcall1
  simpa [syncTransition, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncSecondCallDecodeRevertSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body .reverted := by
  have hprefix := uniswapSyncBalanceOfSecondCallDecodeRevert
    evm evm0 evm1 hwv hunlocked hcall0 hdec0 hcall1 hdec1
  simpa [syncTransition, List.append_assoc] using
    (execBlock_append_term
      (s2 := updateReservesStmts (.var "balance0") (.var "balance1") ++ lockExit)
      hprefix (by intro f e h; cases h))

theorem uniswapSyncUpdateBoundsPrefix (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ] ++
        syncUpdateBoundsBody)
      (.ok { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1) := by
  have hbalances := uniswapSyncBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := uniswapUint256Value balance0) (balance1 := uniswapUint256Value balance1)
    hwv hunlocked hcall0 hdec0 hcall1 hdec1
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
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
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
    hwv hunlocked hcall0 hdec0 hcall1 hdec1
  have hbounds :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        syncUpdateBoundsBody .reverted := by
    change ExecBlock config
      { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
      [ .require (.binary .le (.var "balance0") (.intLit maxUint112)),
        .require (.binary .le (.var "balance1") (.intLit maxUint112)) ]
      .reverted
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (evalExpr_sync_balance0_le_max_false evm1 balance0 balance1 hbound0))
  have hprefix := execBlock_append hbalances hbounds
  simpa [syncTransition, updateReservesStmts, syncUpdateBoundsBody, syncUpdateRemainderBody,
    List.append_assoc] using
    (execBlock_append_term (s2 := syncUpdateRemainderBody ++ lockExit) hprefix
      (by intro f e h; cases h))

theorem uniswapSyncSecondBoundFailureSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
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
    hwv hunlocked hcall0 hdec0 hcall1 hdec1
  have hbounds :
      ExecBlock config { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
        syncUpdateBoundsBody .reverted := by
    change ExecBlock config
      { contract := contract, locals := syncBalanceStore balance0 balance1 } evm1
      [ .require (.binary .le (.var "balance0") (.intLit maxUint112)),
        .require (.binary .le (.var "balance1") (.intLit maxUint112)) ]
      .reverted
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_sync_balance0_le_max_true evm1 balance0 balance1 hbound0))
      ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (evalExpr_sync_balance1_le_max_false evm1 balance0 balance1 hbound1))
  have hprefix := execBlock_append hbalances hbounds
  simpa [syncTransition, updateReservesStmts, syncUpdateBoundsBody, syncUpdateRemainderBody,
    List.append_assoc] using
    (execBlock_append_term (s2 := syncUpdateRemainderBody ++ lockExit) hprefix
      (by intro f e h; cases h))

theorem uniswapSyncUpdateTimestampPrefix (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ExecBlock config { contract := contract, locals := ∅ } evm
      (lockEnter ++
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
          .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ] ++
        syncUpdateTimestampBody)
      (.ok { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
        evm1) := by
  have hprefix := uniswapSyncUpdateBoundsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := balance0) (balance1 := balance1)
    hwv hunlocked hcall0 hdec0 hcall1 hdec1 hbound0 hbound1
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
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ∃ evm2 : EVM.State, ∃ evm3 : EVM.State, ∃ evm4 : EVM.State,
      storageLocStore evm1 (uint112Loc0 ⟨8⟩) (uniswapUint256Value balance0) = some evm2 ∧
      storageLocStore evm2 (uint112Loc14 ⟨8⟩) (uniswapUint256Value balance1) = some evm3 ∧
      storageLocStore evm3 (uint32Loc28 ⟨8⟩) (syncBlockTimestampValue evm1) = some evm4 ∧
      ExecBlock config { contract := contract, locals := ∅ } evm
          (lockEnter ++
            [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
              .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ] ++
            updateReservesStmts (.var "balance0") (.var "balance1"))
          (.ok { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
            evm4) := by
  have hprefix := uniswapSyncUpdateTimestampPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1)
    (balance0 := balance0) (balance1 := balance1)
    hwv hunlocked hcall0 hdec0 hcall1 hdec1 hbound0 hbound1
  rcases uniswapStorageLocStore_uint112_offset0_int_some
      (evm := evm1) (slot := ⟨8⟩) (n := Int.ofNat balance0.toNat) with
    ⟨evm2, hstore0Raw⟩
  have hstore0 :
      storageLocStore evm1 (uint112Loc0 ⟨8⟩) (uniswapUint256Value balance0) =
        some evm2 := by
    simpa [uniswapUint256Value] using hstore0Raw
  rcases uniswapStorageLocStore_uint112_offset14_int_some
      (evm := evm2) (slot := ⟨8⟩) (n := Int.ofNat balance1.toNat) with
    ⟨evm3, hstore1Raw⟩
  have hstore1 :
      storageLocStore evm2 (uint112Loc14 ⟨8⟩) (uniswapUint256Value balance1) =
        some evm3 := by
    simpa [uniswapUint256Value] using hstore1Raw
  rcases uniswapStorageLocStore_uint32_offset28_int_some
      (evm := evm3) (slot := ⟨8⟩) (n := syncBlockTimestampInt evm1) with
    ⟨evm4, hstoreTsRaw⟩
  have hstoreTs :
      storageLocStore evm3 (uint32Loc28 ⟨8⟩) (syncBlockTimestampValue evm1) =
        some evm4 := by
    simpa [syncBlockTimestampValue] using hstoreTsRaw
  refine ⟨evm2, evm3, evm4, hstore0, hstore1, hstoreTs, ?_⟩
  have hassigns :
      ExecBlock config
        { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 } evm1
        [ .assign .storage reserve0Ref (.var "balance0"),
          .assign .storage reserve1Ref (.var "balance1"),
          .assign .storage blockTimestampLastRef (.var "blockTimestamp") ]
        (.ok
          { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
          evm4) := by
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_balance0_afterTimestamp evm1 evm1 balance0 balance1)
        (uniswapAssignReserve0OfStore evm1 evm2
          (syncBlockTimestampStore evm1 balance0 balance1) balance0
          (by simp [syncBlockTimestampStore, syncBalanceStore, uniswapBalanceOfStore])
          hstore0))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_balance1_afterTimestamp evm2 evm1 balance0 balance1)
        (uniswapAssignReserve1OfStore evm2 evm3
          (syncBlockTimestampStore evm1 balance0 balance1) balance1
          (by simp [syncBlockTimestampStore, syncBalanceStore, uniswapBalanceOfStore])
          hstore1))
      ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_sync_blockTimestamp_var evm3 evm1 balance0 balance1)
        (uniswapAssignBlockTimestampLastOfStore evm3 evm4
          (syncBlockTimestampStore evm1 balance0 balance1) (syncBlockTimestampValue evm1)
          (by simp [syncBlockTimestampStore, syncBalanceStore, uniswapBalanceOfStore])
          (by simp)
          hstoreTs))
      ExecBlock.nil
  simpa [updateReservesStmts, syncUpdateTimestampBody, syncUpdateBoundsBody, List.append_assoc]
    using execBlock_append hprefix hassigns

theorem uniswapSyncSuccessSource (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ∃ evm2 : EVM.State, ∃ evm3 : EVM.State, ∃ evm4 : EVM.State,
      storageLocStore evm1 (uint112Loc0 ⟨8⟩) (uniswapUint256Value balance0) = some evm2 ∧
      storageLocStore evm2 (uint112Loc14 ⟨8⟩) (uniswapUint256Value balance1) = some evm3 ∧
      storageLocStore evm3 (uint32Loc28 ⟨8⟩) (syncBlockTimestampValue evm1) = some evm4 ∧
      ExecBlock config { contract := contract, locals := ∅ } evm syncTransition.body
        (.ok { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
          (uniswapLockExitedState evm4)) := by
  rcases uniswapSyncUpdateReservesPrefix
      (evm := evm) (evm0 := evm0) (evm1 := evm1)
      (balance0 := balance0) (balance1 := balance1)
      hwv hunlocked hcall0 hdec0 hcall1 hdec1 hbound0 hbound1 with
    ⟨evm2, evm3, evm4, hstore0, hstore1, hstoreTs, hprefix⟩
  have hexit :
      ExecBlock config
        { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 } evm4
        lockExit
        (.ok
          { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
          (uniswapLockExitedState evm4)) := by
    exact uniswapLockExitSuffix evm4 (syncBlockTimestampStore evm1 balance0 balance1)
      (by simp [syncBlockTimestampStore, syncBalanceStore, uniswapBalanceOfStore])
  refine ⟨evm2, evm3, evm4, hstore0, hstore1, hstoreTs, ?_⟩
  change ExecBlock config { contract := contract, locals := ∅ } evm
    (lockEnter ++
      [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
        .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ] ++
      updateReservesStmts (.var "balance0") (.var "balance1") ++
      lockExit)
    (.ok { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
      (uniswapLockExitedState evm4))
  simpa [List.append_assoc] using execBlock_append hprefix hexit

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
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0)) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncFirstCallFailureSource evm evm0 hwv hunlocked hcall0)

theorem uniswapSyncBodyReverts_firstCallDecode (evm evm0 : EVM.State) {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncFirstCallDecodeRevertSource evm evm0 hwv hunlocked hcall0 hdec0)

theorem uniswapSyncBodyReverts_secondCallFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondCallFailureSource evm evm0 evm1 hwv hunlocked hcall0 hdec0 hcall1)

theorem uniswapSyncBodyReverts_secondCallDecode (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondCallDecodeRevertSource evm evm0 evm1 hwv hunlocked hcall0 hdec0
      hcall1 hdec1)

theorem uniswapSyncBodyReverts_firstBoundFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : maxUint112 < Int.ofNat balance0.toNat) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncFirstBoundFailureSource evm evm0 evm1 hwv hunlocked hcall0 hdec0
      hcall1 hdec1 hbound0)

theorem uniswapSyncBodyReverts_secondBoundFailure (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecTransitionBody config contract evm ∅ syncTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSyncSecondBoundFailureSource evm evm0 evm1 hwv hunlocked hcall0 hdec0
      hcall1 hdec1 hbound0 hbound1)

theorem uniswapSyncBodyReturns (evm evm0 evm1 : EVM.State)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 =
      some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 =
      some (uniswapUint256Value balance1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112) :
    ∃ evm2 : EVM.State, ∃ evm3 : EVM.State, ∃ evm4 : EVM.State,
      storageLocStore evm1 (uint112Loc0 ⟨8⟩) (uniswapUint256Value balance0) = some evm2 ∧
      storageLocStore evm2 (uint112Loc14 ⟨8⟩) (uniswapUint256Value balance1) = some evm3 ∧
      storageLocStore evm3 (uint32Loc28 ⟨8⟩) (syncBlockTimestampValue evm1) = some evm4 ∧
      ExecTransitionBody config contract evm ∅ syncTransition.body
        (.returned
          { contract := contract, locals := syncBlockTimestampStore evm1 balance0 balance1 }
          (uniswapLockExitedState evm4) none) := by
  rcases uniswapSyncSuccessSource
      (evm := evm) (evm0 := evm0) (evm1 := evm1)
      (balance0 := balance0) (balance1 := balance1)
      hwv hunlocked hcall0 hdec0 hcall1 hdec1 hbound0 hbound1 with
    ⟨evm2, evm3, evm4, hstore0, hstore1, hstoreTs, hblock⟩
  refine ⟨evm2, evm3, evm4, hstore0, hstore1, hstoreTs, ?_⟩
  exact ExecFuncBody.execBlockOK hblock

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

end UniswapV2Pair
