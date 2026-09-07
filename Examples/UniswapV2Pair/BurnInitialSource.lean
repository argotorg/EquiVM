import Examples.UniswapV2Pair.BurnCommon
import Examples.UniswapV2Pair.MintCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnReserveStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((burnStore I).insert "_reserve0" (uniswapUint256Value (uniswapReserve0Word evm))).insert
    "_reserve1" (uniswapUint256Value (uniswapReserve1Word evm))

abbrev burnCacheStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((burnReserveStore evm I).insert "_token0" (.address (uniswapAddressAtSlot evm ⟨6⟩))).insert
    "_token1" (.address (uniswapAddressAtSlot evm ⟨7⟩))

abbrev burnCachePrefix : List Stmt :=
  lockEnter ++
    [ .letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
      .letDecl "_reserve1" (some uint112) (.storage reserve1Ref),
      .letDecl "_token0" (some addr) (.storage token0Ref),
      .letDecl "_token1" (some addr) (.storage token1Ref) ]

theorem uniswapBurnCachePrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := burnStore I } evm burnCachePrefix
      (.ok { contract := contract, locals := burnCacheStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) := by
  let evmL := uniswapLockEnteredState evm
  have hres := uniswapMintReservePrefix evm I hwv hunlocked
  have htok0 : evalExpr? config { contract := contract, locals := burnReserveStore evmL I }
      evmL (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    exact evalExpr_uniswap_storage_address evmL (burnReserveStore evmL I)
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [burnReserveStore, burnStore, token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) rfl
  have htok1 : evalExpr? config
      { contract := contract, locals := ((burnReserveStore evmL I).insert "_token0"
          (.address (uniswapAddressAtSlot evmL ⟨6⟩))) }
      evmL (.storage token1Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨7⟩)) := by
    exact evalExpr_uniswap_storage_address evmL _
      (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (by simp [burnReserveStore, burnStore, token1Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) rfl
  have htokens : ExecBlock config { contract := contract, locals := burnReserveStore evmL I }
      evmL [.letDecl "_token0" (some addr) (.storage token0Ref),
        .letDecl "_token1" (some addr) (.storage token1Ref)]
      (.ok { contract := contract, locals := burnCacheStore evmL I } evmL) :=
    ExecBlock.consNormal (ExecStmt.letDecl htok0)
      (ExecBlock.consNormal (ExecStmt.letDecl htok1) ExecBlock.nil)
  simpa only [burnCachePrefix, List.append_assoc] using execBlock_append hres htokens

theorem uniswapAddressAtSlot_eq_runtime
    {σ : AccountMap} {I : ExecutionEnv} {evm : EVM.State} (slot : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I) :
    uniswapAddressAtSlot evm slot =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask (uniswapSlotWord slot σ I)) := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  simp only [uniswapAddressAtSlot, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, henv, uniswapSlotWord, ← hslot,
    accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm]

-- LIBRARY CANDIDATE: evaluating a code-existence guard from coupled accounts and an address value.
theorem evalExpr_uniswap_codeGuard
    {σ : AccountMap} {evm : EVM.State} {frame : Frame} {receiver : Expr}
    {target : UInt256} {addr : AccountAddress}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hreceiver : evalExpr? config frame evm receiver = .ok (.address addr)) :
    evalExpr? config frame evm (.binary .gt (.extCodeSize receiver) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord σ target).toNat))) := by
  have hword : EVM.Word.ofNat
      ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
      extCodeSizeWord σ target := by
    rw [extCodeSizeWord_accountMapEquiv hAccounts]
    cases hacc : evm.accountMap.find? addr <;>
      simp [State.lookupAccount, extCodeSizeWord, ← haddr, hacc, Option.option] <;> rfl
  simp [evalExpr?, hreceiver, EvalResult.bind, bind, pure, evalBinaryOp?, hword]

theorem burnCacheStore_token0 (evm : EVM.State) (I : ExecutionEnv) :
    (burnCacheStore evm I).get? "_token0" = some (.address (uniswapAddressAtSlot evm ⟨6⟩)) := by
  rw [burnCacheStore, store_get_ne _ _ (by decide), store_get_self]

theorem burnCacheStore_token1 (evm : EVM.State) (I : ExecutionEnv) :
    (burnCacheStore evm I).get? "_token1" = some (.address (uniswapAddressAtSlot evm ⟨7⟩)) := by
  rw [burnCacheStore, store_get_self]

theorem uniswapBurnBodyReverts_firstNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard : evalExpr? config
      { contract := contract, locals := burnCacheStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm)
      (.binary .gt (.extCodeSize (.var "_token0")) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  have hprefix := uniswapBurnCachePrefix evm I hwv hunlocked
  have hcall : ExecBlock config
      { contract := contract, locals := burnCacheStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) (balanceOfThisStmts (.var "_token0") "balance0") .reverted := by
    exact checkedExternalCallVarNoCode hguard
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnCachePrefix, List.append_assoc] using
      execBlock_append_term (execBlock_append hprefix hcall) (by intro f e h; cases h))

theorem uniswapBurnBodyReverts_firstBalanceBlock (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hfirst : ExecBlock config
      { contract := contract, locals := burnCacheStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) (balanceOfThisStmts (.var "_token0") "balance0") .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnCachePrefix, List.append_assoc] using
      execBlock_append_term
        (execBlock_append (uniswapBurnCachePrefix evm I hwv hunlocked) hfirst)
        (by intro f e h; cases h))

abbrev burnBalance0Store (evm : EVM.State) (I : ExecutionEnv) (balance0 : UInt256) : Store :=
  (burnCacheStore evm I).insert "balance0" (uniswapUint256Value balance0)

theorem uniswapBurnBodyReverts_secondBalanceBlock
    (evm evm0 : EVM.State) (I : ExecutionEnv) (balance0 : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hfirst : ExecBlock config
      { contract := contract, locals := burnCacheStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) (balanceOfThisStmts (.var "_token0") "balance0")
      (.ok { contract := contract, locals :=
        burnBalance0Store (uniswapLockEnteredState evm) I balance0 } evm0))
    (hsecond : ExecBlock config
      { contract := contract, locals := burnBalance0Store (uniswapLockEnteredState evm) I balance0 }
      evm0 (balanceOfThisStmts (.var "_token1") "balance1") .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnCachePrefix, List.append_assoc] using
      execBlock_append_term
        (execBlock_append (execBlock_append (uniswapBurnCachePrefix evm I hwv hunlocked) hfirst) hsecond)
        (by intro f e h; cases h))

end UniswapV2Pair
