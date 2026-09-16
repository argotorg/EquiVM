import Examples.UniswapV2Pair.SwapReserveSource
import Examples.UniswapV2Pair.BurnInitialSource
import Examples.UniswapV2Pair.AddressComparison
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapTokenStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((swapReserveStore evm I).insert "_token0" (.address (uniswapAddressAtSlot evm ⟨6⟩))).insert
    "_token1" (.address (uniswapAddressAtSlot evm ⟨7⟩))
abbrev swapTokenPrefix : List Stmt := swapReserveGuardPrefix ++
  [.letDecl "_token0" (some addr) (.storage token0Ref),
    .letDecl "_token1" (some addr) (.storage token1Ref)]
abbrev swapRecipientRequireExpr : Expr :=
  .binary .and (.binary .ne (.var "to") (.var "_token0"))
    (.binary .ne (.var "to") (.var "_token1"))
abbrev swapRecipientRequireStmt : Stmt := .require swapRecipientRequireExpr

theorem uniswapSwapTokenPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hreserve : ExecBlock config { contract := contract, locals := swapStore I } evm swapReserveGuardPrefix
      (.ok { contract := contract, locals := swapReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm))) :
    ExecBlock config { contract := contract, locals := swapStore I } evm swapTokenPrefix
      (.ok { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) := by
  let evmL := uniswapLockEnteredState evm
  have ht0 : evalExpr? config { contract := contract, locals := swapReserveStore evmL I }
      evmL (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) :=
    evalExpr_uniswap_storage_address evmL (swapReserveStore evmL I)
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [swapReserveStore, swapStore, token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) rfl
  have ht1 : evalExpr? config
      { contract := contract, locals := ((swapReserveStore evmL I).insert "_token0"
        (.address (uniswapAddressAtSlot evmL ⟨6⟩))) } evmL (.storage token1Ref) =
      .ok (.address (uniswapAddressAtSlot evmL ⟨7⟩)) :=
    evalExpr_uniswap_storage_address evmL _
      (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (by simp [swapReserveStore, swapStore, token1Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) rfl
  exact execBlock_append hreserve (ExecBlock.consNormal (ExecStmt.letDecl ht0)
    (ExecBlock.consNormal (ExecStmt.letDecl ht1) ExecBlock.nil))

theorem evalExpr_swap_recipientRequire (evm : EVM.State) {locals : Store}
    {toAddr token0 token1 : AccountAddress}
    (hto : locals.get? "to" = some (.address toAddr))
    (ht0 : locals.get? "_token0" = some (.address token0))
    (ht1 : locals.get? "_token1" = some (.address token1)) :
    evalExpr? config { contract := contract, locals := locals } evm swapRecipientRequireExpr =
      .ok (.bool (decide (toAddr ≠ token0 ∧ toAddr ≠ token1))) := by
  simp only [swapRecipientRequireExpr, evalExpr?, EvalResult.ofOption, hto, ht0, ht1,
    EvalResult.bind, bind, pure]
  by_cases hp0 : toAddr = token0 <;> simp [evalBinaryOp?, BEq.beq, hp0]

theorem swapTokenStore_recipientGets (evm : EVM.State) (I : ExecutionEnv) :
    (swapTokenStore evm I).get? "to" = some (swapToValue I) ∧
    (swapTokenStore evm I).get? "_token0" = some (.address (uniswapAddressAtSlot evm ⟨6⟩)) ∧
    (swapTokenStore evm I).get? "_token1" = some (.address (uniswapAddressAtSlot evm ⟨7⟩)) := by
  simp only [swapTokenStore, swapReserveStore]
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), swapStore_to]
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_self]
  · exact store_get_self _ _ _

theorem uniswapSwapBodyReverts_recipientGuard (evm : EVM.State) (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapTokenPrefix
      (.ok { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)))
    (hnot : ¬ (AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩ ∧
      AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  obtain ⟨hto, ht0, ht1⟩ := swapTokenStore_recipientGets (uniswapLockEnteredState evm) I
  have hreq := evalExpr_swap_recipientRequire (uniswapLockEnteredState evm) hto ht0 ht1
  have htail : ExecBlock config
      { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) [swapRecipientRequireStmt] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [hnot, decide_false] using hreq))
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapTokenPrefix, swapReserveGuardPrefix, swapReservePrefix,
      swapOutputPrefix, swapOutputRequireStmt, swapOutputRequireExpr, swapReserveRequireStmt,
      swapReserveRequireExpr, swapRecipientRequireStmt, swapRecipientRequireExpr, List.append_assoc,
      List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix htail) (by intro f e h; cases h))

abbrev swapRecipientGuardPrefix : List Stmt := swapTokenPrefix ++ [swapRecipientRequireStmt]

set_option maxHeartbeats 400000 in
theorem uniswapSwapRecipientGuardPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapTokenPrefix
      (.ok { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)))
    (hvalid : AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩ ∧
      AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩) :
    ExecBlock config { contract := contract, locals := swapStore I } evm swapRecipientGuardPrefix
      (.ok { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) := by
  obtain ⟨hto, ht0, ht1⟩ := swapTokenStore_recipientGets (uniswapLockEnteredState evm) I
  have hreq := evalExpr_swap_recipientRequire (uniswapLockEnteredState evm) hto ht0 ht1
  have hd : decide (AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩ ∧
      AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩) = true :=
    decide_eq_true hvalid
  rw [hd] at hreq
  have hreqTrue : ExecStmt config
      { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) swapRecipientRequireStmt
      (.ok { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) :=
    ExecStmt.requireTrue hreq
  have htail : ExecBlock config
      { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) [swapRecipientRequireStmt]
      (.ok { contract := contract, locals := swapTokenStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) := ExecBlock.consNormal hreqTrue ExecBlock.nil
  exact execBlock_append hprefix htail

theorem swapRecipientValid_iff_runtime {evm : EVM.State} {I : ExecutionEnv} {σ : AccountMap}
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I) :
    (AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot evm ⟨6⟩ ∧
      AccountAddress.ofNat (swapToWord I).toNat ≠ uniswapAddressAtSlot evm ⟨7⟩) ↔
    (UInt256.land (swapToMaskedWord I) solcAddrMask ≠ UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩ σ I) ∧
      UInt256.land (swapToMaskedWord I) solcAddrMask ≠ UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ I)) := by
  have hto : AccountAddress.ofNat (swapToWord I).toNat = AccountAddress.ofUInt256 (swapToMaskedWord I) := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact Value.address.inj (solcAddressValue_masked (swapToWord I))
  have hcTo : (swapToMaskedWord I).toNat < EVM.addressModulus := by
    rw [swapToMaskedWord, u256_land_comm]
    exact solcAddrMask_result_canonical _
  have hc0 : (UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩ σ I)).toNat < EVM.addressModulus := by
    rw [u256_land_comm]; exact solcAddrMask_result_canonical _
  have hc1 : (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ I)).toNat < EVM.addressModulus := by
    rw [u256_land_comm]; exact solcAddrMask_result_canonical _
  rw [hto, uniswapAddressAtSlot_eq_runtime ⟨6⟩ hAccounts henv,
    uniswapAddressAtSlot_eq_runtime ⟨7⟩ hAccounts henv, solcAddrMask_clean hcTo]
  simp only [ne_eq, accountAddress_ofUInt256_eq_iff_of_canonical hcTo hc0,
    accountAddress_ofUInt256_eq_iff_of_canonical hcTo hc1]

end UniswapV2Pair
