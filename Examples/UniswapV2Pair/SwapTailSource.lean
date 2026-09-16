import Examples.UniswapV2Pair.SwapUpdateSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

theorem swapBeforeUpdateFrame_unlocked (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 amount0In amount1In : UInt256) :
    (swapBeforeUpdateFrame evm I balance0 balance1 amount0In amount1In).locals.get? "unlocked" = none := by
  unfold swapBeforeUpdateFrame
  rw [swapAfterAdjustmentsFrame_get_ne _ _ _ _ (by decide) (by decide),
    swapAfterInputsFrame_get_ne _ _ _ _ (by decide) (by decide)]
  unfold swapBeforeInputsFrame
  rw [swapAfterBalancesFrame_get_ne _ _ _ _ (by decide) (by decide),
    swapAfterCallbackFrame_get_ne _ _ _ (by decide),
    swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]
  change (swapTokenStore evm I).get? "unlocked" = none
  unfold swapTokenStore swapReserveStore swapStore
  repeat' rw [store_get_ne _ _ (by decide)]
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

theorem uniswapSwapBodyReturns_afterUpdate (evm evmU evmR : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapInvariantPrefix
      (.ok { contract := contract, locals := locals } evmU))
    (hupdate : ExecStmt config { contract := contract, locals := locals } evmU
      (.internalCall "_update" [.var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1"]
        "_updateResult")
      (.ok (resumeAfterInternalCall { contract := contract, locals := locals } "_updateResult" none) evmR))
    (hu : locals.get? "unlocked" = none) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body
      (.returned (resumeAfterInternalCall { contract := contract, locals := locals } "_updateResult" none)
        (uniswapLockExitedState evmR) none) := by
  have htail := uniswapLockExitSuffix evmR (locals.insert "_updateResult" .unit)
    (by rw [store_get_ne _ _ (by decide)]; exact hu)
  apply ExecFuncBody.execBlockOK
  simpa only [swapTransition, swapInvariantPrefix, swapAdjustmentPrefix, swapInputGuardPrefix,
    swapInputsPrefix, swapBalancesPrefix, swapCallbackPrefix, swapTransferPrefix, swapRecipientGuardPrefix,
    swapTokenPrefix, swapReserveGuardPrefix, swapReservePrefix, swapOutputPrefix, swapOutputRequireStmt,
    swapOutputRequireExpr, swapReserveRequireStmt, swapReserveRequireExpr, swapRecipientRequireStmt,
    swapRecipientRequireExpr, swapFirstTransferStmt, swapSecondTransferStmt, swapCallbackStmt,
    swapCallbackCondition, swapCallbackBody, swapBalanceStmts, swapInputStmts, swapInputExpr,
    swapInputRequireStmt, swapInputRequireExpr, swapAdjustmentStmts, swapAdjustedExpr,
    swapInvariantStmt, swapInvariantExpr, updateReservesStmtsWith,
    List.append_assoc, List.cons_append, List.nil_append] using
    execBlock_append hprefix (ExecBlock.consNormal hupdate htail)

end UniswapV2Pair
