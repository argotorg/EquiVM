import Examples.UniswapV2Pair.SwapInputGuardSource
import Examples.UniswapV2Pair.SwapAdjustmentCases
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapAdjustmentPrefix : List Stmt := swapInputGuardPrefix ++ swapAdjustmentStmts

theorem swapAfterInputsFrame_get_ne (caller : Frame) (amount0In amount1In : UInt256) (key : Ident)
    (h0 : ("amount0In" == key) = false) (h1 : ("amount1In" == key) = false) :
    (swapAfterInputsFrame caller amount0In amount1In).locals.get? key = caller.locals.get? key := by
  unfold swapAfterInputsFrame
  rw [store_get_ne _ _ h1, store_get_ne _ _ h0]

theorem swapAfterInputsFrame_adjustmentGets (caller : Frame) (amount0In amount1In balance0 balance1 : UInt256)
    (hb0 : caller.locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : caller.locals.get? "balance1" = some (uniswapUint256Value balance1)) :
    (swapAfterInputsFrame caller amount0In amount1In).locals.get? "balance0" = some (uniswapUint256Value balance0) ∧
    (swapAfterInputsFrame caller amount0In amount1In).locals.get? "balance1" = some (uniswapUint256Value balance1) ∧
    (swapAfterInputsFrame caller amount0In amount1In).locals.get? "amount0In" = some (uniswapUint256Value amount0In) ∧
    (swapAfterInputsFrame caller amount0In amount1In).locals.get? "amount1In" = some (uniswapUint256Value amount1In) := by
  exact ⟨(swapAfterInputsFrame_get_ne _ _ _ _ (by decide) (by decide)).trans hb0,
    (swapAfterInputsFrame_get_ne _ _ _ _ (by decide) (by decide)).trans hb1,
    (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _), store_get_self _ _ _⟩

theorem uniswapSwapBodyReverts_adjustment (evm evmB : EVM.State) (I : ExecutionEnv) (caller : Frame)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapInputGuardPrefix
      (.ok caller evmB))
    (hadjustment : ExecBlock config caller evmB swapAdjustmentStmts .reverted) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapInputGuardPrefix, swapInputsPrefix, swapBalancesPrefix,
      swapCallbackPrefix, swapTransferPrefix, swapRecipientGuardPrefix, swapTokenPrefix,
      swapReserveGuardPrefix, swapReservePrefix, swapOutputPrefix, swapOutputRequireStmt,
      swapOutputRequireExpr, swapReserveRequireStmt, swapReserveRequireExpr, swapRecipientRequireStmt,
      swapRecipientRequireExpr, swapFirstTransferStmt, swapSecondTransferStmt, swapCallbackStmt,
      swapCallbackCondition, swapCallbackBody, swapBalanceStmts, swapInputStmts, swapInputExpr,
      swapInputRequireStmt, swapInputRequireExpr, swapAdjustmentStmts, swapAdjustedExpr,
      List.append_assoc, List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix hadjustment) (by intro f e h; cases h))

end UniswapV2Pair
