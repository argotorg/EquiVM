import Examples.UniswapV2Pair.SwapBalancesCases
import Examples.UniswapV2Pair.SwapCallbackCases
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem swapAfterCallbackFrame_get_ne (caller : Frame) (dataLen : UInt256) (key : Ident)
    (hkey : ("_callback" == key) = false) :
    (swapAfterCallbackFrame caller dataLen).locals.get? key = caller.locals.get? key := by
  unfold swapAfterCallbackFrame
  split
  · rfl
  · exact store_get_ne _ _ hkey

theorem swapAfterCallbackFrame_contract (caller : Frame) (dataLen : UInt256) :
    (swapAfterCallbackFrame caller dataLen).contract = caller.contract := by
  unfold swapAfterCallbackFrame
  split <;> rfl

theorem swapAfterTransfersFrame_contract (caller : Frame) (amount0Out amount1Out : UInt256) :
    (swapAfterTransfersFrame caller amount0Out amount1Out).contract = caller.contract := by
  unfold swapAfterTransfersFrame optionalSafeTransferFrame
  split <;> split <;> rfl

abbrev swapBalancesPrefix : List Stmt := swapCallbackPrefix ++ swapBalanceStmts

theorem uniswapSwapBodyReverts_balances (evm evmB : EVM.State) (I : ExecutionEnv) (caller : Frame)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapCallbackPrefix
      (.ok caller evmB))
    (hbalances : ExecBlock config caller evmB swapBalanceStmts .reverted) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapCallbackPrefix, swapTransferPrefix, swapRecipientGuardPrefix,
      swapTokenPrefix, swapReserveGuardPrefix, swapReservePrefix, swapOutputPrefix,
      swapOutputRequireStmt, swapOutputRequireExpr, swapReserveRequireStmt, swapReserveRequireExpr,
      swapRecipientRequireStmt, swapRecipientRequireExpr, swapFirstTransferStmt, swapSecondTransferStmt,
      swapCallbackStmt, swapCallbackCondition, swapCallbackBody, swapBalanceStmts,
      List.append_assoc, List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix hbalances) (by intro f e h; cases h))

end UniswapV2Pair
