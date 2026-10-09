import Examples.UniswapV2Pair.OptionalSafeTransferSource
import Examples.UniswapV2Pair.SwapRecipientSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapFirstTransferStmt : Stmt :=
  .ite (.binary .gt (.var "amount0Out") (.intLit 0))
    (safeTransferStmts (.var "_token0") (.var "to") (.var "amount0Out") "ok0" "_ret0") []
abbrev swapSecondTransferStmt : Stmt :=
  .ite (.binary .gt (.var "amount1Out") (.intLit 0))
    (safeTransferStmts (.var "_token1") (.var "to") (.var "amount1Out") "ok1" "_ret1") []

abbrev swapAfterTransfersFrame (caller : Frame) (amount0Out amount1Out : UInt256) : Frame :=
  optionalSafeTransferFrame (optionalSafeTransferFrame caller "ok0" amount0Out) "ok1" amount1Out

theorem swapTokenStore_transferGets (evm : EVM.State) (I : ExecutionEnv) :
    (swapTokenStore evm I).get? "_token0" = some (.address (uniswapAddressAtSlot evm ⟨6⟩)) ∧
    (swapTokenStore evm I).get? "_token1" = some (.address (uniswapAddressAtSlot evm ⟨7⟩)) ∧
    (swapTokenStore evm I).get? "to" = some (swapToValue I) ∧
    (swapTokenStore evm I).get? "amount0Out" = some (uniswapUint256Value (swapAmount0OutWord I)) ∧
    (swapTokenStore evm I).get? "amount1Out" = some (uniswapUint256Value (swapAmount1OutWord I)) := by
  obtain ⟨hto, ht0, ht1⟩ := swapTokenStore_recipientGets evm I
  obtain ⟨ha0, ha1, _, _⟩ := swapReserveStore_gets evm I
  refine ⟨ht0, ht1, hto, ?_, ?_⟩
  · rw [swapTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]; exact ha0
  · rw [swapTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]; exact ha1

theorem uniswapSwapBodyReverts_transfers (evm evmT : EVM.State) (I : ExecutionEnv) (caller : Frame)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapRecipientGuardPrefix
      (.ok caller evmT))
    (htransfers : ExecBlock config caller evmT [swapFirstTransferStmt, swapSecondTransferStmt] .reverted) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapRecipientGuardPrefix, swapTokenPrefix, swapReserveGuardPrefix,
      swapReservePrefix, swapOutputPrefix, swapOutputRequireStmt, swapOutputRequireExpr,
      swapReserveRequireStmt, swapReserveRequireExpr, swapRecipientRequireStmt, swapRecipientRequireExpr,
      swapFirstTransferStmt, swapSecondTransferStmt, List.append_assoc, List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix htransfers) (by intro f e h; cases h))

end UniswapV2Pair
