import Examples.UniswapV2Pair.SwapInvariantSource
import Examples.UniswapV2Pair.UpdateCallSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: express a frame with known contract using its locals.
theorem frame_eq_of_contract {caller : Frame} {decl : ContractDecl} (h : caller.contract = decl) :
    caller = { contract := decl, locals := caller.locals } := by
  cases caller
  dsimp only at h ⊢
  cases h
  rfl

abbrev swapBeforeUpdateFrame (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 amount0In amount1In : UInt256) : Frame :=
  swapAfterAdjustmentsFrame
    (swapAfterInputsFrame (swapBeforeInputsFrame evm I balance0 balance1) amount0In amount1In)
    (swapAdjustedWord balance0 amount0In) (swapAdjustedWord balance1 amount1In)

theorem swapBeforeUpdateFrame_contract (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 amount0In amount1In : UInt256) :
    (swapBeforeUpdateFrame evm I balance0 balance1 amount0In amount1In).contract = contract := by
  simp only [swapAfterCallbackFrame_contract, swapAfterTransfersFrame_contract]

theorem swapBeforeUpdateFrame_balances (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 amount0In amount1In : UInt256) :
    (swapBeforeUpdateFrame evm I balance0 balance1 amount0In amount1In).locals.get? "balance0" =
      some (uniswapUint256Value balance0) ∧
    (swapBeforeUpdateFrame evm I balance0 balance1 amount0In amount1In).locals.get? "balance1" =
      some (uniswapUint256Value balance1) := by
  obtain ⟨hb0, hb1, _⟩ := swapBeforeInputsFrame_gets evm I balance0 balance1
  constructor
  all_goals
    unfold swapBeforeUpdateFrame
    rw [swapAfterAdjustmentsFrame_get_ne _ _ _ _ (by decide) (by decide),
      swapAfterInputsFrame_get_ne _ _ _ _ (by decide) (by decide)]
  · exact hb0
  · exact hb1

theorem evalExprs_swap_updateArgs {caller : Frame} (evm : EVM.State)
    (balance0 balance1 reserve0 reserve1 : UInt256)
    (hb0 : caller.locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : caller.locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hr0 : caller.locals.get? "_reserve0" = some (uniswapUint256Value reserve0))
    (hr1 : caller.locals.get? "_reserve1" = some (uniswapUint256Value reserve1)) :
    evalExprs? config caller evm [.var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1"] =
      .ok (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1) := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hb0, hb1, hr0, hr1, EvalResult.bind, bind, pure,
    syncUpdateCallArgValsWith]

theorem uniswapSwapBodyReverts_updateCall (evm evmU : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapInvariantPrefix
      (.ok { contract := contract, locals := locals } evmU))
    (hcall : ExecStmt config { contract := contract, locals := locals } evmU
      (.internalCall "_update" [.var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1"]
        "_updateResult") .reverted) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := locals } evmU
      (updateReservesStmtsWith (.var "balance0") (.var "balance1") (.var "_reserve0") (.var "_reserve1")) .reverted :=
    ExecBlock.consRevert hcall
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapInvariantPrefix, swapAdjustmentPrefix, swapInputGuardPrefix,
      swapInputsPrefix, swapBalancesPrefix, swapCallbackPrefix, swapTransferPrefix, swapRecipientGuardPrefix,
      swapTokenPrefix, swapReserveGuardPrefix, swapReservePrefix, swapOutputPrefix, swapOutputRequireStmt,
      swapOutputRequireExpr, swapReserveRequireStmt, swapReserveRequireExpr, swapRecipientRequireStmt,
      swapRecipientRequireExpr, swapFirstTransferStmt, swapSecondTransferStmt, swapCallbackStmt,
      swapCallbackCondition, swapCallbackBody, swapBalanceStmts, swapInputStmts, swapInputExpr,
      swapInputRequireStmt, swapInputRequireExpr, swapAdjustmentStmts, swapAdjustedExpr,
      swapInvariantStmt, swapInvariantExpr, List.append_assoc, List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix hblock) (by intro f e h; cases h))

end UniswapV2Pair
