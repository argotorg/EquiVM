import Examples.UniswapV2Pair.SwapInputSource
import Examples.UniswapV2Pair.PositiveWordsSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapInputRequireExpr : Expr :=
  .binary .or (.binary .gt (.var "amount0In") (.intLit 0))
    (.binary .gt (.var "amount1In") (.intLit 0))
abbrev swapInputRequireStmt : Stmt := .require swapInputRequireExpr
abbrev swapInputsPrefix : List Stmt := swapBalancesPrefix ++ swapInputStmts
abbrev swapInputGuardPrefix : List Stmt := swapInputsPrefix ++ [swapInputRequireStmt]

theorem evalExpr_swap_inputRequire (caller : Frame) (evm : EVM.State) (amount0In amount1In : UInt256) :
    evalExpr? config (swapAfterInputsFrame caller amount0In amount1In) evm swapInputRequireExpr =
      .ok (.bool (decide (0 < amount0In.toNat ∨ 0 < amount1In.toNat))) := by
  exact evalExpr_uint256_vars_positiveOr evm "amount0In" "amount1In" amount0In amount1In
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)) (store_get_self _ _ _)

theorem uniswapSwapBodyReverts_inputGuard (evm evmB : EVM.State) (I : ExecutionEnv)
    (caller : Frame) (amount0In amount1In : UInt256)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapInputsPrefix
      (.ok (swapAfterInputsFrame caller amount0In amount1In) evmB))
    (hnot : ¬ (0 < amount0In.toNat ∨ 0 < amount1In.toNat)) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  have hreq := evalExpr_swap_inputRequire caller evmB amount0In amount1In
  have hterm := ExecStmt.requireFalse (by simpa only [hnot, decide_false] using hreq)
  have htail : ExecBlock config (swapAfterInputsFrame caller amount0In amount1In) evmB
      [swapInputRequireStmt] .reverted := ExecBlock.consRevert hterm
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapInputsPrefix, swapBalancesPrefix, swapCallbackPrefix,
      swapTransferPrefix, swapRecipientGuardPrefix, swapTokenPrefix, swapReserveGuardPrefix,
      swapReservePrefix, swapOutputPrefix, swapOutputRequireStmt, swapOutputRequireExpr,
      swapReserveRequireStmt, swapReserveRequireExpr, swapRecipientRequireStmt, swapRecipientRequireExpr,
      swapFirstTransferStmt, swapSecondTransferStmt, swapCallbackStmt, swapCallbackCondition,
      swapCallbackBody, swapBalanceStmts, swapInputStmts, swapInputExpr,
      swapInputRequireStmt, swapInputRequireExpr,
      List.append_assoc, List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix htail)
        (by intro f e h; cases h))

theorem uniswapSwapInputGuardSource {caller : Frame} (evm : EVM.State) (amount0In amount1In : UInt256)
    (hpos : 0 < amount0In.toNat ∨ 0 < amount1In.toNat) :
    ExecBlock config (swapAfterInputsFrame caller amount0In amount1In) evm [swapInputRequireStmt]
      (.ok (swapAfterInputsFrame caller amount0In amount1In) evm) := by
  exact ExecBlock.consNormal (ExecStmt.requireTrue
    (by simpa only [hpos, decide_true] using evalExpr_swap_inputRequire caller evm amount0In amount1In)) ExecBlock.nil

end UniswapV2Pair
