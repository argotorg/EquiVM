import Examples.UniswapV2Pair.SwapLock
import Examples.UniswapV2Pair.PositiveWordsSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapOutputRequireExpr : Expr :=
  .binary .or (.binary .gt (.var "amount0Out") (.intLit 0))
    (.binary .gt (.var "amount1Out") (.intLit 0))
abbrev swapOutputRequireStmt : Stmt := .require swapOutputRequireExpr

theorem evalExpr_swap_outputRequire (evm : EVM.State) {locals : Store}
    {amount0 amount1 : UInt256}
    (ha0 : locals.get? "amount0Out" = some (uniswapUint256Value amount0))
    (ha1 : locals.get? "amount1Out" = some (uniswapUint256Value amount1)) :
    evalExpr? config { contract := contract, locals := locals } evm swapOutputRequireExpr =
      .ok (.bool (decide (0 < amount0.toNat ∨ 0 < amount1.toNat))) := by
  exact evalExpr_uint256_vars_positiveOr evm "amount0Out" "amount1Out" amount0 amount1 ha0 ha1

theorem uniswapSwapBodyReverts_outputZero (evm : EVM.State) (I : ExecutionEnv)
    (hlock : ExecBlock config { contract := contract, locals := swapStore I } evm lockEnter
      (.ok { contract := contract, locals := swapStore I } (uniswapLockEnteredState evm)))
    (hzero : ¬ (0 < (swapAmount0OutWord I).toNat ∨ 0 < (swapAmount1OutWord I).toNat)) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  have hreq := evalExpr_swap_outputRequire (uniswapLockEnteredState evm)
    (swapStore_amount0Out I) (swapStore_amount1Out I)
  have htail : ExecBlock config { contract := contract, locals := swapStore I }
      (uniswapLockEnteredState evm) [swapOutputRequireStmt] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [hzero, decide_false] using hreq))
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapOutputRequireStmt, swapOutputRequireExpr, List.append_assoc,
      List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hlock htail) (by intro f e h; cases h))

abbrev swapOutputPrefix : List Stmt := lockEnter ++ [swapOutputRequireStmt]

theorem uniswapSwapOutputPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hlock : ExecBlock config { contract := contract, locals := swapStore I } evm lockEnter
      (.ok { contract := contract, locals := swapStore I } (uniswapLockEnteredState evm)))
    (hpos : 0 < (swapAmount0OutWord I).toNat ∨ 0 < (swapAmount1OutWord I).toNat) :
    ExecBlock config { contract := contract, locals := swapStore I } evm swapOutputPrefix
      (.ok { contract := contract, locals := swapStore I } (uniswapLockEnteredState evm)) := by
  have hreq := evalExpr_swap_outputRequire (uniswapLockEnteredState evm)
    (swapStore_amount0Out I) (swapStore_amount1Out I)
  exact execBlock_append hlock (ExecBlock.consNormal
    (ExecStmt.requireTrue (by simpa only [hpos, decide_true] using hreq)) ExecBlock.nil)

end UniswapV2Pair
