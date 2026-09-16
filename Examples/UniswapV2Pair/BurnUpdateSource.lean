import Examples.UniswapV2Pair.BurnUpdatedBalancesSource
import Examples.UniswapV2Pair.UpdateCallSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnBeforeUpdateStore (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) (newBalance0 newBalance1 : UInt256) : Store :=
  ((burnAfterTransfersStore (burnAfterInternalStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn)).insert
    "newBalance0" (uniswapUint256Value newBalance0)).insert "newBalance1" (uniswapUint256Value newBalance1)

theorem burnBeforeUpdateStore_gets (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) (newBalance0 newBalance1 : UInt256) :
    let locals := burnBeforeUpdateStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn newBalance0 newBalance1
    locals.get? "newBalance0" = some (uniswapUint256Value newBalance0) ∧
    locals.get? "newBalance1" = some (uniswapUint256Value newBalance1) ∧
    locals.get? "_reserve0" = some (uniswapUint256Value (uniswapReserve0Word reserveEvm)) ∧
    locals.get? "_reserve1" = some (uniswapUint256Value (uniswapReserve1Word reserveEvm)) ∧
    locals.get? "feeOn" = some (.bool feeOn) ∧
    locals.get? "amount0" = some (uniswapUint256Value
      (burnAmountWord (burnLiquidityWord callEvm) balance0 (mintFunctionTotalSupplyWord feeEvm))) ∧
    locals.get? "amount1" = some (uniswapUint256Value
      (burnAmountWord (burnLiquidityWord callEvm) balance1 (mintFunctionTotalSupplyWord feeEvm))) := by
  dsimp only
  unfold burnBeforeUpdateStore burnAfterTransfersStore burnAfterInternalStore burnAmountsStore
    burnTotalSupplyStore burnFeeStore burnLiquidityStore burnBalanceStore burnBalance0Store
    burnCacheStore burnReserveStore burnStore
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem evalExprs_burn_updateArgs (reserveEvm callEvm feeEvm updateEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) (newBalance0 newBalance1 : UInt256) :
    evalExprs? config
      { contract := contract,
        locals := burnBeforeUpdateStore reserveEvm callEvm feeEvm I
          balance0 balance1 feeOn newBalance0 newBalance1 } updateEvm
      [.var "newBalance0", .var "newBalance1", .var "_reserve0", .var "_reserve1"] =
      .ok (syncUpdateCallArgValsWith newBalance0 newBalance1
        (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm)) := by
  obtain ⟨hn0, hn1, hr0, hr1, _⟩ := burnBeforeUpdateStore_gets reserveEvm callEvm feeEvm I
    balance0 balance1 feeOn newBalance0 newBalance1
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hn0, hn1, hr0, hr1, EvalResult.bind, bind, pure,
    syncUpdateCallArgValsWith]

theorem uniswapBurnBodyReverts_updateCall (evm evmU : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm
      burnBeforeUpdatePrefix (.ok { contract := contract, locals := locals } evmU))
    (hcall : ExecStmt config { contract := contract, locals := locals } evmU
      (.internalCall "_update" [.var "newBalance0", .var "newBalance1", .var "_reserve0", .var "_reserve1"]
        "_updateResult") .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := locals } evmU
      (updateReservesStmtsWith (.var "newBalance0") (.var "newBalance1") (.var "_reserve0") (.var "_reserve1")) .reverted :=
    ExecBlock.consRevert hcall
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeUpdatePrefix, burnBeforeUpdatedBalancesPrefix, burnBeforeTransfersPrefix,
      burnBeforeAmountsPrefix, burnBeforeFeePrefix, burnCachePrefix, burnAmount0Stmt, burnAmount1Stmt,
      burnAmountsRequireStmt, burnAmountsRequireExpr, burnInternalBurnStmt, List.append_assoc] using
      execBlock_append_term (execBlock_append hprefix hblock) (by intro f e h; cases h))

end UniswapV2Pair
