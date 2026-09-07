import Examples.UniswapV2Pair.BurnAmountsGuardCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem burnAmountsStore_gets (locals : Store) (liquidity balance0 balance1 totalSupply : UInt256)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity)) :
    let next := burnAmountsStore locals liquidity balance0 balance1 totalSupply
    next.get? "liquidity" = some (uniswapUint256Value liquidity) ∧
    next.get? "amount0" = some (uniswapUint256Value (burnAmountWord liquidity balance0 totalSupply)) ∧
    next.get? "amount1" = some (uniswapUint256Value (burnAmountWord liquidity balance1 totalSupply)) := by
  dsimp only
  unfold burnAmountsStore
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    exact hliq
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_self]
  · exact store_get_self _ _ _

abbrev burnBeforeTransfersPrefix : List Stmt :=
  burnBeforeAmountsPrefix ++ [burnAmount0Stmt, burnAmount1Stmt] ++
    [burnAmountsRequireStmt, burnInternalBurnStmt]

theorem uniswapBurnBodyReverts_beforeTransfers (evm : EVM.State) (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm
      burnBeforeTransfersPrefix .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeTransfersPrefix, burnBeforeAmountsPrefix,
      burnBeforeFeePrefix, burnCachePrefix, burnAmount0Stmt, burnAmount1Stmt,
      burnAmountsRequireStmt, burnAmountsRequireExpr, burnInternalBurnStmt, List.append_assoc] using
      execBlock_append_term hprefix (by intro f e h; cases h))

end UniswapV2Pair
