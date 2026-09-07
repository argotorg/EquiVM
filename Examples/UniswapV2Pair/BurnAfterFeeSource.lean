import Examples.UniswapV2Pair.BurnAmountsCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnFeeStore (reserveEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) : Store :=
  (burnLiquidityStore reserveEvm callEvm I balance0 balance1).insert "feeOn" (.bool feeOn)

abbrev burnTotalSupplyStore (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) : Store :=
  (burnFeeStore reserveEvm callEvm I balance0 balance1 feeOn).insert "_totalSupply"
    (uniswapUint256Value (mintFunctionTotalSupplyWord feeEvm))

theorem uniswapBurnTotalSupplyLet (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) :
    ExecBlock config
      { contract := contract, locals := burnFeeStore reserveEvm callEvm I balance0 balance1 feeOn }
      feeEvm [.letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef)]
      (.ok { contract := contract, locals :=
        burnTotalSupplyStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn } feeEvm) := by
  apply uniswapMintTotalSupplyLet
  simp [burnFeeStore, burnLiquidityStore, burnBalanceStore, burnBalance0Store,
    burnCacheStore, burnReserveStore, burnStore]

theorem burnTotalSupplyStore_gets (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) :
    let locals := burnTotalSupplyStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn
    locals.get? "liquidity" = some (uniswapUint256Value (burnLiquidityWord callEvm)) ∧
    locals.get? "balance0" = some (uniswapUint256Value balance0) ∧
    locals.get? "balance1" = some (uniswapUint256Value balance1) ∧
    locals.get? "_totalSupply" = some (uniswapUint256Value (mintFunctionTotalSupplyWord feeEvm)) := by
  dsimp only
  unfold burnTotalSupplyStore burnFeeStore burnLiquidityStore burnBalanceStore burnBalance0Store
  constructor
  · repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  constructor
  · repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  constructor
  · repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  · exact store_get_self _ _ _

abbrev burnBeforeAmountsPrefix : List Stmt :=
  burnBeforeFeePrefix ++ [.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn",
    .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef)]

theorem uniswapBurnBeforeAmountsPrefix
    (evm evm1 evmFee : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeFeePrefix
      (.ok { contract := contract, locals :=
        burnLiquidityStore (uniswapLockEnteredState evm) evm1 I balance0 balance1 } evm1))
    (hfee : ExecStmt config
      { contract := contract, locals :=
        burnLiquidityStore (uniswapLockEnteredState evm) evm1 I balance0 balance1 } evm1
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      (.ok (resumeAfterInternalCall
        { contract := contract, locals :=
          burnLiquidityStore (uniswapLockEnteredState evm) evm1 I balance0 balance1 }
        "feeOn" (some [.bool feeOn])) evmFee)) :
    ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeAmountsPrefix
      (.ok { contract := contract, locals :=
        burnTotalSupplyStore (uniswapLockEnteredState evm) evm1 evmFee I balance0 balance1 feeOn } evmFee) := by
  exact execBlock_append hprefix
    (ExecBlock.consNormal hfee (uniswapBurnTotalSupplyLet _ _ _ _ _ _ _))

theorem uniswapBurnBodyReverts_amounts
    (evm evm1 evmFee : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) (feeOn : Bool)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeAmountsPrefix
      (.ok { contract := contract, locals :=
        burnTotalSupplyStore (uniswapLockEnteredState evm) evm1 evmFee I balance0 balance1 feeOn } evmFee))
    (hamounts : ExecBlock config
      { contract := contract, locals :=
        burnTotalSupplyStore (uniswapLockEnteredState evm) evm1 evmFee I balance0 balance1 feeOn } evmFee
      [burnAmount0Stmt, burnAmount1Stmt] .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeAmountsPrefix, burnBeforeFeePrefix, burnCachePrefix,
      burnAmount0Stmt, burnAmount1Stmt, List.append_assoc] using
      execBlock_append_term (execBlock_append hprefix hamounts) (by intro f e h; cases h))

end UniswapV2Pair
