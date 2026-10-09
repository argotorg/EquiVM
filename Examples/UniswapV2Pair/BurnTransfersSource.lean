import Examples.UniswapV2Pair.BurnTransfersRuntime
import Examples.UniswapV2Pair.SafeTransferCallCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnAfterInternalStore (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) : Store :=
  (burnAmountsStore (burnTotalSupplyStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn)
    (burnLiquidityWord callEvm) balance0 balance1 (mintFunctionTotalSupplyWord feeEvm)).insert
    "_burnResult" .unit

theorem burnAfterInternalStore_transferGets
    (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) :
    let locals := burnAfterInternalStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn
    locals.get? "_token0" = some (.address (uniswapAddressAtSlot reserveEvm ⟨6⟩)) ∧
    locals.get? "_token1" = some (.address (uniswapAddressAtSlot reserveEvm ⟨7⟩)) ∧
    locals.get? "to" = some (burnToValue I) ∧
    locals.get? "amount0" = some (uniswapUint256Value
      (burnAmountWord (burnLiquidityWord callEvm) balance0 (mintFunctionTotalSupplyWord feeEvm))) ∧
    locals.get? "amount1" = some (uniswapUint256Value
      (burnAmountWord (burnLiquidityWord callEvm) balance1 (mintFunctionTotalSupplyWord feeEvm))) := by
  dsimp only
  unfold burnAfterInternalStore burnAmountsStore burnTotalSupplyStore burnFeeStore burnLiquidityStore
    burnBalanceStore burnBalance0Store burnCacheStore burnReserveStore burnStore
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals repeat' first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]

theorem evalExprs_burn_firstSafeTransferArgs
    (reserveEvm callEvm feeEvm transferEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) :
    evalExprs? config
      { contract := contract, locals := burnAfterInternalStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn }
      transferEvm [.var "_token0", .var "to", .var "amount0"] =
      .ok (safeTransferArgs (uniswapAddressAtSlot reserveEvm ⟨6⟩)
        (AccountAddress.ofNat (burnToWord I).toNat)
        (burnAmountWord (burnLiquidityWord callEvm) balance0 (mintFunctionTotalSupplyWord feeEvm))) := by
  obtain ⟨ht0, _, hto, ha0, _⟩ :=
    burnAfterInternalStore_transferGets reserveEvm callEvm feeEvm I balance0 balance1 feeOn
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, ht0, hto, ha0, EvalResult.bind, bind, pure]

theorem uniswapBurnBodyReverts_firstTransfer (evm evmT : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm
      burnBeforeTransfersPrefix (.ok { contract := contract, locals := locals } evmT))
    (htransfer : ExecStmt config { contract := contract, locals := locals } evmT
      (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "amount0"] "ok0") .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  have htail : ExecBlock config { contract := contract, locals := locals } evmT
      (safeTransferStmts (.var "_token0") (.var "to") (.var "amount0") "ok0" "_ret0") .reverted :=
    ExecBlock.consRevert htransfer
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeTransfersPrefix, burnBeforeAmountsPrefix,
      burnBeforeFeePrefix, burnCachePrefix, burnAmount0Stmt, burnAmount1Stmt,
      burnAmountsRequireStmt, burnAmountsRequireExpr, burnInternalBurnStmt, List.append_assoc] using
      execBlock_append_term (execBlock_append hprefix htail) (by intro f e h; cases h))

theorem evalExprs_burn_secondSafeTransferArgs
    (reserveEvm callEvm feeEvm transferEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) :
    evalExprs? config
      (resumeAfterInternalCall
        { contract := contract, locals := burnAfterInternalStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn }
        "ok0" none)
      transferEvm [.var "_token1", .var "to", .var "amount1"] =
      .ok (safeTransferArgs (uniswapAddressAtSlot reserveEvm ⟨7⟩)
        (AccountAddress.ofNat (burnToWord I).toNat)
        (burnAmountWord (burnLiquidityWord callEvm) balance1 (mintFunctionTotalSupplyWord feeEvm))) := by
  obtain ⟨_, ht1, hto, _, ha1⟩ := burnAfterInternalStore_transferGets reserveEvm callEvm feeEvm I balance0 balance1 feeOn
  simp only [resumeAfterInternalCall, evalExprs?, evalExpr?,
    store_get_ne _ (k := "ok0") (a := "_token1") .unit (by decide), store_get_ne _ (k := "ok0") (a := "to") .unit (by decide), store_get_ne _ (k := "ok0") (a := "amount1") .unit (by decide),
    EvalResult.ofOption, ht1, hto, ha1, EvalResult.bind, bind, pure]

theorem uniswapBurnBodyReverts_secondTransfer (evm evmT evmT1 : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm
      burnBeforeTransfersPrefix (.ok { contract := contract, locals := locals } evmT))
    (hfirst : ExecStmt config { contract := contract, locals := locals } evmT
      (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "amount0"] "ok0")
      (.ok (resumeAfterInternalCall { contract := contract, locals := locals } "ok0" none) evmT1))
    (hsecond : ExecStmt config (resumeAfterInternalCall { contract := contract, locals := locals } "ok0" none) evmT1
      (.internalCall "_safeTransfer" [.var "_token1", .var "to", .var "amount1"] "ok1") .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  have htail : ExecBlock config { contract := contract, locals := locals } evmT
      (safeTransferStmts (.var "_token0") (.var "to") (.var "amount0") "ok0" "_ret0" ++
        safeTransferStmts (.var "_token1") (.var "to") (.var "amount1") "ok1" "_ret1") .reverted :=
    ExecBlock.consNormal hfirst (ExecBlock.consRevert hsecond)
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeTransfersPrefix, burnBeforeAmountsPrefix,
      burnBeforeFeePrefix, burnCachePrefix, burnAmount0Stmt, burnAmount1Stmt,
      burnAmountsRequireStmt, burnAmountsRequireExpr, burnInternalBurnStmt, List.append_assoc] using
      execBlock_append_term (execBlock_append hprefix htail) (by intro f e h; cases h))

end UniswapV2Pair
