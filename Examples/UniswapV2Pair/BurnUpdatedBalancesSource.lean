import Examples.UniswapV2Pair.BurnTransfersSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev burnAfterTransfersStore (locals : Store) : Store := (locals.insert "ok0" .unit).insert "ok1" .unit
abbrev burnBeforeUpdatedBalancesPrefix : List Stmt :=
  burnBeforeTransfersPrefix ++
    safeTransferStmts (.var "_token0") (.var "to") (.var "amount0") "ok0" "_ret0" ++
    safeTransferStmts (.var "_token1") (.var "to") (.var "amount1") "ok1" "_ret1"

theorem uniswapBurnBeforeUpdatedBalancesPrefix (evm evmT evmT0 evmT1 : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm
      burnBeforeTransfersPrefix (.ok { contract := contract, locals := locals } evmT))
    (hfirst : ExecStmt config { contract := contract, locals := locals } evmT
      (.internalCall "_safeTransfer" [.var "_token0", .var "to", .var "amount0"] "ok0")
      (.ok (resumeAfterInternalCall { contract := contract, locals := locals } "ok0" none) evmT0))
    (hsecond : ExecStmt config (resumeAfterInternalCall { contract := contract, locals := locals } "ok0" none) evmT0
      (.internalCall "_safeTransfer" [.var "_token1", .var "to", .var "amount1"] "ok1")
      (.ok (resumeAfterInternalCall (resumeAfterInternalCall { contract := contract, locals := locals } "ok0" none) "ok1" none) evmT1)) :
    ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeUpdatedBalancesPrefix
      (.ok { contract := contract, locals := burnAfterTransfersStore locals } evmT1) := by
  exact execBlock_append (execBlock_append hprefix (ExecBlock.consNormal hfirst ExecBlock.nil))
    (ExecBlock.consNormal hsecond ExecBlock.nil)

theorem burnAfterTransfersStore_tokens (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) :
    let locals := burnAfterTransfersStore (burnAfterInternalStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn)
    locals.get? "_token0" = some (.address (uniswapAddressAtSlot reserveEvm ⟨6⟩)) ∧
    locals.get? "_token1" = some (.address (uniswapAddressAtSlot reserveEvm ⟨7⟩)) := by
  obtain ⟨ht0, ht1, _⟩ := burnAfterInternalStore_transferGets reserveEvm callEvm feeEvm I balance0 balance1 feeOn
  dsimp only
  unfold burnAfterTransfersStore
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    exact ht0
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    exact ht1

theorem uniswapBurnBodyReverts_updatedBalance0 (evm evmT : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm
      burnBeforeUpdatedBalancesPrefix (.ok { contract := contract, locals := locals } evmT))
    (hcall : ExecBlock config { contract := contract, locals := locals } evmT
      (balanceOfThisStmts (.var "_token0") "newBalance0") .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeUpdatedBalancesPrefix, burnBeforeTransfersPrefix, burnBeforeAmountsPrefix,
      burnBeforeFeePrefix, burnCachePrefix, burnAmount0Stmt, burnAmount1Stmt,
      burnAmountsRequireStmt, burnAmountsRequireExpr, burnInternalBurnStmt, List.append_assoc] using
      execBlock_append_term (execBlock_append hprefix hcall) (by intro f e h; cases h))

abbrev burnBeforeUpdatePrefix : List Stmt := burnBeforeUpdatedBalancesPrefix ++
  balanceOfThisStmts (.var "_token0") "newBalance0" ++ balanceOfThisStmts (.var "_token1") "newBalance1"

theorem uniswapBurnBodyReverts_beforeUpdate (evm : EVM.State) (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeUpdatePrefix .reverted) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [burnTransition, burnBeforeUpdatePrefix, burnBeforeUpdatedBalancesPrefix, burnBeforeTransfersPrefix,
      burnBeforeAmountsPrefix, burnBeforeFeePrefix, burnCachePrefix, burnAmount0Stmt, burnAmount1Stmt,
      burnAmountsRequireStmt, burnAmountsRequireExpr, burnInternalBurnStmt, List.append_assoc] using
      execBlock_append_term hprefix (by intro f e h; cases h))

end UniswapV2Pair
