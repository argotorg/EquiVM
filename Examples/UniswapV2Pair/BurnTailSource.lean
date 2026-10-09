import Examples.UniswapV2Pair.MintAfterUpdateCases
import Examples.UniswapV2Pair.BurnUpdateSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev uniswapKLastIfFeeState (evm : EVM.State) (fee : Bool) : EVM.State :=
  if fee then mintKLastUpdatedState evm else evm
abbrev uniswapKLastIfFeeStmt : Stmt := .ite (.var "feeOn")
  [.assign .storage kLastRef (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref)))] []

theorem uniswapKLastIfFeeSource {locals : Store} (evm : EVM.State) (fee : Bool)
    (hfee : locals.get? "feeOn" = some (.bool fee))
    (hr0 : locals.get? "reserve0" = none) (hr1 : locals.get? "reserve1" = none)
    (hk : locals.get? "kLast" = none) :
    ExecStmt config { contract := contract, locals := locals } evm uniswapKLastIfFeeStmt
      (.ok { contract := contract, locals := locals } (uniswapKLastIfFeeState evm fee)) := by
  have heval : evalExpr? config { contract := contract, locals := locals } evm (.var "feeOn") = .ok (.bool fee) := by
    simp only [evalExpr?, EvalResult.ofOption, hfee]
  cases fee with
  | false => exact ExecStmt.iteFalse heval ExecBlock.nil
  | true =>
    exact ExecStmt.iteTrue heval (ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_mint_kLastReserveProduct_of_storage evm hr0 hr1
        (mintFeeReserveProductNat_source_lt evm)) (mintAssignKLastProduct evm hk)) ExecBlock.nil)

abbrev burnAfterUpdateTail : List Stmt := [uniswapKLastIfFeeStmt] ++ lockExit ++ [.return [.var "amount0", .var "amount1"]]

theorem uniswapBurnAfterUpdateSourceReturns {locals : Store} (evm : EVM.State) (fee : Bool) (amount0 amount1 : UInt256)
    (hfee : locals.get? "feeOn" = some (.bool fee))
    (ha0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (ha1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hr0 : locals.get? "reserve0" = none) (hr1 : locals.get? "reserve1" = none)
    (hk : locals.get? "kLast" = none) (hu : locals.get? "unlocked" = none) :
    ExecBlock config { contract := contract, locals := locals } evm burnAfterUpdateTail
      (.returned { contract := contract, locals := locals }
        (uniswapLockExitedState (uniswapKLastIfFeeState evm fee))
        (some [uniswapUint256Value amount0, uniswapUint256Value amount1])) := by
  have hkStep := uniswapKLastIfFeeSource evm fee hfee hr0 hr1 hk
  have hlock := uniswapLockExitSuffix (uniswapKLastIfFeeState evm fee) locals hu
  have hreturn : ExecBlock config { contract := contract, locals := locals }
      (uniswapLockExitedState (uniswapKLastIfFeeState evm fee)) [.return [.var "amount0", .var "amount1"]]
      (.returned { contract := contract, locals := locals }
        (uniswapLockExitedState (uniswapKLastIfFeeState evm fee))
        (some [uniswapUint256Value amount0, uniswapUint256Value amount1])) := by
    exact ExecBlock.consReturn (ExecStmt.return (by
      simp only [evalExprs?, evalExpr?, EvalResult.ofOption, ha0, ha1, EvalResult.bind, bind, pure]))
  exact ExecBlock.consNormal hkStep (execBlock_append hlock hreturn)

theorem burnAfterUpdateStore_bases (reserveEvm callEvm feeEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (feeOn : Bool) (newBalance0 newBalance1 : UInt256) :
    let locals := (burnBeforeUpdateStore reserveEvm callEvm feeEvm I balance0 balance1 feeOn newBalance0 newBalance1).insert "_updateResult" .unit
    locals.get? "reserve0" = none ∧ locals.get? "reserve1" = none ∧ locals.get? "kLast" = none ∧ locals.get? "unlocked" = none := by
  dsimp only
  unfold burnBeforeUpdateStore burnAfterTransfersStore burnAfterInternalStore burnAmountsStore
    burnTotalSupplyStore burnFeeStore burnLiquidityStore burnBalanceStore burnBalance0Store
    burnCacheStore burnReserveStore burnStore
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals repeat' first | rw [store_get_ne _ _ (by decide)]
  all_goals simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

theorem uniswapBurnBodyReturns_afterUpdate (evm evmU evmR : EVM.State) (I : ExecutionEnv) (locals : Store) (amount0 amount1 : UInt256)
    (hprefix : ExecBlock config { contract := contract, locals := burnStore I } evm burnBeforeUpdatePrefix
      (.ok { contract := contract, locals := locals } evmU))
    (hupdate : ExecStmt config { contract := contract, locals := locals } evmU
      (.internalCall "_update" [.var "newBalance0", .var "newBalance1", .var "_reserve0", .var "_reserve1"] "_updateResult")
      (.ok (resumeAfterInternalCall { contract := contract, locals := locals } "_updateResult" none) evmR))
    {evmFinal : EVM.State}
    (htail : ExecBlock config (resumeAfterInternalCall { contract := contract, locals := locals } "_updateResult" none) evmR
      burnAfterUpdateTail (.returned (resumeAfterInternalCall { contract := contract, locals := locals } "_updateResult" none)
        evmFinal (some [uniswapUint256Value amount0, uniswapUint256Value amount1]))) :
    ExecTransitionBody config contract evm (burnStore I) burnTransition.body
      (.returned (resumeAfterInternalCall { contract := contract, locals := locals } "_updateResult" none)
        evmFinal (some [uniswapUint256Value amount0, uniswapUint256Value amount1])) := by
  apply ExecFuncBody.execBlockRet
  simpa only [burnTransition, burnBeforeUpdatePrefix, burnBeforeUpdatedBalancesPrefix, burnBeforeTransfersPrefix,
    burnBeforeAmountsPrefix, burnBeforeFeePrefix, burnCachePrefix, burnAmount0Stmt, burnAmount1Stmt,
    burnAmountsRequireStmt, burnAmountsRequireExpr, burnInternalBurnStmt, burnAfterUpdateTail,
    uniswapKLastIfFeeStmt, updateReservesStmtsWith, List.append_assoc, List.cons_append, List.nil_append] using
    execBlock_append hprefix (ExecBlock.consNormal hupdate htail)

end UniswapV2Pair
