import Examples.UniswapV2Pair.SwapOutputSource
import Examples.UniswapV2Pair.MintCommon
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapReserveStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((swapStore I).insert "_reserve0" (uniswapUint256Value (uniswapReserve0Word evm))).insert
    "_reserve1" (uniswapUint256Value (uniswapReserve1Word evm))
abbrev swapReservePrefix : List Stmt := swapOutputPrefix ++
  [.letDecl "_reserve0" (some uint112) (.storage reserve0Ref),
    .letDecl "_reserve1" (some uint112) (.storage reserve1Ref)]
abbrev swapReserveRequireExpr : Expr :=
  .binary .and (.binary .lt (.var "amount0Out") (.var "_reserve0"))
    (.binary .lt (.var "amount1Out") (.var "_reserve1"))
abbrev swapReserveRequireStmt : Stmt := .require swapReserveRequireExpr

theorem uniswapSwapReservePrefix (evm : EVM.State) (I : ExecutionEnv)
    (houtput : ExecBlock config { contract := contract, locals := swapStore I } evm swapOutputPrefix
      (.ok { contract := contract, locals := swapStore I } (uniswapLockEnteredState evm))) :
    ExecBlock config { contract := contract, locals := swapStore I } evm swapReservePrefix
      (.ok { contract := contract, locals := swapReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) := by
  have hr0 := evalExpr_uniswap_reserve0 (uniswapLockEnteredState evm) (swapStore I)
    (by simp [swapStore])
  have hr1 := evalExpr_uniswap_reserve1 (uniswapLockEnteredState evm)
    ((swapStore I).insert "_reserve0" (uniswapUint256Value (uniswapReserve0Word (uniswapLockEnteredState evm))))
    (by simp [swapStore])
  exact execBlock_append houtput (ExecBlock.consNormal (ExecStmt.letDecl hr0)
    (ExecBlock.consNormal (ExecStmt.letDecl hr1) ExecBlock.nil))

theorem evalExpr_swap_reserveRequire (evm : EVM.State) {locals : Store}
    {amount0 amount1 reserve0 reserve1 : UInt256}
    (ha0 : locals.get? "amount0Out" = some (uniswapUint256Value amount0))
    (ha1 : locals.get? "amount1Out" = some (uniswapUint256Value amount1))
    (hr0 : locals.get? "_reserve0" = some (uniswapUint256Value reserve0))
    (hr1 : locals.get? "_reserve1" = some (uniswapUint256Value reserve1)) :
    evalExpr? config { contract := contract, locals := locals } evm swapReserveRequireExpr =
      .ok (.bool (decide (amount0.toNat < reserve0.toNat ∧ amount1.toNat < reserve1.toNat))) := by
  simp only [swapReserveRequireExpr, evalExpr?, EvalResult.ofOption, ha0, ha1, hr0, hr1,
    EvalResult.bind, bind, pure]
  by_cases hp0 : amount0.toNat < reserve0.toNat <;> simp [evalBinaryOp?, hp0]

theorem swapReserveStore_gets (evm : EVM.State) (I : ExecutionEnv) :
    (swapReserveStore evm I).get? "amount0Out" = some (uniswapUint256Value (swapAmount0OutWord I)) ∧
    (swapReserveStore evm I).get? "amount1Out" = some (uniswapUint256Value (swapAmount1OutWord I)) ∧
    (swapReserveStore evm I).get? "_reserve0" = some (uniswapUint256Value (uniswapReserve0Word evm)) ∧
    (swapReserveStore evm I).get? "_reserve1" = some (uniswapUint256Value (uniswapReserve1Word evm)) := by
  simp only [swapReserveStore]
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), swapStore_amount0Out]
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), swapStore_amount1Out]
  constructor
  · rw [store_get_ne _ _ (by decide), store_get_self]
  · exact store_get_self _ _ _

theorem uniswapSwapBodyReverts_reserveGuard (evm : EVM.State) (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapReservePrefix
      (.ok { contract := contract, locals := swapReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)))
    (hnot : ¬ ((swapAmount0OutWord I).toNat < (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ∧
      (swapAmount1OutWord I).toNat < (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat)) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  obtain ⟨ha0, ha1, hr0, hr1⟩ := swapReserveStore_gets (uniswapLockEnteredState evm) I
  have hreq := evalExpr_swap_reserveRequire (uniswapLockEnteredState evm) ha0 ha1 hr0 hr1
  have htail : ExecBlock config
      { contract := contract, locals := swapReserveStore (uniswapLockEnteredState evm) I }
      (uniswapLockEnteredState evm) [swapReserveRequireStmt] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [hnot, decide_false] using hreq))
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapReservePrefix, swapOutputPrefix, swapOutputRequireStmt,
      swapOutputRequireExpr, swapReserveRequireStmt, swapReserveRequireExpr, List.append_assoc,
      List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix htail) (by intro f e h; cases h))

abbrev swapReserveGuardPrefix : List Stmt := swapReservePrefix ++ [swapReserveRequireStmt]

theorem uniswapSwapReserveGuardPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapReservePrefix
      (.ok { contract := contract, locals := swapReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)))
    (hfit : (swapAmount0OutWord I).toNat < (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ∧
      (swapAmount1OutWord I).toNat < (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat) :
    ExecBlock config { contract := contract, locals := swapStore I } evm swapReserveGuardPrefix
      (.ok { contract := contract, locals := swapReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)) := by
  obtain ⟨ha0, ha1, hr0, hr1⟩ := swapReserveStore_gets (uniswapLockEnteredState evm) I
  have hreq := evalExpr_swap_reserveRequire (uniswapLockEnteredState evm) ha0 ha1 hr0 hr1
  exact execBlock_append hprefix (ExecBlock.consNormal
    (ExecStmt.requireTrue (by simpa only [hfit, decide_true] using hreq)) ExecBlock.nil)

end UniswapV2Pair
