import Examples.UniswapV2Pair.SwapInvariantRuntime
import Examples.UniswapV2Pair.SwapAdjustmentPrefix
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

abbrev swapInvariantExpr : Expr :=
  .binary .ge (u256 (.binary .mul (.var "balance0Adjusted") (.var "balance1Adjusted")))
    (u256 (.binary .mul (u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))) (.intLit 1000000)))
abbrev swapInvariantStmt : Stmt := .require swapInvariantExpr
abbrev swapInvariantPrefix : List Stmt := swapAdjustmentPrefix ++ [swapInvariantStmt]

theorem evalExpr_swap_invariant {caller : Frame} (evm : EVM.State)
    (adjusted0 adjusted1 reserve0 reserve1 : UInt256)
    (ha0 : caller.locals.get? "balance0Adjusted" = some (uniswapUint256Value adjusted0))
    (ha1 : caller.locals.get? "balance1Adjusted" = some (uniswapUint256Value adjusted1))
    (hr0 : caller.locals.get? "_reserve0" = some (uniswapUint256Value reserve0))
    (hr1 : caller.locals.get? "_reserve1" = some (uniswapUint256Value reserve1))
    (hc0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hc1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hfit : adjusted0.toNat * adjusted1.toNat < UInt256.size) :
    evalExpr? config caller evm swapInvariantExpr = .ok (.bool (decide
      ((swapInvariantReserveWord reserve0 reserve1).toNat ≤ (UInt256.mul adjusted0 adjusted1).toNat))) := by
  have hleft : evalExpr? config caller evm
      (u256 (.binary .mul (.var "balance0Adjusted") (.var "balance1Adjusted"))) =
      .ok (uniswapUint256Value (UInt256.mul adjusted0 adjusted1)) :=
    evalExpr_uint256_mul (by simp only [evalExpr?, EvalResult.ofOption, ha0])
      (by simp only [evalExpr?, EvalResult.ofOption, ha1]) hfit
  obtain ⟨hfitR, hfitS⟩ := swapInvariantReserveFits reserve0 reserve1 hc0 hc1
  have hright : evalExpr? config caller evm
      (u256 (.binary .mul (u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))) (.intLit 1000000))) =
      .ok (uniswapUint256Value (swapInvariantReserveWord reserve0 reserve1)) :=
    evalExpr_uint256_mul (evalExpr_uint256_mul
      (by simp only [evalExpr?, EvalResult.ofOption, hr0])
      (by simp only [evalExpr?, EvalResult.ofOption, hr1]) hfitR)
      (by norm_num [evalExpr?, pure, uint256Value, UInt256.toNat, UInt256.size]) hfitS
  simp only [swapInvariantExpr, evalExpr?, hleft, hright, EvalResult.bind, bind,
    uniswapUint256Value, uint256Value, evalBinaryOp?, Int.ofNat_eq_natCast]
  simp

theorem evalExpr_swap_invariant_overflow {caller : Frame} (evm : EVM.State)
    (adjusted0 adjusted1 : UInt256)
    (ha0 : caller.locals.get? "balance0Adjusted" = some (uniswapUint256Value adjusted0))
    (ha1 : caller.locals.get? "balance1Adjusted" = some (uniswapUint256Value adjusted1))
    (hover : UInt256.size ≤ adjusted0.toNat * adjusted1.toNat) :
    evalExpr? config caller evm swapInvariantExpr = .revert := by
  have hleft : evalExpr? config caller evm
      (u256 (.binary .mul (.var "balance0Adjusted") (.var "balance1Adjusted"))) = .revert :=
    evalExpr_uint256_mul_overflow
      (by simp only [evalExpr?, EvalResult.ofOption, ha0])
      (by simp only [evalExpr?, EvalResult.ofOption, ha1]) hover
  simp only [swapInvariantExpr, evalExpr?, hleft, EvalResult.bind, bind]

theorem uniswapSwapInvariantSourceRevert {caller : Frame} (evm : EVM.State)
    (adjusted0 adjusted1 reserve0 reserve1 : UInt256)
    (ha0 : caller.locals.get? "balance0Adjusted" = some (uniswapUint256Value adjusted0))
    (ha1 : caller.locals.get? "balance1Adjusted" = some (uniswapUint256Value adjusted1))
    (hr0 : caller.locals.get? "_reserve0" = some (uniswapUint256Value reserve0))
    (hr1 : caller.locals.get? "_reserve1" = some (uniswapUint256Value reserve1))
    (hc0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hc1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hnot : ¬ swapInvariantValid adjusted0 adjusted1 reserve0 reserve1) :
    ExecStmt config caller evm swapInvariantStmt .reverted := by
  by_cases hfit : adjusted0.toNat * adjusted1.toNat < UInt256.size
  · have hle : ¬ (swapInvariantReserveWord reserve0 reserve1).toNat ≤ (UInt256.mul adjusted0 adjusted1).toNat :=
      fun h ↦ hnot ⟨hfit, h⟩
    exact ExecStmt.requireFalse (by simpa only [hle, decide_false] using
      (evalExpr_swap_invariant evm adjusted0 adjusted1 reserve0 reserve1 ha0 ha1 hr0 hr1 hc0 hc1 hfit))
  · exact ExecStmt.requireRevert
      (evalExpr_swap_invariant_overflow evm adjusted0 adjusted1 ha0 ha1 (Nat.le_of_not_lt hfit))

theorem uniswapSwapInvariantSourceSuccess {caller : Frame} (evm : EVM.State)
    (adjusted0 adjusted1 reserve0 reserve1 : UInt256)
    (ha0 : caller.locals.get? "balance0Adjusted" = some (uniswapUint256Value adjusted0))
    (ha1 : caller.locals.get? "balance1Adjusted" = some (uniswapUint256Value adjusted1))
    (hr0 : caller.locals.get? "_reserve0" = some (uniswapUint256Value reserve0))
    (hr1 : caller.locals.get? "_reserve1" = some (uniswapUint256Value reserve1))
    (hc0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hc1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hvalid : swapInvariantValid adjusted0 adjusted1 reserve0 reserve1) :
    ExecStmt config caller evm swapInvariantStmt (.ok caller evm) := by
  exact ExecStmt.requireTrue (by simpa only [decide_eq_true hvalid.2] using
    (evalExpr_swap_invariant evm adjusted0 adjusted1 reserve0 reserve1 ha0 ha1 hr0 hr1 hc0 hc1 hvalid.1))

theorem swapAfterAdjustmentsFrame_get_ne (caller : Frame) (adjusted0 adjusted1 : UInt256) (key : Ident)
    (h0 : ("balance0Adjusted" == key) = false) (h1 : ("balance1Adjusted" == key) = false) :
    (swapAfterAdjustmentsFrame caller adjusted0 adjusted1).locals.get? key = caller.locals.get? key := by
  unfold swapAfterAdjustmentsFrame
  rw [store_get_ne _ _ h1, store_get_ne _ _ h0]

theorem swapAfterAdjustmentsFrame_invariantGets (caller : Frame) (adjusted0 adjusted1 reserve0 reserve1 : UInt256)
    (hr0 : caller.locals.get? "_reserve0" = some (uniswapUint256Value reserve0))
    (hr1 : caller.locals.get? "_reserve1" = some (uniswapUint256Value reserve1)) :
    (swapAfterAdjustmentsFrame caller adjusted0 adjusted1).locals.get? "balance0Adjusted" = some (uniswapUint256Value adjusted0) ∧
    (swapAfterAdjustmentsFrame caller adjusted0 adjusted1).locals.get? "balance1Adjusted" = some (uniswapUint256Value adjusted1) ∧
    (swapAfterAdjustmentsFrame caller adjusted0 adjusted1).locals.get? "_reserve0" = some (uniswapUint256Value reserve0) ∧
    (swapAfterAdjustmentsFrame caller adjusted0 adjusted1).locals.get? "_reserve1" = some (uniswapUint256Value reserve1) := by
  exact ⟨(store_get_ne _ _ (by decide)).trans (store_get_self _ _ _), store_get_self _ _ _,
    (swapAfterAdjustmentsFrame_get_ne _ _ _ _ (by decide) (by decide)).trans hr0,
    (swapAfterAdjustmentsFrame_get_ne _ _ _ _ (by decide) (by decide)).trans hr1⟩

theorem uniswapSwapBodyReverts_invariant (evm evmB : EVM.State) (I : ExecutionEnv) (caller : Frame)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapAdjustmentPrefix
      (.ok caller evmB))
    (hrequire : ExecStmt config caller evmB swapInvariantStmt .reverted) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  have htail : ExecBlock config caller evmB [swapInvariantStmt] .reverted := ExecBlock.consRevert hrequire
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapAdjustmentPrefix, swapInputGuardPrefix, swapInputsPrefix,
      swapBalancesPrefix, swapCallbackPrefix, swapTransferPrefix, swapRecipientGuardPrefix,
      swapTokenPrefix, swapReserveGuardPrefix, swapReservePrefix, swapOutputPrefix,
      swapOutputRequireStmt, swapOutputRequireExpr, swapReserveRequireStmt, swapReserveRequireExpr,
      swapRecipientRequireStmt, swapRecipientRequireExpr, swapFirstTransferStmt, swapSecondTransferStmt,
      swapCallbackStmt, swapCallbackCondition, swapCallbackBody, swapBalanceStmts, swapInputStmts,
      swapInputExpr, swapInputRequireStmt, swapInputRequireExpr, swapAdjustmentStmts, swapAdjustedExpr,
      swapInvariantStmt, swapInvariantExpr, List.append_assoc, List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix htail) (by intro f e h; cases h))

end UniswapV2Pair
