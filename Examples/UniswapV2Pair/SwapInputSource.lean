import Examples.UniswapV2Pair.SwapInputRuntime
import Examples.UniswapV2Pair.SwapBalanceSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapInputExpr (balanceVar reserveVar outVar : Ident) : Expr :=
  .ite (.binary .gt (.var balanceVar) (.binary .sub (.var reserveVar) (.var outVar)))
    (u256 (.binary .sub (.var balanceVar) (.binary .sub (.var reserveVar) (.var outVar))))
    (.intLit 0)

theorem evalExpr_swap_input {caller : Frame} (evm : EVM.State)
    (balanceVar reserveVar outVar : Ident) (balance reserve amountOut : UInt256)
    (hb : caller.locals.get? balanceVar = some (uniswapUint256Value balance))
    (hr : caller.locals.get? reserveVar = some (uniswapUint256Value reserve))
    (ho : caller.locals.get? outVar = some (uniswapUint256Value amountOut))
    (hle : amountOut.toNat ≤ reserve.toNat) :
    evalExpr? config caller evm (swapInputExpr balanceVar reserveVar outVar) =
      .ok (uniswapUint256Value (swapAmountInWord balance reserve amountOut)) := by
  have hsub := usub_toNat hle
  have hint : Int.ofNat reserve.toNat - Int.ofNat amountOut.toNat = Int.ofNat (UInt256.sub reserve amountOut).toNat := by
    rw [hsub]
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [swapInputExpr, evalExpr?, EvalResult.ofOption, hb, hr, ho,
    EvalResult.bind, bind, pure, uniswapUint256Value, uint256Value, evalBinaryOp?, hint]
  by_cases hp : (UInt256.sub reserve amountOut).toNat < balance.toNat
  · have hpI : Int.ofNat (UInt256.sub reserve amountOut).toNat < Int.ofNat balance.toNat := by simp only [Int.ofNat_eq_natCast]; omega
    simp only [hpI, decide_true, swapAmountInWord, if_pos hp]
    have hdiff := usub_toNat (Nat.le_of_lt hp)
    have hintDiff : Int.ofNat balance.toNat - Int.ofNat (UInt256.sub reserve amountOut).toNat =
        Int.ofNat (UInt256.sub balance (UInt256.sub reserve amountOut)).toNat := by
      rw [hdiff]
      simp only [Int.ofNat_eq_natCast]
      omega
    simp only [u256, evalExpr?, EvalResult.ofOption, hb, hr, ho, EvalResult.bind, bind, pure,
      uniswapUint256Value, uint256Value, evalBinaryOp?, hint, hintDiff, uint256Int]
    have hbound := (UInt256.sub balance (UInt256.sub reserve amountOut)).val.isLt
    change (UInt256.sub balance (UInt256.sub reserve amountOut)).toNat < 2 ^ 256 at hbound
    have hn : ¬ Int.ofNat (UInt256.sub balance (UInt256.sub reserve amountOut)).toNat < 0 := by simp only [Int.ofNat_eq_natCast]; omega
    have hh : ¬ Int.ofNat (UInt256.sub balance (UInt256.sub reserve amountOut)).toNat ≥ 2 ^ 256 := by simp only [Int.ofNat_eq_natCast]; omega
    simp only [hn, hh, decide_false, Bool.false_or, Bool.false_eq_true, if_false]
  · have hpI : ¬ Int.ofNat (UInt256.sub reserve amountOut).toNat < Int.ofNat balance.toNat := by simp only [Int.ofNat_eq_natCast]; omega
    simp only [hpI, decide_false, swapAmountInWord, if_neg hp]
    rfl

abbrev swapInputStmts : List Stmt :=
  [.letDecl "amount0In" (some uint256) (swapInputExpr "balance0" "_reserve0" "amount0Out"),
    .letDecl "amount1In" (some uint256) (swapInputExpr "balance1" "_reserve1" "amount1Out")]

abbrev swapAfterInputsFrame (caller : Frame) (amount0In amount1In : UInt256) : Frame :=
  { caller with locals := ((caller.locals.insert "amount0In" (uniswapUint256Value amount0In)).insert
      "amount1In" (uniswapUint256Value amount1In)) }

theorem uniswapSwapInputsSource {caller : Frame} (evm : EVM.State)
    (balance0 balance1 reserve0 reserve1 amount0Out amount1Out : UInt256)
    (hb0 : caller.locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : caller.locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hr0 : caller.locals.get? "_reserve0" = some (uniswapUint256Value reserve0))
    (hr1 : caller.locals.get? "_reserve1" = some (uniswapUint256Value reserve1))
    (ho0 : caller.locals.get? "amount0Out" = some (uniswapUint256Value amount0Out))
    (ho1 : caller.locals.get? "amount1Out" = some (uniswapUint256Value amount1Out))
    (hle0 : amount0Out.toNat ≤ reserve0.toNat) (hle1 : amount1Out.toNat ≤ reserve1.toNat) :
    ExecBlock config caller evm swapInputStmts
      (.ok (swapAfterInputsFrame caller (swapAmountInWord balance0 reserve0 amount0Out)
        (swapAmountInWord balance1 reserve1 amount1Out)) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_swap_input evm "balance0" "_reserve0" "amount0Out" balance0 reserve0 amount0Out
      hb0 hr0 ho0 hle0)) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_swap_input evm "balance1" "_reserve1" "amount1Out" balance1 reserve1 amount1Out
      (by rw [store_get_ne _ _ (by decide), hb1])
      (by rw [store_get_ne _ _ (by decide), hr1])
      (by rw [store_get_ne _ _ (by decide), ho1]) hle1)) ExecBlock.nil

theorem swapAfterBalancesFrame_get_ne (caller : Frame) (balance0 balance1 : UInt256) (key : Ident)
    (h0 : ("balance0" == key) = false) (h1 : ("balance1" == key) = false) :
    (swapAfterBalancesFrame caller balance0 balance1).locals.get? key = caller.locals.get? key := by
  unfold swapAfterBalancesFrame
  rw [store_get_ne _ _ h1, store_get_ne _ _ h0]

abbrev swapBeforeInputsFrame (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) : Frame :=
  swapAfterBalancesFrame (swapAfterCallbackFrame
    (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evm I }
      (swapAmount0OutWord I) (swapAmount1OutWord I)) (swapDataSizeWord I)) balance0 balance1

theorem swapBeforeInputsFrame_gets (evm : EVM.State) (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (swapBeforeInputsFrame evm I balance0 balance1).locals.get? "balance0" = some (uniswapUint256Value balance0) ∧
    (swapBeforeInputsFrame evm I balance0 balance1).locals.get? "balance1" = some (uniswapUint256Value balance1) ∧
    (swapBeforeInputsFrame evm I balance0 balance1).locals.get? "_reserve0" = some (uniswapUint256Value (uniswapReserve0Word evm)) ∧
    (swapBeforeInputsFrame evm I balance0 balance1).locals.get? "_reserve1" = some (uniswapUint256Value (uniswapReserve1Word evm)) ∧
    (swapBeforeInputsFrame evm I balance0 balance1).locals.get? "amount0Out" = some (uniswapUint256Value (swapAmount0OutWord I)) ∧
    (swapBeforeInputsFrame evm I balance0 balance1).locals.get? "amount1Out" = some (uniswapUint256Value (swapAmount1OutWord I)) := by
  obtain ⟨ho0, ho1, hr0, hr1⟩ := swapReserveStore_gets evm I
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
  · exact store_get_self _ _ _
  all_goals
    unfold swapBeforeInputsFrame
    rw [swapAfterBalancesFrame_get_ne _ _ _ _ (by decide) (by decide),
      swapAfterCallbackFrame_get_ne _ _ _ (by decide),
      swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]
    change (swapTokenStore evm I).get? _ = _
    rw [swapTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  · exact hr0
  · exact hr1
  · exact ho0
  · exact ho1

end UniswapV2Pair
