import Examples.UniswapV2Pair.SwapAdjustmentRuntime
import Examples.UniswapV2Pair.WordArithmeticSource
import Examples.UniswapV2Pair.Spec
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapAdjustedExpr (balanceVar inputVar : Ident) : Expr :=
  u256 (.binary .sub (u256 (.binary .mul (.var balanceVar) (.intLit 1000)))
    (u256 (.binary .mul (.var inputVar) (.intLit 3))))

theorem evalExpr_swap_adjusted {caller : Frame} (evm : EVM.State)
    (balanceVar inputVar : Ident) (balance amountIn : UInt256)
    (hb : caller.locals.get? balanceVar = some (uniswapUint256Value balance))
    (hi : caller.locals.get? inputVar = some (uniswapUint256Value amountIn))
    (hle : amountIn.toNat ≤ balance.toNat) (hfit : balance.toNat * 1000 < UInt256.size) :
    evalExpr? config caller evm (swapAdjustedExpr balanceVar inputVar) =
      .ok (uniswapUint256Value (swapAdjustedWord balance amountIn)) := by
  obtain ⟨hfitI, hsub⟩ := swapAdjustmentBounds balance amountIn hle hfit
  exact evalExpr_uint256_sub
    (evalExpr_uint256_mul (by simp only [evalExpr?, EvalResult.ofOption, hb]) (by norm_num [evalExpr?, pure, uint256Value, UInt256.toNat, UInt256.size]) hfit)
    (evalExpr_uint256_mul (by simp only [evalExpr?, EvalResult.ofOption, hi]) (by norm_num [evalExpr?, pure, uint256Value, UInt256.toNat, UInt256.size]) hfitI) hsub

theorem evalExpr_swap_adjusted_overflow {caller : Frame} (evm : EVM.State)
    (balanceVar inputVar : Ident) (balance : UInt256)
    (hb : caller.locals.get? balanceVar = some (uniswapUint256Value balance))
    (hover : UInt256.size ≤ balance.toNat * 1000) :
    evalExpr? config caller evm (swapAdjustedExpr balanceVar inputVar) = .revert := by
  have hm : evalExpr? config caller evm (u256 (.binary .mul (.var balanceVar) (.intLit 1000))) = .revert :=
    evalExpr_uint256_mul_overflow (a := balance) (b := ⟨1000⟩) (by simp only [evalExpr?, EvalResult.ofOption, hb]) (by norm_num [evalExpr?, pure, uint256Value, UInt256.toNat, UInt256.size]) hover
  dsimp only [u256] at hm
  simp only [swapAdjustedExpr, u256, evalExpr?, hm, EvalResult.bind, bind]

abbrev swapAdjustmentStmts : List Stmt :=
  [.letDecl "balance0Adjusted" (some uint256) (swapAdjustedExpr "balance0" "amount0In"),
    .letDecl "balance1Adjusted" (some uint256) (swapAdjustedExpr "balance1" "amount1In")]

abbrev swapAfterAdjustmentsFrame (caller : Frame) (balance0Adjusted balance1Adjusted : UInt256) : Frame :=
  { caller with locals := ((caller.locals.insert "balance0Adjusted" (uniswapUint256Value balance0Adjusted)).insert
      "balance1Adjusted" (uniswapUint256Value balance1Adjusted)) }

theorem uniswapSwapAdjustmentsSource {caller : Frame} (evm : EVM.State)
    (balance0 balance1 amount0In amount1In : UInt256)
    (hb0 : caller.locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : caller.locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hi0 : caller.locals.get? "amount0In" = some (uniswapUint256Value amount0In))
    (hi1 : caller.locals.get? "amount1In" = some (uniswapUint256Value amount1In))
    (hle0 : amount0In.toNat ≤ balance0.toNat) (hle1 : amount1In.toNat ≤ balance1.toNat)
    (hfit0 : balance0.toNat * 1000 < UInt256.size) (hfit1 : balance1.toNat * 1000 < UInt256.size) :
    ExecBlock config caller evm swapAdjustmentStmts
      (.ok (swapAfterAdjustmentsFrame caller (swapAdjustedWord balance0 amount0In)
        (swapAdjustedWord balance1 amount1In)) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_swap_adjusted evm "balance0" "amount0In" balance0 amount0In hb0 hi0 hle0 hfit0)) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_swap_adjusted evm "balance1" "amount1In" balance1 amount1In
      (by rw [store_get_ne _ _ (by decide), hb1])
      (by rw [store_get_ne _ _ (by decide), hi1]) hle1 hfit1)) ExecBlock.nil

theorem uniswapSwapAdjustmentsRevert0 {caller : Frame} (evm : EVM.State) (balance0 : UInt256)
    (hb0 : caller.locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hover : UInt256.size ≤ balance0.toNat * 1000) :
    ExecBlock config caller evm swapAdjustmentStmts .reverted :=
  ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_swap_adjusted_overflow evm "balance0" "amount0In" balance0 hb0 hover))

theorem uniswapSwapAdjustmentsRevert1 {caller : Frame} (evm : EVM.State)
    (balance0 balance1 amount0In : UInt256)
    (hb0 : caller.locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : caller.locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hi0 : caller.locals.get? "amount0In" = some (uniswapUint256Value amount0In))
    (hle0 : amount0In.toNat ≤ balance0.toNat)
    (hfit0 : balance0.toNat * 1000 < UInt256.size) (hover1 : UInt256.size ≤ balance1.toNat * 1000) :
    ExecBlock config caller evm swapAdjustmentStmts .reverted := by
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_swap_adjusted evm "balance0" "amount0In" balance0 amount0In hb0 hi0 hle0 hfit0)) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_swap_adjusted_overflow evm "balance1" "amount1In" balance1
      (by rw [store_get_ne _ _ (by decide), hb1]) hover1))

end UniswapV2Pair
