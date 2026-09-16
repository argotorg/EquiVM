import Examples.UniswapV2Pair.OptionalSafeTransferCases
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

-- LIBRARY CANDIDATE: evaluating a positive unsigned-word local.
theorem evalExpr_uint256_var_positive {cfg : Config} {frame : Frame} (evm : EVM.State)
    (name : Ident) (word : UInt256)
    (hget : frame.locals.get? name = some (.int (Int.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.binary .gt (.var name) (.intLit 0)) =
      .ok (.bool (decide (0 < word.toNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, hget, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]

theorem evalExprs_safeTransfer_args_of_get {caller : Frame} (evm : EVM.State)
    (tokenName toName valueName : Ident) (token recipient : AccountAddress) (value : UInt256)
    (ht : caller.locals.get? tokenName = some (.address token))
    (hto : caller.locals.get? toName = some (.address recipient))
    (hv : caller.locals.get? valueName = some (uniswapUint256Value value)) :
    evalExprs? config caller evm [.var tokenName, .var toName, .var valueName] =
      .ok (safeTransferArgs token recipient value) := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, ht, hto, hv, EvalResult.bind, bind, pure]

theorem optionalSafeTransferFrame_get_ne (caller : Frame) (retVar key : Ident) (value : UInt256)
    (hne : key ≠ retVar) :
    (optionalSafeTransferFrame caller retVar value).locals.get? key = caller.locals.get? key := by
  unfold optionalSafeTransferFrame
  split
  · rfl
  · exact store_get_ne _ _ (beq_eq_false_iff_ne.mpr (Ne.symm hne))

end UniswapV2Pair
