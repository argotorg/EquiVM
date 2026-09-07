import Reasoning.SolmBody
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace UniswapV2Pair
-- LIBRARY CANDIDATE: evaluate a disjunction of positivity tests on two word-valued locals.
theorem evalExpr_uint256_vars_positiveOr {cfg : Config} {caller : Frame} (evm : EVM.State)
    (var0 var1 : Ident) (word0 word1 : UInt256)
    (h0 : caller.locals.get? var0 = some (uint256Value word0))
    (h1 : caller.locals.get? var1 = some (uint256Value word1)) :
    evalExpr? cfg caller evm
      (.binary .or (.binary .gt (.var var0) (.intLit 0)) (.binary .gt (.var var1) (.intLit 0))) =
      .ok (.bool (decide (0 < word0.toNat ∨ 0 < word1.toNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, h0, h1, EvalResult.bind, bind, pure]
  by_cases hp0 : 0 < word0.toNat <;> simp [evalBinaryOp?, hp0]

end UniswapV2Pair
