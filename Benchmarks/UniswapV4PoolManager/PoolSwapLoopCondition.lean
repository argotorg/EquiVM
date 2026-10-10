import Benchmarks.UniswapV4PoolManager.PoolSwapLoopInvariant

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapLoopCondition : Expr :=
  .unary .not (.binary .or (.binary .eq (.var "amountSpecifiedRemaining") (.intLit 0))
    (.binary .eq (.field (.var "result") "sqrtPriceX96") (.field (.var "params") "sqrtPriceLimitX96")))

theorem poolSwapFunction_loop : poolSwapFunction.body[28]! = .while poolSwapLoopCondition poolSwapLoopBody := rfl

def poolSwapLoopContinues (p : PoolSwapParamsWords) (q : PoolSwapLoopWords) : Prop :=
  q.remaining ≠ ⟨0⟩ ∧ q.result.price ≠ p.priceLimit

instance (p : PoolSwapParamsWords) (q : PoolSwapLoopWords) : Decidable (poolSwapLoopContinues p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem poolSwapLoopCondition_eval {f : Frame} {evm : State} {id fee protocol : UInt256}
    {p : PoolSwapParamsWords} {q : PoolSwapLoopWords}
    (h : PoolSwapLoopLocals f id q.step q.result p q.remaining q.calculated fee protocol q.amountToProtocol) :
    evalExpr? config f evm poolSwapLoopCondition = .ok (.bool (decide (poolSwapLoopContinues p q))) := by
  have hrem : evalExpr? config f evm (.binary .eq (.var "amountSpecifiedRemaining") (.intLit 0)) =
      .ok (.bool (decide (q.remaining = ⟨0⟩))) := by
    simpa only [signed_eq_zero_iff] using evalIntEq (evalLocalValue (evm := evm) h.remaining)
      (show evalExpr? config f evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
  have hprice := evalEqWords
    (evalStructField (cfg := config) (evm := evm) (field := "sqrtPriceX96") (evalLocalValue h.result) rfl)
    (evalStructField (field := "sqrtPriceLimitX96") (evalLocalValue h.params) rfl)
  have he := evalNotBool (evalOrBool hrem hprice)
  by_cases hr : q.remaining = ⟨0⟩ <;> by_cases hp : q.result.price = p.priceLimit <;>
    simpa only [poolSwapLoopContinues, hr, hp, decide_true, decide_false,
      Bool.true_or, Bool.false_or, Bool.not_true, Bool.not_false, ne_eq, not_true_eq_false,
      not_false_eq_true, false_and, true_and, and_self] using he

end Benchmarks.UniswapV4PoolManager
