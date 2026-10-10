import Benchmarks.UniswapV4PoolManager.Amount0Numerators
import Benchmarks.UniswapV4PoolManager.FullMathRoundSource
import Benchmarks.UniswapV4PoolManager.DivRoundSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem amount0Branches {f : Frame} {evm : EVM.State} {lo hi liquidity : UInt256} {roundUp : Bool}
    (hf : f.contract = contract) (hlo : lo ≠ ⟨0⟩)
    (ha : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat lo.toNat)))
    (hb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat hi.toNat)))
    (h1 : f.locals.get? "numerator1" = some (.int (Int.ofNat (amount0Numerator1 liquidity).toNat)))
    (h2 : f.locals.get? "numerator2" = some (.int (Int.ofNat (amount0Numerator2 lo hi).toNat)))
    (hr : f.locals.get? "roundUp" = some (.bool roundUp)) :
    ∃ f', ExecStmt config f evm amount0Function.body[4]!
      (if amount0CoreFits lo hi liquidity roundUp then
        .returned f' evm (some [.int (Int.ofNat (amount0CoreWord lo hi liquidity roundUp).toNat)])
       else .reverted) := by
  cases roundUp with
  | false =>
    have hcall := fullMathCall (f := f) (evm := evm) hf
      (evalLocalValue h1) (evalLocalValue h2) (evalLocalValue hb) "amount"
    by_cases hfit : fullMathFits (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi
    · rw [if_pos hfit] at hcall
      have hc : amount0CoreFits lo hi liquidity false := ⟨hlo, hfit⟩
      simp only [if_pos hc, amount0CoreWord, Bool.false_eq_true, if_false]
      let f1 := wordLocal f "amount"
        (fullMathWord (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi)
      have ha1 : f1.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat lo.toNat)) := by
        simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
      exact ⟨f1, ExecStmt.iteFalse (evalLocalValue hr) (ExecBlock.consNormal hcall
        (ABlock.start.returns (evalWordDiv wordLocal_eval (evalLocalValue ha1) hlo)))⟩
    · rw [if_neg hfit] at hcall
      have hc : ¬amount0CoreFits lo hi liquidity false := fun hh => hfit hh.2
      simp only [if_neg hc]
      exact ⟨f, ExecStmt.iteFalse (evalLocalValue hr) (ExecBlock.consRevert hcall)⟩
  | true =>
    have hcall := fullMathRoundCall (f := f) (evm := evm) hf
      (evalLocalValue h1) (evalLocalValue h2) (evalLocalValue hb) "amount"
    by_cases hfit : fullMathRoundFits (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi
    · rw [if_pos hfit] at hcall
      have hc : amount0CoreFits lo hi liquidity true := ⟨hlo, hfit⟩
      simp only [if_pos hc, amount0CoreWord, Bool.true_eq, if_true]
      let f1 := wordLocal f "amount"
        (fullMathRoundWord (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi)
      have ha1 : f1.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat lo.toNat)) := by
        simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
      have hdiv := divRoundCall (f := f1) (evm := evm) hf wordLocal_eval (evalLocalValue ha1) "result"
      exact ⟨_, ExecStmt.iteTrue (evalLocalValue hr) (ExecBlock.consNormal hcall
        (ExecBlock.consNormal hdiv (ABlock.start.returns wordLocal_eval)))⟩
    · rw [if_neg hfit] at hcall
      have hc : ¬amount0CoreFits lo hi liquidity true := fun hh => hfit hh.2
      simp only [if_neg hc]
      exact ⟨f, ExecStmt.iteTrue (evalLocalValue hr) (ExecBlock.consRevert hcall)⟩

end Benchmarks.UniswapV4PoolManager
