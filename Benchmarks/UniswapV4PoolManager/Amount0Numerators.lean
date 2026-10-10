import Benchmarks.UniswapV4PoolManager.Amount0Sort
import Benchmarks.UniswapV4PoolManager.WordBoundedSubSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def amount0NumeratorsFrame (f : Frame) (lo hi liquidity : UInt256) : Frame :=
  wordLocal (wordLocal f "numerator1" (amount0Numerator1 liquidity)) "numerator2" (amount0Numerator2 lo hi)

theorem amount0Numerators {f : Frame} {evm : EVM.State} {lo hi liquidity : UInt256}
    (ho : lo.toNat ≤ hi.toNat) (hh : hi.toNat < 2^160)
    (ha : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat lo.toNat)))
    (hb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat hi.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat))) :
    ExecBlock config f evm ((amount0Function.body.drop 2).take 2)
      (.ok (amount0NumeratorsFrame f lo hi liquidity) evm) := by
  let f1 := wordLocal f "numerator1" (amount0Numerator1 liquidity)
  have hcast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
    (evalLocalValue (cfg := config) (f := f) (evm := evm) hl)
  rw [normalizeInt_uint256_word] at hcast
  have h1 : ExecStmt config f evm amount0Function.body[2]! (.ok f1 evm) :=
    ExecStmt.letDecl (evalWordShl (by decide : 96 < 256) hcast
      (by simp only [evalExpr?, pure]; rfl))
  have ha1 : f1.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat lo.toNat)) := by
    simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
  have hb1 : f1.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat hi.toNat)) := by
    simp only [f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb]
  have h2 : ExecStmt config f1 evm amount0Function.body[3]!
      (.ok (amount0NumeratorsFrame f lo hi liquidity) evm) :=
    ExecStmt.letDecl (evalBoundedWordSub ⟨160, by decide⟩ ho hh
      (evalLocalValue hb1) (evalLocalValue ha1))
  exact ExecBlock.consNormal h1 (execBlock_singleton h2)

end Benchmarks.UniswapV4PoolManager
