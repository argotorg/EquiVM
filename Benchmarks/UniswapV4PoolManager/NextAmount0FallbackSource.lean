import Benchmarks.UniswapV4PoolManager.NextAmount0Words
import Benchmarks.UniswapV4PoolManager.DivRoundSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextAmount0FallbackStmts : List Stmt :=
  [.internalCall "UnsafeMath_divRoundingUp" [.var "numerator1",
     .inRange (.uint ⟨256, by decide⟩) (.binary .add (.binary .div (.var "numerator1") (.var "sqrtPX96"))
       (.var "amount"))] "__c1",
   .return [.cast (.var "__c1") (.elem (.int (.uint ⟨160, by decide⟩)))]]

theorem nextAmount0FallbackSource {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    (hf : f.contract = contract) (hp : price ≠ ⟨0⟩)
    (hn : f.locals.get? "numerator1" = some (.int (Int.ofNat (amount0Numerator1 liquidity).toNat)))
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ∃ f', ExecBlock config f evm nextAmount0FallbackStmts
      (if nextAmount0FallbackFits price liquidity amount then
        .returned f' evm (some [.int (Int.ofNat (nextAmount0FallbackWord price liquidity amount).toNat)])
       else .reverted) := by
  have hd := evalWordDiv (evalLocalValue (cfg := config) (f := f) (evm := evm) hn) (evalLocalValue hs) hp
  by_cases hfit : nextAmount0FallbackFits price liquidity amount
  · simp only [if_pos hfit]
    have he := checkedAddSourceOk hd (evalLocalValue ha) hfit
    have hc := divRoundCall hf (evalLocalValue hn) he "__c1"
    let result := divRoundWord (amount0Numerator1 liquidity) (UInt256.div (amount0Numerator1 liquidity) price+amount)
    have hr := evalExpr_cast_int (intType := .uint ⟨160, by decide⟩)
      (wordLocal_eval (cfg := config) (f := f) (evm := evm) (name := "__c1") (w := result))
    rw [normalizeUintWord ⟨160, by decide⟩ _ solcAddrMask rfl] at hr
    exact ⟨wordLocal f "__c1" result, ExecBlock.consNormal hc (ABlock.start.returns hr)⟩
  · simp only [if_neg hfit]
    have he := checkedAddSourceOverflow hd (evalLocalValue ha) (Nat.le_of_not_gt hfit)
    refine ⟨f, ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)⟩
    simp only [evalExprs?, evalLocalValue hn, he, bind, EvalResult.bind]

end Benchmarks.UniswapV4PoolManager
