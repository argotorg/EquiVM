import Benchmarks.UniswapV4PoolManager.NextPriceWords
import Benchmarks.UniswapV4PoolManager.NextAmount0Source
import Benchmarks.UniswapV4PoolManager.NextAmount1Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextPriceCalcName (use0 : Bool) : Ident :=
  if use0 then "SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp"
  else "SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown"

theorem nextPriceCalcCall {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    {es el ea : Expr} (use0 add : Bool) (hf : f.contract = contract)
    (hp : price.toNat < 2^160) (hn : nextPriceValid price liquidity)
    (hs : evalExpr? config f evm es = .ok (.int (Int.ofNat price.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall (nextPriceCalcName use0) [es, el, ea, .boolLit add] ret)
      (if nextPriceCalcFits price liquidity amount use0 add then
        .ok (wordLocal f ret (nextPriceCalcWord price liquidity amount use0 add)) evm else .reverted) := by
  cases use0 with
  | false => exact nextAmount1Call hf hp hn.2 hs hl ha (by simp only [evalExpr?, pure]) ret
  | true => exact nextAmount0Call hf hn.1 hs hl ha (by simp only [evalExpr?, pure]) ret

def nextPriceReturnStmts (amountName : Ident) (use0 add : Bool) : List Stmt :=
  [.internalCall (nextPriceCalcName use0)
    [.var "sqrtPX96", .var "liquidity", .var amountName, .boolLit add] "result",
   .return [.var "result"]]

theorem nextPriceReturnSource {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    (amountName : Ident) (use0 add : Bool) (hf : f.contract = contract)
    (hp : price.toNat < 2^160) (hn : nextPriceValid price liquidity)
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (ha : f.locals.get? amountName = some (.int (Int.ofNat amount.toNat))) :
    ExecBlock config f evm (nextPriceReturnStmts amountName use0 add)
      (if nextPriceCalcFits price liquidity amount use0 add then
        .returned (wordLocal f "result" (nextPriceCalcWord price liquidity amount use0 add)) evm
          (some [.int (Int.ofNat (nextPriceCalcWord price liquidity amount use0 add).toNat)])
       else .reverted) := by
  have hc := nextPriceCalcCall (f := f) (evm := evm) use0 add hf hp hn (evalLocalValue hs) (evalLocalValue hl)
    (evalLocalValue ha) "result"
  by_cases hfit : nextPriceCalcFits price liquidity amount use0 add
  · rw [if_pos hfit] at hc ⊢
    exact ExecBlock.consNormal hc (ABlock.start.returns (evalLocalValue (store_get_self _ _ _)))
  · rw [if_neg hfit] at hc ⊢
    exact ExecBlock.consRevert hc

end Benchmarks.UniswapV4PoolManager
