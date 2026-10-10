import Benchmarks.UniswapV4PoolManager.CheckedAmountPath
import Benchmarks.UniswapV4PoolManager.Amount0Source
import Benchmarks.UniswapV4PoolManager.SignedAmount0Words

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem signedAmount0Path {f : Frame} {evm : EVM.State} {a b liquidity : UInt256} {el : Expr}
    (hf : f.contract = contract) (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hea : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)))
    (heb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)))
    (hel : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat))) (roundUp : Bool) :
    ∃ f', ExecBlock config f evm
      (.internalCall "SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool"
        [.var "sqrtPriceAX96", .var "sqrtPriceBX96", el, .boolLit roundUp] "amount" ::
        checkedAmountReturnBlock roundUp)
      (if amount0Fits a b liquidity roundUp ∧ (amount0Word a b liquidity roundUp).toNat < 2^255 then
        .returned f' evm (some [.int (EVM.signed (checkedAmountReturnWord (amount0Word a b liquidity roundUp) roundUp))])
       else .reverted) := by
  have hcall := amount0Call hf ha hb (evalLocalValue hea) (evalLocalValue heb) hel
    (show evalExpr? config f evm (.boolLit roundUp) = .ok (.bool roundUp) by simp only [evalExpr?, pure]) "amount"
  exact checkedAmountPath hf hcall roundUp

end Benchmarks.UniswapV4PoolManager
