import Benchmarks.UniswapV4PoolManager.Amount1Words
import Benchmarks.UniswapV4PoolManager.FullMathSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev amount1Function : FunctionDecl := contract.functions[94]!
theorem amount1_lookup : lookupCallable? contract "SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool" =
    some amount1Function.toCallable := rfl

theorem amount1Tail {f : Frame} {evm : EVM.State} {a b liquidity : UInt256} {roundUp : Bool}
    (hl : f.locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hn : f.locals.get? "numerator" = some (.int (Int.ofNat (absDiffWord a b).toNat)))
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat fullMathQ96.toNat)))
    (ha : f.locals.get? "amount1" = some (.int (Int.ofNat (fullMathWord liquidity (absDiffWord a b) fullMathQ96).toNat)))
    (hr : f.locals.get? "roundUp" = some (.bool roundUp)) :
    ExecFuncBody config f evm (amount1Function.body.drop 6)
      (.returned (wordLocal f "amount1" (amount1Word a b liquidity roundUp)) evm
        (some [.int (Int.ofNat (amount1Word a b liquidity roundUp).toNat)])) := by
  have hrem := evalWordMulMod (evalLocalValue (cfg := config) (f := f) (evm := evm) hl)
    (evalLocalValue hn) (evalLocalValue hd) fullMathQ96_ne
  have hgt := evalWordGt (a := fullMathRemainder liquidity (absDiffWord a b) fullMathQ96) (b := ⟨0⟩) hrem
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  have he := evalWordAdd
    (evalLocalValue (cfg := config) (f := f) (evm := evm) ha)
    (evalBoolWord (evalAndBool (evalLocalValue hr) hgt))
  exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.assign he (assignLocalValue ha))
    (ABlock.start.returns wordLocal_eval))

end Benchmarks.UniswapV4PoolManager
