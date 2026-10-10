import Benchmarks.UniswapV3.Pool.SwapCallbackEncoding
import Benchmarks.UniswapV3.Pool.FlashCallbackSource
import Benchmarks.UniswapV3.Pool.Calls
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def swapCallbackName (zeroForOne : Bool) : Ident :=
  if zeroForOne then "__c23" else "__c28"

def swapCallbackStmts (zeroForOne : Bool) : List Stmt :=
  [.require (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)),
    .externalCall (.var "callback") "uniswapV3SwapCallback" (.intLit 0)
      [.var "amount0", .var "amount1", .var "data"] (swapCallbackName zeroForOne)]

theorem evalSwapCallbackArgs {frame : Frame} {evm : EVM.State}
    {amount0 amount1 : Int} {data : ByteArray}
    (hf0 : frame.locals.get? "amount0" = some (.int amount0))
    (hf1 : frame.locals.get? "amount1" = some (.int amount1))
    (hd : frame.locals.get? "data" = some (.bytes data)) :
    evalExprs? config frame evm [.var "amount0", .var "amount1", .var "data"] =
      .ok [.int amount0, .int amount1, .bytes data] := by
  simp only [evalExprs?, evalExpr_var_get hf0, evalExpr_var_get hf1, evalExpr_var_get hd,
    bind, EvalResult.bind, pure]

theorem swapCallbackNoCode {frame : Frame} {evm : EVM.State} {σ : AccountMap}
    {target : AccountAddress} (zeroForOne : Bool) (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hc : extCodeSizeWord σ (EVM.word target.val) = ⟨0⟩) :
    ExecBlock config frame evm (swapCallbackStmts zeroForOne) .reverted := by
  apply checkedExternalCallVarNoCode
  simpa only [hc, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalFlashCallbackGuard ha ht

theorem swapCallbackReverts {frame : Frame} {evm evm' : EVM.State} {σ : AccountMap}
    {target : AccountAddress} {amount0 amount1 : Int} {data out : ByteArray}
    (zeroForOne : Bool) (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "amount0" = some (.int amount0))
    (hf1 : frame.locals.get? "amount1" = some (.int amount1))
    (hd : frame.locals.get? "data" = some (.bytes data))
    (h0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (h1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255)
    (hc : extCodeSizeWord σ (EVM.word target.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm target 0 (swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt
      amount1) data) (false, evm', out)) :
    ExecBlock config frame evm (swapCallbackStmts zeroForOne) .reverted := by
  apply checkedExternalCallVarFailure (evm' := evm') (out := out) (flashCallbackGuardTrue ha ht hc)
    ht
    (evalSwapCallbackArgs hf0 hf1 hd)
  refine ⟨swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt amount1) data,
    swapCallbackEncode amount0 amount1 data h0 h1, ?_⟩
  simpa only [show EVM.address target.val = target from by
      apply Fin.ext
      exact Nat.mod_eq_of_lt target.isLt] using hcall

theorem swapCallbackReturns {frame : Frame} {evm evm' : EVM.State} {σ : AccountMap}
    {target : AccountAddress} {amount0 amount1 : Int} {data out : ByteArray}
    (zeroForOne : Bool) (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "amount0" = some (.int amount0))
    (hf1 : frame.locals.get? "amount1" = some (.int amount1))
    (hd : frame.locals.get? "data" = some (.bytes data))
    (h0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (h1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255)
    (hc : extCodeSizeWord σ (EVM.word target.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm target 0 (swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt
      amount1) data) (true, evm', out)) :
    ExecBlock config frame evm (swapCallbackStmts zeroForOne)
      (.ok {frame with locals := frame.locals.insert (swapCallbackName zeroForOne) .unit} evm') :=
        by
  apply checkedExternalCallVarSuccess (out := out) (flashCallbackGuardTrue ha ht hc) ht
    (evalSwapCallbackArgs hf0 hf1 hd) (value := [])
  · refine ⟨swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt amount1) data,
    swapCallbackEncode amount0 amount1 data h0 h1, ?_⟩
    simpa only [show EVM.address target.val = target from by
      apply Fin.ext
      exact Nat.mod_eq_of_lt target.isLt] using hcall
  · exact swapCallbackDecode out

end Benchmarks.UniswapV3.Pool
