import Benchmarks.UniswapV3.Pool.MintCallbackEncoding
import Benchmarks.UniswapV3.Pool.FlashCallbackSource
import Benchmarks.UniswapV3.Pool.Calls
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def mintCallbackStmts : List Stmt :=
  [.require (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)),
    .externalCall (.var "callback") "uniswapV3MintCallback" (.intLit 0)
      [.var "amount0", .var "amount1", .var "data"] "__c4"]

theorem evalMintCallbackArgs {frame : Frame} {evm : EVM.State}
    {amount0 amount1 : UInt256} {data : ByteArray}
    (hf0 : frame.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (hf1 : frame.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : frame.locals.get? "data" = some (.bytes data)) :
    evalExprs? config frame evm [.var "amount0", .var "amount1", .var "data"] =
      .ok [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat), .bytes data] := by
  simp only [evalExprs?, evalExpr_var_get hf0, evalExpr_var_get hf1, evalExpr_var_get hd,
    bind, EvalResult.bind, pure]

theorem mintCallbackNoCode {frame : Frame} {evm : EVM.State} {σ : AccountMap}
    {target : AccountAddress} (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hc : extCodeSizeWord σ (EVM.word target.val) = ⟨0⟩) :
    ExecBlock config frame evm mintCallbackStmts .reverted := by
  apply checkedExternalCallVarNoCode
  simpa only [hc, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalFlashCallbackGuard ha ht

theorem mintCallbackReverts {frame : Frame} {evm evm' : EVM.State} {σ : AccountMap}
    {target : AccountAddress} {amount0 amount1 : UInt256} {data out : ByteArray}
    (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (hf1 : frame.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : frame.locals.get? "data" = some (.bytes data))
    (hc : extCodeSizeWord σ (EVM.word target.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm target 0 (mintCallbackCalldata amount0 amount1 data) (false, evm', out)) :
    ExecBlock config frame evm mintCallbackStmts .reverted := by
  apply checkedExternalCallVarFailure (evm' := evm') (out := out) (flashCallbackGuardTrue ha ht hc) ht
    (evalMintCallbackArgs hf0 hf1 hd)
  refine ⟨mintCallbackCalldata amount0 amount1 data, mintCallbackEncode amount0 amount1 data, ?_⟩
  simpa only [show EVM.address target.val = target from by
      apply Fin.ext
      exact Nat.mod_eq_of_lt target.isLt] using hcall

theorem mintCallbackReturns {frame : Frame} {evm evm' : EVM.State} {σ : AccountMap}
    {target : AccountAddress} {amount0 amount1 : UInt256} {data out : ByteArray}
    (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (hf1 : frame.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : frame.locals.get? "data" = some (.bytes data))
    (hc : extCodeSizeWord σ (EVM.word target.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm target 0 (mintCallbackCalldata amount0 amount1 data) (true, evm', out)) :
    ExecBlock config frame evm mintCallbackStmts
      (.ok {frame with locals := frame.locals.insert "__c4" .unit} evm') := by
  apply checkedExternalCallVarSuccess (out := out) (flashCallbackGuardTrue ha ht hc) ht
    (evalMintCallbackArgs hf0 hf1 hd) (value := [])
  · refine ⟨mintCallbackCalldata amount0 amount1 data, mintCallbackEncode amount0 amount1 data, ?_⟩
    simpa only [show EVM.address target.val = target from by
      apply Fin.ext
      exact Nat.mod_eq_of_lt target.isLt] using hcall
  · exact mintCallbackDecode out

end Benchmarks.UniswapV3.Pool
