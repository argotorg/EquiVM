import Benchmarks.UniswapV3.Pool.CallbackEncoding
import Benchmarks.UniswapV3.Pool.Calls
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def flashCallbackStmts : List Stmt :=
  [.require (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)),
    .externalCall (.var "callback") "uniswapV3FlashCallback" (.intLit 0)
      [.var "fee0", .var "fee1", .var "data"] "__c7"]

theorem evalFlashCallbackArgs {frame : Frame} {evm : EVM.State}
    {fee0 fee1 : UInt256} {data : ByteArray}
    (hf0 : frame.locals.get? "fee0" = some (.int (Int.ofNat fee0.toNat)))
    (hf1 : frame.locals.get? "fee1" = some (.int (Int.ofNat fee1.toNat)))
    (hd : frame.locals.get? "data" = some (.bytes data)) :
    evalExprs? config frame evm [.var "fee0", .var "fee1", .var "data"] =
      .ok [.int (Int.ofNat fee0.toNat), .int (Int.ofNat fee1.toNat), .bytes data] := by
  simp only [evalExprs?, evalExpr_var_get hf0, evalExpr_var_get hf1, evalExpr_var_get hd,
    bind, EvalResult.bind, pure]

theorem evalFlashCallbackGuard {frame : Frame} {evm : EVM.State} {σ : AccountMap}
    {target : AccountAddress} (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target)) :
    evalExpr? config frame evm (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord σ (EVM.word target.val)).toNat))) :=
  evalExpr_codeGuard_of_accounts_eq ha (accountAddress_roundtrip target).symm (evalExpr_var_get ht)

theorem flashCallbackNoCode {frame : Frame} {evm : EVM.State} {σ : AccountMap}
    {target : AccountAddress} (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hc : extCodeSizeWord σ (EVM.word target.val) = ⟨0⟩) :
    ExecBlock config frame evm flashCallbackStmts .reverted := by
  apply checkedExternalCallVarNoCode
  simpa only [hc, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalFlashCallbackGuard ha ht

theorem flashCallbackGuardTrue {frame : Frame} {evm : EVM.State} {σ : AccountMap}
    {target : AccountAddress} (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hc : extCodeSizeWord σ (EVM.word target.val) ≠ ⟨0⟩) :
    evalExpr? config frame evm (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)) =
      .ok (.bool true) := by
  have hp : 0 < (extCodeSizeWord σ (EVM.word target.val)).toNat := by
    by_contra hn
    apply hc
    apply u256_inj
    change _ = 0
    omega
  simpa only [hp, decide_true] using evalFlashCallbackGuard ha ht

theorem flashCallbackReverts {frame : Frame} {evm evm' : EVM.State} {σ : AccountMap}
    {target : AccountAddress} {fee0 fee1 : UInt256} {data out : ByteArray}
    (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "fee0" = some (.int (Int.ofNat fee0.toNat)))
    (hf1 : frame.locals.get? "fee1" = some (.int (Int.ofNat fee1.toNat)))
    (hd : frame.locals.get? "data" = some (.bytes data))
    (hc : extCodeSizeWord σ (EVM.word target.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm target 0 (flashCallbackCalldata fee0 fee1 data) (false, evm', out)) :
    ExecBlock config frame evm flashCallbackStmts .reverted := by
  apply checkedExternalCallVarFailure (evm' := evm') (out := out) (flashCallbackGuardTrue ha ht hc) ht
    (evalFlashCallbackArgs hf0 hf1 hd)
  refine ⟨flashCallbackCalldata fee0 fee1 data, flashCallbackEncode fee0 fee1 data, ?_⟩
  simpa only [show EVM.address target.val = target from by
      apply Fin.ext
      exact Nat.mod_eq_of_lt target.isLt] using hcall

theorem flashCallbackReturns {frame : Frame} {evm evm' : EVM.State} {σ : AccountMap}
    {target : AccountAddress} {fee0 fee1 : UInt256} {data out : ByteArray}
    (ha : σ = evm.accountMap)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "fee0" = some (.int (Int.ofNat fee0.toNat)))
    (hf1 : frame.locals.get? "fee1" = some (.int (Int.ofNat fee1.toNat)))
    (hd : frame.locals.get? "data" = some (.bytes data))
    (hc : extCodeSizeWord σ (EVM.word target.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm target 0 (flashCallbackCalldata fee0 fee1 data) (true, evm', out)) :
    ExecBlock config frame evm flashCallbackStmts
      (.ok {frame with locals := frame.locals.insert "__c7" .unit} evm') := by
  apply checkedExternalCallVarSuccess (out := out) (flashCallbackGuardTrue ha ht hc) ht
    (evalFlashCallbackArgs hf0 hf1 hd) (value := [])
  · refine ⟨flashCallbackCalldata fee0 fee1 data, flashCallbackEncode fee0 fee1 data, ?_⟩
    simpa only [show EVM.address target.val = target from by
      apply Fin.ext
      exact Nat.mod_eq_of_lt target.isLt] using hcall
  · exact flashCallbackDecode out

end Benchmarks.UniswapV3.Pool
