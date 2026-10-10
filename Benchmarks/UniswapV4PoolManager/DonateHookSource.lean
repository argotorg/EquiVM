import Benchmarks.UniswapV4PoolManager.DonateHookABI
import Benchmarks.UniswapV4PoolManager.InitializeHookSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def donateHookFunction (after : Bool) : FunctionDecl :=
  if after then contract.functions[40]! else contract.functions[39]!
def donateHookFlag (after : Bool) : UInt256 := if after then ⟨16⟩ else ⟨32⟩
def donateHookFunctionName (after : Bool) : Ident := if after then "Hooks_afterDonate" else "Hooks_beforeDonate"

theorem donateHookBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {amount0 amount1 : UInt256} {data out : ByteArray} {z : Bool}
    (after : Bool) (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : f.locals.get? "hookData" = some (.bytes data)) (hc : PoolKeyCanonical key)
    (hcall : hookEnabled evm.executionEnv.source hook (donateHookFlag after) →
      callViaEVM evm hook 0 (donateHookPayload after evm.executionEnv.source key amount0 amount1 data) (z, post, out)) :
    ∃ f', ExecFuncBody config f evm (donateHookFunction after).body
      (hookInvocationResult f' evm post (hookEnabled evm.executionEnv.source hook (donateHookFlag after)) z
        (donateHookPayload after evm.executionEnv.source key amount0 amount1 data) out) := by
  have hcaller : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
    simp only [evalExpr?, envValue, pure]
  have htuple := evalPoolKeyTuple (evalLocalValue (cfg := config) (evm := evm) hk)
  have ha0 := evalLocalValue (cfg := config) (evm := evm) h0
  have ha1 := evalLocalValue (cfg := config) (evm := evm) h1
  have hdata := evalLocalValue (cfg := config) (evm := evm) hd
  have hargs : evalExprList? config f evm [.env .caller, poolKeyTupleExpr (.var "key"),
      .var "amount0", .var "amount1", .var "hookData"] =
      .ok (donateHookValues evm.executionEnv.source key amount0 amount1 data) := by
    simp only [evalExprList?, hcaller, htuple, ha0, ha1, hdata, bind, EvalResult.bind, pure]
    rfl
  have hr := conditionalHookBody hf hs
    (hookEnabled_eval hs (donateHookFlag after) (by cases after <;> decide))
    (evalABIEncodeCall hargs (donateHookEncode after _ _ _ _ hc))
    (by rw [donateHookPayload_size]; omega) hcall
  cases after <;> exact hr

theorem donateHook_lookup (after : Bool) : lookupCallable? contract (donateHookFunctionName after) =
    some (donateHookFunction after).toCallable := by cases after <;> rfl

theorem donateHookCall {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {amount0 amount1 : UInt256} {data out : ByteArray} {z : Bool}
    {es ek e0 e1 ed : Expr} (after : Bool) (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (h0 : evalExpr? config f evm e0 = .ok (.int (Int.ofNat amount0.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (Int.ofNat amount1.toNat)))
    (hd : evalExpr? config f evm ed = .ok (.bytes data)) (hc : PoolKeyCanonical key)
    (hcall : hookEnabled evm.executionEnv.source hook (donateHookFlag after) →
      callViaEVM evm hook 0 (donateHookPayload after evm.executionEnv.source key amount0 amount1 data) (z, post, out))
    (ret : Ident) :
    ExecStmt config f evm (.internalCall (donateHookFunctionName after) [es, ek, e0, e1, ed] ret)
      (resumeCallResult f ret (hookInvocationResult f evm post
        (hookEnabled evm.executionEnv.source hook (donateHookFlag after)) z
        (donateHookPayload after evm.executionEnv.source key amount0 amount1 data) out)) := by
  let s := (∅ : Store).insert "hookData" (.bytes data)
  let s1 := s.insert "amount1" (.int (Int.ofNat amount1.toNat))
  let s2 := s1.insert "amount0" (.int (Int.ofNat amount0.toNat))
  let s3 := s2.insert "key" (poolKeyValue key)
  let cf : Frame := {f with locals := s3.insert "self" (.address hook)}
  obtain ⟨f', hb⟩ := donateHookBody (f := cf) after hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide) (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide) (by decide) (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne4 _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)).trans (store_get_self _ _ _)) hc hcall
  have hargs : evalExprs? config f evm [es, ek, e0, e1, ed] =
      .ok [.address hook, poolKeyValue key, .int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat), .bytes data] := by
    simp only [evalExprs?, hs, hk, h0, h1, hd, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract (donateHookFunctionName after) =
      some (donateHookFunction after).toCallable := by rw [hf]; exact donateHook_lookup after
  have hbind : bindParams? (donateHookFunction after).params
      [.address hook, poolKeyValue key, .int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat), .bytes data] =
      some cf.locals := by cases after <;> rfl
  have hr := internalCallFunctionExec (retVar := ret) hargs hlookup hbind hb
  simpa only [hookInvocationResult, resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_reverted] using hr

end Benchmarks.UniswapV4PoolManager
