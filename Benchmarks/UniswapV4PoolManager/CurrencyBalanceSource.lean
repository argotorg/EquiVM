import Benchmarks.UniswapV4PoolManager.CurrencyReservesSource
import Benchmarks.UniswapV4PoolManager.CurrencyBalanceABI
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev currencyBalanceFunction : FunctionDecl := contract.functions[24]!
theorem currencyBalance_lookup : lookupCallable? contract "CurrencyLibrary_balanceOfSelf" = some currencyBalanceFunction.toCallable := rfl

def currencyBalanceFrame (f : Frame) (currency : AccountAddress) (out : ByteArray) : Frame :=
  {f with locals := (((f.locals.insert "__c0" (.bool false)).insert "__c1" (.address currency)).insert
    "__c2" (.int (Int.ofNat (returnedBalanceWord out).toNat)))}

def currencyBalanceResult (f : Frame) (evm' : EVM.State) (currency : AccountAddress) (z : Bool) (out : ByteArray) : ExecResult :=
  if z = true ∧ 32 ≤ out.size then
    .returned (currencyBalanceFrame f currency out) evm' (some [.int (Int.ofNat (returnedBalanceWord out).toNat)])
  else .reverted

theorem currencyBalanceBody {f : Frame} {evm evm' : EVM.State} {currency : AccountAddress} {z : Bool} {out : ByteArray}
    (hf : f.contract = contract) (hc : f.locals.get? "currency" = some (.address currency))
    (hn : currency ≠ AccountAddress.ofNat 0) (ho : out.size < 2^255)
    (hcall : typedCallViaEVM config evm currency "balanceOf" 0 [.address evm.executionEnv.codeOwner] (z, evm', out) false) :
    ExecFuncBody config f evm currencyBalanceFunction.body (currencyBalanceResult f evm' currency z out) := by
  let f1 : Frame := {f with locals := f.locals.insert "__c0" (.bool false)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c1" (.address currency)}
  have hzero := currencyZeroCall (evm := evm) hf (evalLocalValue hc) "__c0"
  rw [decide_eq_false hn] at hzero
  have hguard : evalExpr? config f1 evm (.var "__c0") = .ok (.bool false) := evalLocalValue (store_get_self _ _ _)
  have hlet : ExecStmt config f1 evm (.letDecl "__c1" none (.cast (.var "currency") (.elem .address))) (.ok f2 evm) :=
    ExecStmt.letDecl (evalCastValue (evalLocalValue
      ((store_get_ne _ _ (by decide : ("__c0" == "currency") = false)).trans hc)) rfl)
  have hrecv : evalExpr? config f2 evm (.var "__c1") = .ok (.address currency) := evalLocalValue (store_get_self _ _ _)
  have heth : evalExpr? config f2 evm (.intLit 0) = .ok (.int 0) := by simp only [evalExpr?, pure]
  have hargs : evalExprs? config f2 evm [.env .this] = .ok [.address evm.executionEnv.codeOwner] := by
    simp only [evalExprs?, evalExpr?, envValue, bind, EvalResult.bind, pure]
  have hcall' : typedCallViaEVM config evm (EVM.address currency) "balanceOf" 0
      [.address evm.executionEnv.codeOwner] (z, evm', out) false := by
    simpa only [address_of_val] using hcall
  unfold currencyBalanceResult
  cases z with
  | false =>
    rw [if_neg (by simp)]
    exact .execBlockRevert (ExecBlock.consNormal hzero (ExecBlock.consRevert (ExecStmt.iteFalse hguard
      (ExecBlock.consNormal hlet (ExecBlock.consRevert (ExecStmt.externalCallFailure hrecv heth hargs hcall'))))))
  | true =>
    by_cases hlo : 32 ≤ out.size
    · rw [if_pos ⟨rfl, hlo⟩]
      have hbalance := ExecStmt.externalCallSuccess (retVar := "__c2") hrecv heth hargs hcall' (balanceOfDecode_ok hlo ho)
      exact .execBlockRet (ExecBlock.consNormal hzero (ExecBlock.consReturn (ExecStmt.iteFalse hguard
        (ExecBlock.consNormal hlet (ExecBlock.consNormal hbalance
          (ABlock.start.returns (evalLocalValue (store_get_self _ _ _))))))))
    · rw [if_neg (fun h => hlo h.2)]
      exact .execBlockRevert (ExecBlock.consNormal hzero (ExecBlock.consRevert (ExecStmt.iteFalse hguard
        (ExecBlock.consNormal hlet (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
          hrecv heth hargs hcall' (balanceOfDecode_short (Nat.lt_of_not_ge hlo))))))))

theorem currencyBalanceCall {f : Frame} {evm evm' : EVM.State} {e : Expr} {currency : AccountAddress} {z : Bool} {out : ByteArray}
    (hf : f.contract = contract) (hc : evalExpr? config f evm e = .ok (.address currency))
    (hn : currency ≠ AccountAddress.ofNat 0) (ho : out.size < 2^255)
    (hcall : typedCallViaEVM config evm currency "balanceOf" 0 [.address evm.executionEnv.codeOwner] (z, evm', out) false)
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyLibrary_balanceOfSelf" [e] retVar)
      (if z = true ∧ 32 ≤ out.size then
        .ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (returnedBalanceWord out).toNat))} evm'
      else .reverted) := by
  have hb := currencyBalanceBody (f := {f with locals := (∅ : Store).insert "currency" (.address currency)})
    hf (store_get_self _ _ _) hn ho hcall
  have hh := internalCallFunctionExec (caller := f) (name := "CurrencyLibrary_balanceOfSelf")
    (retVar := retVar) (args := [e]) (argVals := [.address currency]) (evalExprs?_singleton hc)
    (by rw [hf]; exact currencyBalance_lookup) rfl hb
  simpa only [currencyBalanceResult, resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_reverted] using hh

end Benchmarks.UniswapV4PoolManager
