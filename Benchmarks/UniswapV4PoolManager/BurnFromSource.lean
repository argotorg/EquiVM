import Benchmarks.UniswapV4PoolManager.BurnAuthorization
import Benchmarks.UniswapV4PoolManager.BalanceBurn
import Benchmarks.UniswapV4PoolManager.CallComposition

/-! Source composition of authorization and the ERC6909 balance burn. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem burnFromFunction_lookup : lookupCallable? contract "_burnFrom" = some burnFromFunction.toCallable := rfl

def burnFromResult (f : Frame) (evm : EVM.State) (sender id amount : UInt256) : ExecResult :=
  if transferFromNeedsAllowance evm sender then
    let allowed := transferFromAllowed evm sender id
    if allowed = maxAllowanceWord then balanceBurnResult f evm sender id amount else
    if amount.toNat ≤ allowed.toNat then
      if evm.executionEnv.perm = false then .staticViolation else
      balanceBurnResult f (transferFromAllowancePost evm sender id amount) sender id amount
    else .reverted
  else balanceBurnResult f evm sender id amount

def burnFromFinalFrame (f : Frame) (evm : EVM.State) (sender id : UInt256) : Frame :=
  let f1 := {f with locals := f.locals.insert "sender" (.address evm.executionEnv.source)}
  let f2 := if transferFromNeedsAllowance evm sender then burnAllowedFrame f1 (transferFromAllowed evm sender id) else f1
  {f2 with locals := f2.locals.insert "__c0" .unit}

theorem burnFromTailExec {f : Frame} {evm : EVM.State} {sender id amount : UInt256}
    (h : BurnFromArgs f sender id amount) (hcs : sender.toNat < EVM.addressModulus) :
    ExecFuncBody config f evm (burnFromFunction.body.drop 2)
      (balanceBurnResult {f with locals := f.locals.insert "__c0" .unit} evm sender id amount) := by
  have hcall := balanceBurnCall (evm := evm) h.contract_eq hcs (evalLocalValue h.from_get)
    (evalLocalValue h.id_get) (evalLocalValue h.amount_get) "__c0"
  have hbody := execFuncBody_singleton hcall
  simpa only [balanceBurnCallResult, finishBlockResult_ite, finishBlockResult_ok,
    finishBlockResult_static, finishBlockResult_reverted, balanceBurnResult] using hbody

theorem burnFromBodyExec {f : Frame} {evm : EVM.State} {sender id amount : UInt256}
    (h : BurnFromArgs f sender id amount) (hcs : sender.toNat < EVM.addressModulus) :
    ExecFuncBody config f evm burnFromFunction.body
      (burnFromResult (burnFromFinalFrame f evm sender id) evm sender id amount) := by
  let f1 := {f with locals := f.locals.insert "sender" (.address evm.executionEnv.source)}
  have hargs : BurnFromArgs f1 sender id amount := by
    refine ⟨h.contract_eq, ?_, ?_, ?_, ?_, ?_⟩
    · exact (store_get_ne _ _ (by decide : ("sender" == "from") = false)).trans h.from_get
    · exact (store_get_ne _ _ (by decide : ("sender" == "id") = false)).trans h.id_get
    · exact (store_get_ne _ _ (by decide : ("sender" == "amount") = false)).trans h.amount_get
    · exact (store_get_ne _ _ (by decide : ("sender" == "isOperator") = false)).trans h.operator_get
    · exact (store_get_ne _ _ (by decide : ("sender" == "allowance") = false)).trans h.allowance_get
  have hlet : ExecStmt config f evm burnFromFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, envValue, pure])
  have hauth := burnAuthExec (evm := evm) hargs hcs (store_get_self _ _ _)
  rw [burnFromResult, burnFromFinalFrame]
  by_cases hneed : transferFromNeedsAllowance evm sender
  · simp only [if_pos hneed]
    rw [burnAuthResult, if_pos hneed] at hauth
    have hargs' := burnAllowedFrame_args hargs (transferFromAllowed evm sender id)
    by_cases hmax : transferFromAllowed evm sender id = maxAllowanceWord
    · rw [if_pos hmax] at hauth ⊢
      exact execFuncBody_prepend (ExecBlock.consNormal hlet (ExecBlock.consNormal hauth ExecBlock.nil))
        (burnFromTailExec hargs' hcs)
    · rw [if_neg hmax] at hauth ⊢
      by_cases hsub : amount.toNat ≤ (transferFromAllowed evm sender id).toNat
      · rw [if_pos hsub] at hauth ⊢
        by_cases hp : evm.executionEnv.perm = false
        · rw [if_pos hp] at hauth ⊢
          exact .execBlockStatic (ExecBlock.consNormal hlet (ExecBlock.consStatic hauth))
        · rw [if_neg hp] at hauth ⊢
          exact execFuncBody_prepend (ExecBlock.consNormal hlet (ExecBlock.consNormal hauth ExecBlock.nil))
            (burnFromTailExec hargs' hcs)
      · rw [if_neg hsub] at hauth ⊢
        exact .execBlockRevert (ExecBlock.consNormal hlet (ExecBlock.consRevert hauth))
  · simp only [if_neg hneed]
    rw [burnAuthResult, if_neg hneed] at hauth
    exact execFuncBody_prepend (ExecBlock.consNormal hlet (ExecBlock.consNormal hauth ExecBlock.nil))
      (burnFromTailExec hargs hcs)

def burnFromCallResult (f : Frame) (evm : EVM.State) (sender id amount : UInt256) (retVar : Ident) : ExecResult :=
  resumeCallResult f retVar (burnFromResult f evm sender id amount)

theorem burnFromCall {f : Frame} {evm : EVM.State} {sender id amount : UInt256} {es ei ea : Expr}
    (hf : f.contract = contract) (hcs : sender.toNat < EVM.addressModulus)
    (hs : evalExpr? config f evm es = .ok (.address (AccountAddress.ofNat sender.toNat)))
    (hi : evalExpr? config f evm ei = .ok (.int (Int.ofNat id.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "_burnFrom" [es, ei, ea] retVar)
      (burnFromCallResult f evm sender id amount retVar) := by
  let locals := (((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert "id" (.int (Int.ofNat id.toNat))).insert
    "from" (.address (AccountAddress.ofNat sender.toNat))
  have hparams : BurnFromArgs {f with locals := locals} sender id amount := by
    refine ⟨hf, store_get_self _ _ _, ?_, ?_, ?_, ?_⟩
    · exact (store_get_ne _ _ (by decide : ("from" == "id") = false)).trans (store_get_self _ _ _)
    · exact (store_get_ne _ _ (by decide : ("from" == "amount") = false)).trans
        ((store_get_ne _ _ (by decide : ("id" == "amount") = false)).trans (store_get_self _ _ _))
    · exact (store_get_ne _ _ (by decide : ("from" == "isOperator") = false)).trans
        ((store_get_ne _ _ (by decide : ("id" == "isOperator") = false)).trans
          ((store_get_ne _ _ (by decide : ("amount" == "isOperator") = false)).trans (store_get_empty _)))
    · exact (store_get_ne _ _ (by decide : ("from" == "allowance") = false)).trans
        ((store_get_ne _ _ (by decide : ("id" == "allowance") = false)).trans
          ((store_get_ne _ _ (by decide : ("amount" == "allowance") = false)).trans (store_get_empty _)))
  have hbody := burnFromBodyExec (evm := evm) hparams hcs
  have hargs : evalExprs? config f evm [es, ei, ea] = .ok
      [.address (AccountAddress.ofNat sender.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)] := by
    simp only [evalExprs?, hs, hi, ha, bind, EvalResult.bind, pure]
  have hl : lookupCallable? f.contract "_burnFrom" = some burnFromFunction.toCallable := by
    rw [hf]; exact burnFromFunction_lookup
  have hbind : bindParams? burnFromFunction.params
      [.address (AccountAddress.ofNat sender.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)] = some locals := rfl
  have hcall := internalCallFunctionExec (retVar := retVar) hargs hl hbind hbody
  simpa only [burnFromCallResult, burnFromResult, balanceBurnResult, resumeCallResult_ite,
    resumeCallResult_returned, resumeCallResult_reverted, resumeCallResult_static] using hcall

end Benchmarks.UniswapV4PoolManager
