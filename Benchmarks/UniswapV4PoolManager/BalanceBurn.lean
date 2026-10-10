import Benchmarks.UniswapV4PoolManager.BalanceTransfer
import Benchmarks.UniswapV4PoolManager.DeltaCount

/-! Shared source proof of the internal ERC6909 burn helper. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev balanceBurnFunction : FunctionDecl := contract.functions[85]!
theorem balanceBurnFunction_lookup :
    lookupCallable? contract "_burn" = some balanceBurnFunction.toCallable := rfl

def balanceBurnPost (evm : EVM.State) (sender id amount : UInt256) : EVM.State :=
  balancePost evm sender id (UInt256.sub (balanceWord evm sender id) amount)

def balanceBurnResult (f : Frame) (evm : EVM.State) (sender id amount : UInt256) : ExecResult :=
  if amount.toNat ≤ (balanceWord evm sender id).toNat then
    if evm.executionEnv.perm = false then .staticViolation else
    .returned f (balanceBurnPost evm sender id amount) none
  else .reverted

theorem balanceBurnBodyExec {f : Frame} {evm : EVM.State} {sender id amount : UInt256}
    (hf : f.contract = contract) (hcr : sender.toNat < EVM.addressModulus)
    (hr : f.locals.get? "sender" = some (.address (AccountAddress.ofNat sender.toNat)))
    (hi : f.locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "balanceOf" = none) :
    ExecFuncBody config f evm balanceBurnFunction.body (balanceBurnResult f evm sender id amount) := by
  have hread := balanceOfRead (evm := evm) sender id hf hcr hb (evalLocalValue hr) (evalLocalValue hi)
  rw [balanceBurnResult]
  by_cases hfit : amount.toNat ≤ (balanceWord evm sender id).toNat
  · rw [if_pos hfit]
    have heval := evalExpr_uint256_sub hread (evalLocalValue ha) hfit
    have hwrite := balanceOfWrite (evm := evm) sender id (UInt256.sub (balanceWord evm sender id) amount)
      hf hcr hb (evalLocalValue hr) (evalLocalValue hi)
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp]
      exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic (ExecStmt.assignStatic heval hwrite hp))
    · rw [if_neg hp]
      apply ExecFuncBody.execBlockOK
      refine ExecBlock.consNormal (ExecStmt.assign heval hwrite) (ExecBlock.consNormal (ExecStmt.emit
        (vals := [.address evm.executionEnv.source, .address (AccountAddress.ofNat sender.toNat),
          .address (AccountAddress.ofNat 0), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)]) ?_) ExecBlock.nil)
      simp only [evalExprs?, evalExpr?, hr, hi, ha, EvalResult.ofOption, bind, EvalResult.bind,
        envValue, pure, balancePost_env, castValue?]
      rfl
  · rw [if_neg hfit]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.assignExprRevert
      (checkedSubSourceUnderflow hread (evalLocalValue ha) (Nat.lt_of_not_ge hfit))))

def balanceBurnCallResult (f : Frame) (evm : EVM.State) (sender id amount : UInt256) (retVar : Ident) : ExecResult :=
  if amount.toNat ≤ (balanceWord evm sender id).toNat then
    if evm.executionEnv.perm = false then .staticViolation else
    .ok {f with locals := f.locals.insert retVar .unit} (balanceBurnPost evm sender id amount)
  else .reverted

theorem balanceBurnCall {f : Frame} {evm : EVM.State} {sender id amount : UInt256} {er ei ea : Expr}
    (hf : f.contract = contract) (hcr : sender.toNat < EVM.addressModulus)
    (hr : evalExpr? config f evm er = .ok (.address (AccountAddress.ofNat sender.toNat)))
    (hi : evalExpr? config f evm ei = .ok (.int (Int.ofNat id.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "_burn" [er, ei, ea] retVar)
      (balanceBurnCallResult f evm sender id amount retVar) := by
  let locals := (((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert "id" (.int (Int.ofNat id.toNat))).insert
    "sender" (.address (AccountAddress.ofNat sender.toNat))
  have hbody := balanceBurnBodyExec (f := {f with locals := locals}) (evm := evm) hf hcr
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("sender" == "id") = false)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide : ("sender" == "amount") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "amount") = false)).trans (store_get_self _ _ _)))
    ((store_get_ne _ _ (by decide : ("sender" == "balanceOf") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "balanceOf") = false)).trans
        ((store_get_ne _ _ (by decide : ("amount" == "balanceOf") = false)).trans (store_get_empty _))))
  have hargs : evalExprs? config f evm [er, ei, ea] = .ok
      [.address (AccountAddress.ofNat sender.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)] := by
    simp only [evalExprs?, hr, hi, ha, bind, EvalResult.bind, pure]
  have hl : lookupCallable? f.contract "_burn" = some balanceBurnFunction.toCallable := by
    rw [hf]; exact balanceBurnFunction_lookup
  have hbind : bindParams? balanceBurnFunction.params
      [.address (AccountAddress.ofNat sender.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)] = some locals := rfl
  rw [balanceBurnResult] at hbody
  rw [balanceBurnCallResult]
  by_cases hfit : amount.toNat ≤ (balanceWord evm sender id).toNat
  · rw [if_pos hfit] at hbody ⊢
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp] at hbody ⊢
      exact internalCallFunctionStatic hargs hl hbind hbody
    · rw [if_neg hp] at hbody ⊢
      exact internalCallFunctionReturn hargs hl hbind hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hl hbind hbody

end Benchmarks.UniswapV4PoolManager
