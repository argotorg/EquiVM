import Benchmarks.UniswapV4PoolManager.BalanceTransfer
import Benchmarks.UniswapV4PoolManager.DeltaCount

/-! Shared source proof of the internal ERC6909 mint helper. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev balanceMintFunction : FunctionDecl := contract.functions[45]!
theorem balanceMintFunction_lookup :
    lookupCallable? contract "_mint" = some balanceMintFunction.toCallable := rfl

def balanceMintPost (evm : EVM.State) (receiver id amount : UInt256) : EVM.State :=
  balancePost evm receiver id (balanceWord evm receiver id + amount)

def balanceMintResult (f : Frame) (evm : EVM.State) (receiver id amount : UInt256) : ExecResult :=
  if (balanceWord evm receiver id).toNat + amount.toNat < UInt256.size then
    if evm.executionEnv.perm = false then .staticViolation else
    .returned f (balanceMintPost evm receiver id amount) none
  else .reverted

theorem balanceMintBodyExec {f : Frame} {evm : EVM.State} {receiver id amount : UInt256}
    (hf : f.contract = contract) (hcr : receiver.toNat < EVM.addressModulus)
    (hr : f.locals.get? "receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hi : f.locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "balanceOf" = none) :
    ExecFuncBody config f evm balanceMintFunction.body (balanceMintResult f evm receiver id amount) := by
  have hread := balanceOfRead (evm := evm) receiver id hf hcr hb (evalLocalValue hr) (evalLocalValue hi)
  rw [balanceMintResult]
  by_cases hfit : (balanceWord evm receiver id).toNat + amount.toNat < UInt256.size
  · rw [if_pos hfit]
    have heval := checkedAddSourceOk hread (evalLocalValue ha) hfit
    have hwrite := balanceOfWrite (evm := evm) receiver id (balanceWord evm receiver id + amount)
      hf hcr hb (evalLocalValue hr) (evalLocalValue hi)
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp]
      exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic (ExecStmt.assignStatic heval hwrite hp))
    · rw [if_neg hp]
      apply ExecFuncBody.execBlockOK
      refine ExecBlock.consNormal (ExecStmt.assign heval hwrite) (ExecBlock.consNormal (ExecStmt.emit
        (vals := [.address evm.executionEnv.source, .address (AccountAddress.ofNat 0),
          .address (AccountAddress.ofNat receiver.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)]) ?_) ExecBlock.nil)
      simp only [evalExprs?, evalExpr?, hr, hi, ha, EvalResult.ofOption, bind, EvalResult.bind,
        envValue, pure, balancePost_env, castValue?]
      rfl
  · rw [if_neg hfit]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.assignExprRevert
      (checkedAddSourceOverflow hread (evalLocalValue ha) (Nat.le_of_not_gt hfit))))

def balanceMintCallResult (f : Frame) (evm : EVM.State) (receiver id amount : UInt256) (retVar : Ident) : ExecResult :=
  if (balanceWord evm receiver id).toNat + amount.toNat < UInt256.size then
    if evm.executionEnv.perm = false then .staticViolation else
    .ok {f with locals := f.locals.insert retVar .unit} (balanceMintPost evm receiver id amount)
  else .reverted

theorem balanceMintCall {f : Frame} {evm : EVM.State} {receiver id amount : UInt256} {er ei ea : Expr}
    (hf : f.contract = contract) (hcr : receiver.toNat < EVM.addressModulus)
    (hr : evalExpr? config f evm er = .ok (.address (AccountAddress.ofNat receiver.toNat)))
    (hi : evalExpr? config f evm ei = .ok (.int (Int.ofNat id.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "_mint" [er, ei, ea] retVar)
      (balanceMintCallResult f evm receiver id amount retVar) := by
  let locals := (((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert "id" (.int (Int.ofNat id.toNat))).insert
    "receiver" (.address (AccountAddress.ofNat receiver.toNat))
  have hbody := balanceMintBodyExec (f := {f with locals := locals}) (evm := evm) hf hcr
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("receiver" == "id") = false)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide : ("receiver" == "amount") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "amount") = false)).trans (store_get_self _ _ _)))
    ((store_get_ne _ _ (by decide : ("receiver" == "balanceOf") = false)).trans
      ((store_get_ne _ _ (by decide : ("id" == "balanceOf") = false)).trans
        ((store_get_ne _ _ (by decide : ("amount" == "balanceOf") = false)).trans (store_get_empty _))))
  have hargs : evalExprs? config f evm [er, ei, ea] = .ok
      [.address (AccountAddress.ofNat receiver.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)] := by
    simp only [evalExprs?, hr, hi, ha, bind, EvalResult.bind, pure]
  have hl : lookupCallable? f.contract "_mint" = some balanceMintFunction.toCallable := by
    rw [hf]; exact balanceMintFunction_lookup
  have hbind : bindParams? balanceMintFunction.params
      [.address (AccountAddress.ofNat receiver.toNat), .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)] = some locals := rfl
  rw [balanceMintResult] at hbody
  rw [balanceMintCallResult]
  by_cases hfit : (balanceWord evm receiver id).toNat + amount.toNat < UInt256.size
  · rw [if_pos hfit] at hbody ⊢
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp] at hbody ⊢
      exact internalCallFunctionStatic hargs hl hbind hbody
    · rw [if_neg hp] at hbody ⊢
      exact internalCallFunctionReturn hargs hl hbind hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hl hbind hbody

end Benchmarks.UniswapV4PoolManager
