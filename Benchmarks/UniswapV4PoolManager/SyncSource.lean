import Benchmarks.UniswapV4PoolManager.CurrencyBalanceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def syncZeroResult (f : Frame) (evm : EVM.State) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation else
    .returned {f with locals := (f.locals.insert "__c0" (.bool true)).insert "__c1" .unit}
      (resetCurrencyPost evm) none

theorem syncZeroBody {evm : EVM.State} {locals imms : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : locals.get? "currency" = some (.address (AccountAddress.ofNat 0))) :
    ExecTransitionBody config contract evm locals syncTransition.body
      (syncZeroResult (calldataFrame contract locals imms evm) evm) imms := by
  let f := calldataFrame contract locals imms evm
  let f1 : Frame := {f with locals := f.locals.insert "__c0" (.bool true)}
  have hzero := currencyZeroCall (f := f) (evm := evm) rfl (evalLocalValue
    ((store_get_ne _ _ (by decide : ("__calldata" == "currency") = false)).trans hc)) "__c0"
  simp only [decide_true] at hzero
  have hreset := resetCurrencyCall (f := f1) (evm := evm) rfl "__c1"
  unfold syncZeroResult
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp] at hreset ⊢
    apply ExecFuncBody.execBlockStatic
    apply nonpayableCalldataBlock hwv hhi
    exact ExecBlock.consNormal hzero (ExecBlock.consStatic (ExecStmt.iteTrue
      (evalLocalValue (store_get_self _ _ _)) (ExecBlock.consStatic hreset)))
  · rw [if_neg hp] at hreset ⊢
    apply ExecFuncBody.execBlockOK
    apply nonpayableCalldataBlock hwv hhi
    exact ExecBlock.consNormal hzero (ExecBlock.consNormal (ExecStmt.iteTrue
      (evalLocalValue (store_get_self _ _ _)) (ExecBlock.consNormal hreset ExecBlock.nil)) ExecBlock.nil)

def syncTokenResult (f : Frame) (evm' : EVM.State) (currency : AccountAddress) (z : Bool) (out : ByteArray) : ExecResult :=
  if z = true ∧ 32 ≤ out.size then
    if evm'.executionEnv.perm = false then .staticViolation else
      .returned {f with locals := (((f.locals.insert "__c0" (.bool false)).insert "balance"
        (.int (Int.ofNat (returnedBalanceWord out).toNat))).insert "__c3" .unit)}
        (syncReservesPost evm' currency (returnedBalanceWord out)) none
  else .reverted

theorem syncTokenBody {evm evm' : EVM.State} {locals imms : Store} {currency : AccountAddress} {z : Bool} {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : locals.get? "currency" = some (.address currency)) (hn : currency ≠ AccountAddress.ofNat 0)
    (ho : out.size < 2^255)
    (hcall : typedCallViaEVM config evm currency "balanceOf" 0 [.address evm.executionEnv.codeOwner] (z, evm', out) false) :
    ExecTransitionBody config contract evm locals syncTransition.body
      (syncTokenResult (calldataFrame contract locals imms evm) evm' currency z out) imms := by
  let f := calldataFrame contract locals imms evm
  let f1 : Frame := {f with locals := f.locals.insert "__c0" (.bool false)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "balance" (.int (Int.ofNat (returnedBalanceWord out).toNat))}
  have hc0 : f.locals.get? "currency" = some (.address currency) :=
    (store_get_ne _ _ (by decide : ("__calldata" == "currency") = false)).trans hc
  have hzero := currencyZeroCall (f := f) (evm := evm) rfl (evalLocalValue hc0) "__c0"
  rw [decide_eq_false hn] at hzero
  have hc1 : f1.locals.get? "currency" = some (.address currency) :=
    (store_get_ne _ _ (by decide : ("__c0" == "currency") = false)).trans hc0
  have hbalance := currencyBalanceCall (f := f1) (evm := evm) rfl (evalLocalValue hc1) hn ho hcall "balance"
  have hguard : evalExpr? config f1 evm (.var "__c0") = .ok (.bool false) := evalLocalValue (store_get_self _ _ _)
  unfold syncTokenResult
  by_cases hg : z = true ∧ 32 ≤ out.size
  · rw [if_pos hg] at hbalance ⊢
    have hsync := syncReservesCall (f := f2) (evm := evm') rfl
      (evalLocalValue ((store_get_ne _ _ (by decide : ("balance" == "currency") = false)).trans hc1))
      (evalLocalValue (store_get_self _ _ _)) "__c3"
    by_cases hp : evm'.executionEnv.perm = false
    · rw [if_pos hp] at hsync ⊢
      apply ExecFuncBody.execBlockStatic
      apply nonpayableCalldataBlock hwv hhi
      exact ExecBlock.consNormal hzero (ExecBlock.consStatic (ExecStmt.iteFalse hguard
        (ExecBlock.consNormal hbalance (ExecBlock.consStatic hsync))))
    · rw [if_neg hp] at hsync ⊢
      apply ExecFuncBody.execBlockOK
      apply nonpayableCalldataBlock hwv hhi
      exact ExecBlock.consNormal hzero (ExecBlock.consNormal (ExecStmt.iteFalse hguard
        (ExecBlock.consNormal hbalance (ExecBlock.consNormal hsync ExecBlock.nil))) ExecBlock.nil)
  · rw [if_neg hg] at hbalance ⊢
    apply ExecFuncBody.execBlockRevert
    apply nonpayableCalldataBlock hwv hhi
    exact ExecBlock.consNormal hzero (ExecBlock.consRevert (ExecStmt.iteFalse hguard (ExecBlock.consRevert hbalance)))

end Benchmarks.UniswapV4PoolManager
