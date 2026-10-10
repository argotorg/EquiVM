import Benchmarks.UniswapV4PoolManager.CurrencyId
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.AccountDeltaSource
import Benchmarks.UniswapV4PoolManager.BurnFromSource
import Benchmarks.UniswapV4PoolManager.SourceComposition

/-! Source execution of burn, preserving accounting before authorization and the balance debit. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def burnTailFrame (f : Frame) (currency : AccountAddress) : Frame :=
  {f with locals := (f.locals.insert "__c4" (.int (Int.ofNat (accountWord currency).toNat))).insert "__c5" .unit}

theorem burnTailExec {f : Frame} {evm : EVM.State} {sender amount : UInt256} {currency : AccountAddress}
    (hf : f.contract = contract) (hcr : sender.toNat < EVM.addressModulus)
    (hc : f.locals.get? "currency" = some (.address currency))
    (hr : f.locals.get? "from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ExecFuncBody config f evm (burnTransition.body.drop 8)
      (burnFromResult (burnTailFrame f currency) evm sender (accountWord currency) amount) := by
  have hconvert := currencyToIdCall (evm := evm) hf (evalLocalValue hc) "__c4"
  let f1 := {f with locals := f.locals.insert "__c4" (.int (Int.ofNat (accountWord currency).toNat))}
  have hr1 : f1.locals.get? "from" = some (.address (AccountAddress.ofNat sender.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c4" == "from") = false)).trans hr
  have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c4" == "amount") = false)).trans ha
  have hcall := burnFromCall (f := f1) (evm := evm) hf hcr (evalLocalValue hr1)
    (evalLocalValue (f := f1) (store_get_self _ _ _)) (evalLocalValue ha1) "__c5"
  have hbody := execFuncBody_prepend (execBlock_singleton hconvert) (execFuncBody_singleton hcall)
  simpa only [burnFromCallResult, burnFromResult, balanceBurnResult,
    resumeCallResult_ite, resumeCallResult_returned, resumeCallResult_reverted, resumeCallResult_static,
    finishBlockResult_ite, finishBlockResult_ok, finishBlockResult_reverted, finishBlockResult_static,
    burnTailFrame] using hbody

def burnAccountResult (f : Frame) (evm : EVM.State) (sender : UInt256) (currency : AccountAddress)
    (amount : UInt256) : ExecResult :=
  let f' := burnTailFrame {f with locals := f.locals.insert "__c3" .unit} currency
  if amount.toNat = 0 then burnFromResult f' evm sender (accountWord currency) amount else
  if int256Fits (currencyDeltaValue evm evm.executionEnv.source currency + Int.ofNat amount.toNat) then
    if evm.executionEnv.perm = false then .staticViolation else
    burnFromResult f' (accountDeltaPost evm evm.executionEnv.source currency (Int.ofNat amount.toNat))
      sender (accountWord currency) amount
  else .reverted

theorem burnAccountExec {f : Frame} {evm : EVM.State} {sender amount : UInt256} {currency : AccountAddress}
    (hf : f.contract = contract) (hcr : sender.toNat < EVM.addressModulus) (hfit : amount.toNat < 2^127)
    (hc : f.locals.get? "currency" = some (.address currency))
    (hr : f.locals.get? "from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hd : f.locals.get? "__c2" = some (.int (Int.ofNat amount.toNat))) :
    ExecFuncBody config f evm (burnTransition.body.drop 7) (burnAccountResult f evm sender currency amount) := by
  have hcall := accountDeltaCall (evm := evm) (et := .env .caller) hf (evalLocalValue hc) (evalLocalValue hd)
    (by simp only [evalExpr?, envValue, pure]; rfl) "__c3"
  let f1 := {f with locals := f.locals.insert "__c3" .unit}
  have hc1 : f1.locals.get? "currency" = some (.address currency) :=
    (store_get_ne _ _ (by decide : ("__c3" == "currency") = false)).trans hc
  have hr1 : f1.locals.get? "from" = some (.address (AccountAddress.ofNat sender.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c3" == "from") = false)).trans hr
  have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("__c3" == "amount") = false)).trans ha
  rw [burnAccountResult]
  rw [accountDeltaCallResult] at hcall
  by_cases hz : amount.toNat = 0
  · rw [if_pos hz]
    have hzInt : Int.ofNat amount.toNat = 0 := by rw [hz]; rfl
    rw [if_pos hzInt] at hcall
    exact execFuncBody_prepend (execBlock_singleton hcall) (burnTailExec (f := f1) hf hcr hc1 hr1 ha1)
  · rw [if_neg hz]
    have hzInt : Int.ofNat amount.toNat ≠ 0 := by simp only [Int.ofNat_eq_natCast]; omega
    rw [if_neg hzInt] at hcall
    by_cases hsum : int256Fits (currencyDeltaValue evm evm.executionEnv.source currency + Int.ofNat amount.toNat)
    · rw [if_pos hsum] at hcall ⊢
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp] at hcall ⊢
        exact .execBlockStatic (ExecBlock.consStatic hcall)
      · rw [if_neg hp] at hcall ⊢
        exact execFuncBody_prepend (execBlock_singleton hcall) (burnTailExec (f := f1) hf hcr hc1 hr1 ha1)
    · rw [if_neg hsum] at hcall ⊢
      exact .execBlockRevert (ExecBlock.consRevert hcall)

def burnInputFrame (f : Frame) (id amount : UInt256) : Frame :=
  {f with locals := ((f.locals.insert "__c0" (.bool true)).insert "currency"
    (.address (AccountAddress.ofNat id.toNat))).insert "__c2" (.int (Int.ofNat amount.toNat))}

def burnBodyResult (f : Frame) (evm : EVM.State) (sender id amount : UInt256) : ExecResult :=
  if transientWord evm lockSlot = ⟨0⟩ then .reverted else
  if amount.toNat < 2^127 then
    burnAccountResult (burnInputFrame f id amount) evm sender (AccountAddress.ofNat id.toNat) amount
  else .reverted

theorem burnBodyExec {evm : EVM.State} {locals imms : Store} {sender id amount : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcr : sender.toNat < EVM.addressModulus)
    (hr : locals.get? "from" = some (.address (AccountAddress.ofNat sender.toNat)))
    (hi : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ExecTransitionBody config contract evm locals burnTransition.body
      (burnBodyResult (calldataFrame contract locals imms evm) evm sender id amount) imms := by
  let f := calldataFrame contract locals imms evm
  have hlock := lockCall (f := f) (evm := evm) rfl "__c0"
  rw [burnBodyResult]
  apply nonpayableCalldataBody hwv hhi
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    rw [decide_eq_false (not_not.mpr hl)] at hlock
    exact .execBlockRevert (ExecBlock.consNormal hlock (ExecBlock.consRevert (ExecStmt.iteTrue
      (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?]; rfl))))))
  · rw [if_neg hl]
    rw [decide_eq_true hl] at hlock
    let f1 := {f with locals := f.locals.insert "__c0" (.bool true)}
    have hguard : ExecStmt config f1 evm burnTransition.body[4]! (.ok f1 evm) :=
      ExecStmt.iteFalse (evalNotBool (va := true) (evalLocalValue (store_get_self _ _ _))) ExecBlock.nil
    have hi1 : f1.locals.get? "id" = some (.int (Int.ofNat id.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c0" == "id") = false)).trans
        ((store_get_ne _ _ (by decide : ("__calldata" == "id") = false)).trans hi)
    have hcurrency := currencyFromIdCall (evm := evm) rfl (evalLocalValue hi1) "currency"
    let f2 := {f1 with locals := f1.locals.insert "currency" (.address (AccountAddress.ofNat id.toNat))}
    have ha2 : f2.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
      (store_get_ne _ _ (by decide : ("currency" == "amount") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c0" == "amount") = false)).trans
          ((store_get_ne _ _ (by decide : ("__calldata" == "amount") = false)).trans ha))
    by_cases hfit : amount.toNat < 2^127
    · rw [if_pos hfit]
      have hcast := uintToInt128Call rfl (evalLocalValue (cfg := config) (evm := evm) ha2) hfit "__c2"
      let f3 := {f2 with locals := f2.locals.insert "__c2" (.int (Int.ofNat amount.toNat))}
      have hr3 : f3.locals.get? "from" = some (.address (AccountAddress.ofNat sender.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c2" == "from") = false)).trans
          ((store_get_ne _ _ (by decide : ("currency" == "from") = false)).trans
            ((store_get_ne _ _ (by decide : ("__c0" == "from") = false)).trans
              ((store_get_ne _ _ (by decide : ("__calldata" == "from") = false)).trans hr)))
      have ha3 : f3.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c2" == "amount") = false)).trans ha2
      have hc3 : f3.locals.get? "currency" = some (.address (AccountAddress.ofNat id.toNat)) :=
        (store_get_ne _ _ (by decide : ("__c2" == "currency") = false)).trans (store_get_self _ _ _)
      exact execFuncBody_prepend
        (ExecBlock.consNormal hlock (ExecBlock.consNormal hguard (ExecBlock.consNormal hcurrency
          (ExecBlock.consNormal hcast ExecBlock.nil))))
        (burnAccountExec rfl hcr hfit hc3 hr3 ha3 (store_get_self _ _ _))
    · rw [if_neg hfit]
      have hcast := uintToInt128CallReverts rfl (evalLocalValue (cfg := config) (evm := evm) ha2) hfit "__c2"
      exact .execBlockRevert (ExecBlock.consNormal hlock (ExecBlock.consNormal hguard
        (ExecBlock.consNormal hcurrency (ExecBlock.consRevert hcast))))

end Benchmarks.UniswapV4PoolManager
