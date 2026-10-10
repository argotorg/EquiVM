import Benchmarks.UniswapV4PoolManager.SettlePaidSource
import Benchmarks.UniswapV4PoolManager.CurrencyBalanceSource
import Benchmarks.UniswapV4PoolManager.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def settleInputFrame (f : Frame) (evm : EVM.State) : Frame :=
  {f with locals := (((f.locals.insert "paid" (.int 0)).insert "currency" (.address (syncedCurrency evm))).insert
    "__c1" (.bool (decide (syncedCurrency evm = AccountAddress.ofNat 0))))}

theorem settlePrefix {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    ExecBlock config f evm (settleFunction.body.take 3) (.ok (settleInputFrame f evm) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (syncedCurrencyCall (f := {f with locals := f.locals.insert "paid" (.int 0)}) hf "currency") ?_
  exact ExecBlock.consNormal (currencyZeroCall (f := {f with locals := ((f.locals.insert "paid" (.int 0)).insert
    "currency" (.address (syncedCurrency evm)))}) hf (evalLocalValue (store_get_self _ _ _)) "__c1") ExecBlock.nil

theorem settleInput_recipient {f : Frame} {evm : EVM.State} {recipient : AccountAddress}
    (hr : f.locals.get? "recipient" = some (.address recipient)) :
    (settleInputFrame f evm).locals.get? "recipient" = some (.address recipient) :=
  (store_get_ne _ _ (by decide : ("__c1" == "recipient") = false)).trans
    ((store_get_ne _ _ (by decide : ("currency" == "recipient") = false)).trans
      ((store_get_ne _ _ (by decide : ("paid" == "recipient") = false)).trans hr))

theorem settleInput_currency (f : Frame) (evm : EVM.State) :
    (settleInputFrame f evm).locals.get? "currency" = some (.address (syncedCurrency evm)) :=
  (store_get_ne _ _ (by decide : ("__c1" == "currency") = false)).trans (store_get_self _ _ _)

theorem settleInput_paid (f : Frame) (evm : EVM.State) :
    (settleInputFrame f evm).locals.get? "paid" = some (.int 0) :=
  (store_get_ne _ _ (by decide : ("__c1" == "paid") = false)).trans
    ((store_get_ne _ _ (by decide : ("currency" == "paid") = false)).trans (store_get_self _ _ _))

def settleNativeFrame (f : Frame) (evm : EVM.State) : Frame :=
  {settleInputFrame f evm with locals := ((settleInputFrame f evm).locals.insert "paid"
    (.int (Int.ofNat evm.executionEnv.weiValue.toNat)))}

theorem settleNativeBody {f : Frame} {evm : EVM.State} {recipient : AccountAddress}
    (hf : f.contract = contract) (hr : f.locals.get? "recipient" = some (.address recipient))
    (hz : syncedCurrency evm = AccountAddress.ofNat 0) :
    ExecFuncBody config f evm settleFunction.body
      (settlePaidResult (settleNativeFrame f evm) evm recipient (syncedCurrency evm) evm.executionEnv.weiValue) := by
  have hg : evalExpr? config (settleInputFrame f evm) evm (.var "__c1") = .ok (.bool true) := by
    simpa only [decide_eq_true hz] using evalLocalValue (cfg := config) (evm := evm)
      (show (settleInputFrame f evm).locals.get? "__c1" = some (.bool (decide (syncedCurrency evm = AccountAddress.ofNat 0))) from store_get_self _ _ _)
  have hb := settlePaidBody (f := settleNativeFrame f evm) (evm := evm) hf
    ((store_get_ne _ _ (by decide : ("paid" == "recipient") = false)).trans (settleInput_recipient hr))
    ((store_get_ne _ _ (by decide : ("paid" == "currency") = false)).trans (settleInput_currency f evm))
    (store_get_self _ _ _)
  apply execFuncBody_prepend (settlePrefix hf)
  apply execFuncBody_prepend (pre := [settleFunction.body[3]!]) ?_ hb
  exact execBlock_singleton (ExecStmt.iteTrue hg (ExecBlock.consNormal (ExecStmt.assign
    (by simp only [evalExpr?, envValue, pure]; rfl) (assignLocalValue (settleInput_paid f evm))) ExecBlock.nil))

theorem evalCallvaluePositive {f : Frame} {evm : EVM.State} :
    evalExpr? config f evm (.binary .gt (.env .callvalue) (.intLit 0)) =
      .ok (.bool (decide (evm.executionEnv.weiValue ≠ ⟨0⟩))) := by
  simp only [evalExpr?, envValue, bind, EvalResult.bind, pure, evalBinaryOp?]
  congr 2
  by_cases hz : evm.executionEnv.weiValue = ⟨0⟩
  · rw [hz]; decide
  · have hn : evm.executionEnv.weiValue.toNat ≠ 0 := fun he => hz (uint256_toNat_eq_zero he)
    have hp : Int.ofNat evm.executionEnv.weiValue.toNat > 0 := by simp only [Int.ofNat_eq_natCast]; omega
    change decide (Int.ofNat evm.executionEnv.weiValue.toNat > 0) = _
    rw [decide_eq_true hp, decide_eq_true hz]

theorem settleValueReverts {f : Frame} {evm : EVM.State}
    (hf : f.contract = contract) (hn : syncedCurrency evm ≠ AccountAddress.ofNat 0)
    (hv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecFuncBody config f evm settleFunction.body .reverted := by
  apply execFuncBody_prepend (settlePrefix hf)
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert (ExecStmt.iteFalse
    ((evalLocalValue (store_get_self _ _ _)).trans (by rw [decide_eq_false hn]))
    (ExecBlock.consRevert (ExecStmt.iteTrue (evalCallvaluePositive.trans (by rw [decide_eq_true hv]))
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))))

def settleTokenFrame (f : Frame) (evm : EVM.State) (out : ByteArray) : Frame :=
  {f with locals := (
    let locals := (settleInputFrame f evm).locals.insert "reservesBefore" (.int (Int.ofNat (transientWord evm reservesSlot).toNat))
    let locals := locals.insert "reservesNow" (.int (Int.ofNat (returnedBalanceWord out).toNat))
    let locals := locals.insert "paid" (.int (Int.ofNat (UInt256.sub (returnedBalanceWord out) (transientWord evm reservesSlot)).toNat))
    locals.insert "__c4" .unit)}

theorem settleTokenFrame_contract (f : Frame) (evm : EVM.State) (out : ByteArray) :
    (settleTokenFrame f evm out).contract = f.contract := by simp only [settleTokenFrame]

def settleTokenResult (f : Frame) (evm evm' : EVM.State) (recipient : AccountAddress) (z : Bool) (out : ByteArray) : ExecResult :=
  if z = true ∧ 32 ≤ out.size then
    if (transientWord evm reservesSlot).toNat ≤ (returnedBalanceWord out).toNat then
      if evm'.executionEnv.perm = false then .staticViolation else
      settlePaidResult (settleTokenFrame f evm out) (resetCurrencyPost evm') recipient (syncedCurrency evm)
        (UInt256.sub (returnedBalanceWord out) (transientWord evm reservesSlot))
    else .reverted
  else .reverted

theorem settleTokenBody {f : Frame} {evm evm' : EVM.State} {recipient : AccountAddress} {z : Bool} {out : ByteArray}
    (hf : f.contract = contract) (hr : f.locals.get? "recipient" = some (.address recipient))
    (hn : syncedCurrency evm ≠ AccountAddress.ofNat 0) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : out.size < 2^255)
    (hcall : typedCallViaEVM config evm (syncedCurrency evm) "balanceOf" 0 [.address evm.executionEnv.codeOwner] (z, evm', out) false) :
    ExecFuncBody config f evm settleFunction.body (settleTokenResult f evm evm' recipient z out) := by
  let f1 := settleInputFrame f evm
  let f2 : Frame := {f1 with locals := f1.locals.insert "reservesBefore" (.int (Int.ofNat (transientWord evm reservesSlot).toNat))}
  let f3 : Frame := {f2 with locals := f2.locals.insert "reservesNow" (.int (Int.ofNat (returnedBalanceWord out).toNat))}
  let paid := UInt256.sub (returnedBalanceWord out) (transientWord evm reservesSlot)
  let f4 : Frame := {f3 with locals := f3.locals.insert "paid" (.int (Int.ofNat paid.toNat))}
  have hguard : evalExpr? config f1 evm (.var "__c1") = .ok (.bool false) :=
    (evalLocalValue (store_get_self _ _ _)).trans (by rw [decide_eq_false hn])
  have hvalue : ExecStmt config f1 evm
      (.ite (.binary .gt (.env .callvalue) (.intLit 0)) [.require (.boolLit false)] []) (.ok f1 evm) :=
    ExecStmt.iteFalse (evalCallvaluePositive.trans (by rw [decide_eq_false (not_not.mpr hv)])) ExecBlock.nil
  have hbefore := syncedReservesCall (f := f1) (evm := evm) hf "reservesBefore"
  have hbalance := currencyBalanceCall (f := f2) (evm := evm) hf
    (evalLocalValue ((store_get_ne _ _ (by decide : ("reservesBefore" == "currency") = false)).trans
      (settleInput_currency f evm))) hn ho hcall "reservesNow"
  rw [settleTokenResult]
  apply execFuncBody_prepend (settlePrefix hf)
  by_cases hg : z = true ∧ 32 ≤ out.size
  · rw [if_pos hg] at hbalance ⊢
    have hp3 : f3.locals.get? "paid" = some (.int 0) :=
      (store_get_ne _ _ (by decide : ("reservesNow" == "paid") = false)).trans
        ((store_get_ne _ _ (by decide : ("reservesBefore" == "paid") = false)).trans (settleInput_paid f evm))
    have hnow : evalExpr? config f3 evm' (.var "reservesNow") = .ok (.int (Int.ofNat (returnedBalanceWord out).toNat)) :=
      evalLocalValue (store_get_self _ _ _)
    have hprev : evalExpr? config f3 evm' (.var "reservesBefore") = .ok (.int (Int.ofNat (transientWord evm reservesSlot).toNat)) :=
      evalLocalValue ((store_get_ne _ _ (by decide : ("reservesNow" == "reservesBefore") = false)).trans (store_get_self _ _ _))
    by_cases hsub : (transientWord evm reservesSlot).toNat ≤ (returnedBalanceWord out).toNat
    · rw [if_pos hsub]
      have hpaid := ExecStmt.assign (evalExpr_uint256_sub hnow hprev hsub) (assignLocalValue hp3)
      have hreset := resetCurrencyCall (f := f4) (evm := evm') hf "__c4"
      by_cases hp : evm'.executionEnv.perm = false
      · rw [if_pos hp] at hreset ⊢
        exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.iteFalse hguard (ExecBlock.consNormal hvalue
          (ExecBlock.consNormal hbefore (ExecBlock.consNormal hbalance (ExecBlock.consNormal hpaid (ExecBlock.consStatic hreset)))))))
      · rw [if_neg hp] at hreset ⊢
        have hprefix : ExecBlock config f1 evm [settleFunction.body[3]!] (.ok (settleTokenFrame f evm out) (resetCurrencyPost evm')) :=
          execBlock_singleton (ExecStmt.iteFalse hguard (ExecBlock.consNormal hvalue
            (ExecBlock.consNormal hbefore (ExecBlock.consNormal hbalance (ExecBlock.consNormal hpaid
              (ExecBlock.consNormal hreset ExecBlock.nil))))))
        have hrecipient : (settleTokenFrame f evm out).locals.get? "recipient" = some (.address recipient) := by
          exact (store_get_ne _ _ (by decide : ("__c4" == "recipient") = false)).trans
            ((store_get_ne _ _ (by decide : ("paid" == "recipient") = false)).trans
              ((store_get_ne _ _ (by decide : ("reservesNow" == "recipient") = false)).trans
                ((store_get_ne _ _ (by decide : ("reservesBefore" == "recipient") = false)).trans (settleInput_recipient hr))))
        have hcurrency : (settleTokenFrame f evm out).locals.get? "currency" = some (.address (syncedCurrency evm)) := by
          exact (store_get_ne _ _ (by decide : ("__c4" == "currency") = false)).trans
            ((store_get_ne _ _ (by decide : ("paid" == "currency") = false)).trans
              ((store_get_ne _ _ (by decide : ("reservesNow" == "currency") = false)).trans
                ((store_get_ne _ _ (by decide : ("reservesBefore" == "currency") = false)).trans (settleInput_currency f evm))))
        have hpaidFinal : (settleTokenFrame f evm out).locals.get? "paid" = some (.int (Int.ofNat paid.toNat)) :=
          (store_get_ne _ _ (by decide : ("__c4" == "paid") = false)).trans (store_get_self _ _ _)
        have hcontract : (settleTokenFrame f evm out).contract = contract :=
          (settleTokenFrame_contract f evm out).trans hf
        generalize hframe : settleTokenFrame f evm out = finalFrame at hprefix hrecipient hcurrency hpaidFinal hcontract ⊢
        generalize hpost : resetCurrencyPost evm' = post at hprefix ⊢
        have htail := settlePaidBody (f := finalFrame) (evm := post)
          hcontract hrecipient hcurrency hpaidFinal
        exact execFuncBody_prepend hprefix htail
    · rw [if_neg hsub]
      exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteFalse hguard (ExecBlock.consNormal hvalue
        (ExecBlock.consNormal hbefore (ExecBlock.consNormal hbalance (ExecBlock.consRevert (ExecStmt.assignExprRevert
          (checkedSubSourceUnderflow hnow hprev (Nat.lt_of_not_ge hsub)))))))))
  · rw [if_neg hg] at hbalance ⊢
    exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteFalse hguard (ExecBlock.consNormal hvalue
      (ExecBlock.consNormal hbefore (ExecBlock.consRevert hbalance)))))

end Benchmarks.UniswapV4PoolManager
