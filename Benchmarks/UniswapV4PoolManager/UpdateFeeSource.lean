import Benchmarks.UniswapV4PoolManager.PoolLPFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def dynamicFeeAuthorized (I : ExecutionEnv) (key : PoolKeyWords) : Prop :=
  key.fee.toNat = 8388608 ∧ I.source = AccountAddress.ofNat key.hooks.toNat
instance (I : ExecutionEnv) (key : PoolKeyWords) : Decidable (dynamicFeeAuthorized I key) :=
  inferInstanceAs (Decidable (_ ∧ _))

def updateFeeAlias : Ident := "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.26"
def updateFeeFinalFrame (f : Frame) (key : PoolKeyWords) : Frame :=
  let locals := f.locals.insert "key" (poolKeyValue key)
  let locals := locals.insert "__c0" (.bool (decide (key.fee.toNat = 8388608)))
  let locals := locals.insert "__c1" .unit
  let locals := locals.insert "id" (wordBytes32Value (poolKeyId key))
  let locals := locals.insert updateFeeAlias (poolRefValue (poolKeyId key))
  {f with locals := locals.insert "__c3" .unit}

def updateFeeResult (f : Frame) (evm : EVM.State) (key : PoolKeyWords) (fee : UInt256) : ExecResult :=
  if dynamicFeeAuthorized evm.executionEnv key then
    if fee.toNat ≤ 1000000 then poolSetFeeResult (updateFeeFinalFrame f key) evm (poolKeyId key) fee else .reverted
  else .reverted

theorem updateFeeGuard {f : Frame} {evm : EVM.State} {key : PoolKeyWords}
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hd : f.locals.get? "__c0" = some (.bool (decide (key.fee.toNat = 8388608)))) :
    evalExpr? config f evm (.binary .or (.unary .not (.var "__c0"))
      (.binary .ne (.env .caller) (.field (.var "key") "hooks"))) =
      .ok (.bool (decide (¬dynamicFeeAuthorized evm.executionEnv key))) := by
  have he := evalOrBool (evalNotBool (evalLocalValue (cfg := config) (evm := evm) hd))
    (evalNeAddress (by simp only [evalExpr?, envValue, pure] :
      evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source))
      (evalStructField (evalLocalValue hk) (field := "hooks") rfl))
  simpa only [dynamicFeeAuthorized, not_and_or, Bool.decide_or, decide_not] using he

theorem updateFeeBody {evm : EVM.State} {locals imms : Store} {key : PoolKeyWords} {fee : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : PoolKeyCanonical key) (hfee : fee.toNat < 2^24)
    (hk : locals.get? "key" = some (.tuple (poolKeyValues key)))
    (he : locals.get? "newDynamicLPFee" = some (.int (Int.ofNat fee.toNat)))
    (hpools : locals.get? "_pools" = none) :
    ExecTransitionBody config contract evm locals updateDynamicLPFeeTransition.body
      (updateFeeResult (calldataFrame contract locals imms evm) evm key fee) imms := by
  let f := calldataFrame contract locals imms evm
  let f1 : Frame := {f with locals := f.locals.insert "key" (poolKeyValue key)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c0" (.bool (decide (key.fee.toNat = 8388608)))}
  let f3 : Frame := {f2 with locals := f2.locals.insert "__c1" .unit}
  let f4 : Frame := {f3 with locals := f3.locals.insert "id" (wordBytes32Value (poolKeyId key))}
  let f5 : Frame := {f4 with locals := f4.locals.insert updateFeeAlias (poolRefValue (poolKeyId key))}
  have hlet : ExecStmt config f evm updateDynamicLPFeeTransition.body[3]! (.ok f1 evm) :=
    ExecStmt.letDecl (poolKeyFromTuple_eval (evalLocalValue
      ((store_get_ne _ _ (by decide : ("__calldata" == "key") = false)).trans hk)))
  have hdyn := lpFeeDynamicCall (f := f1) (evm := evm) rfl
    (evalStructField (evalLocalValue (store_get_self _ _ _)) (field := "fee") rfl) "__c0"
  have hk2 : f2.locals.get? "key" = some (poolKeyValue key) :=
    (store_get_ne _ _ (by decide : ("__c0" == "key") = false)).trans (store_get_self _ _ _)
  have hguard := updateFeeGuard (f := f2) (evm := evm) hk2 (store_get_self _ _ _)
  rw [updateFeeResult]
  by_cases hauth : dynamicFeeAuthorized evm.executionEnv key
  · rw [if_pos hauth]
    rw [decide_eq_false (not_not.mpr hauth)] at hguard
    have hite : ExecStmt config f2 evm updateDynamicLPFeeTransition.body[5]! (.ok f2 evm) :=
      ExecStmt.iteFalse hguard ExecBlock.nil
    have he2 : f2.locals.get? "newDynamicLPFee" = some (.int (Int.ofNat fee.toNat)) :=
      (store_get_ne3 _ _ _ _ (by decide : ("__calldata" == "newDynamicLPFee") = false)
        (by decide : ("key" == "newDynamicLPFee") = false) (by decide : ("__c0" == "newDynamicLPFee") = false)).trans he
    have hvalidate := lpFeeValidateCall (f := f2) (evm := evm) rfl (evalLocalValue he2) "__c1"
    by_cases hv : fee.toNat ≤ 1000000
    · rw [if_pos hv] at hvalidate ⊢
      have hid := poolIdCall (f := f3) (evm := evm) rfl hc (evalLocalValue
        ((store_get_ne _ _ (by decide : ("__c1" == "key") = false)).trans hk2)) "id"
      have hbase : f4.locals.get? "_pools" = none :=
        (store_get_ne5 _ _ _ _ _ _ (by decide : ("__calldata" == "_pools") = false)
          (by decide : ("key" == "_pools") = false) (by decide : ("__c0" == "_pools") = false)
          (by decide : ("__c1" == "_pools") = false) (by decide : ("id" == "_pools") = false)).trans hpools
      have href : ExecStmt config f4 evm updateDynamicLPFeeTransition.body[8]! (.ok f5 evm) :=
        ExecStmt.letStorage (poolMappingResolve rfl hbase (evalLocalValue (store_get_self _ _ _)))
      have he5 : f5.locals.get? "newDynamicLPFee" = some (.int (Int.ofNat fee.toNat)) :=
        (store_get_ne3 _ _ _ _ (by decide : ("__c1" == "newDynamicLPFee") = false)
          (by decide : ("id" == "newDynamicLPFee") = false)
          (by decide : (updateFeeAlias == "newDynamicLPFee") = false)).trans he2
      have hset := poolSetFeeCall (f := f5) (evm := evm) rfl hfee
        (evalLocalValue (store_get_self _ _ _)) (evalLocalValue he5) "__c3"
      have htail := execFuncBody_singleton hset
      simp only [poolSetFeeCallResult, poolSetFeeResult, resumeCallResult_ite, resumeCallResult_reverted,
        resumeCallResult_static, resumeCallResult_returned, finishBlockResult_ite, finishBlockResult_reverted,
        finishBlockResult_static, finishBlockResult_ok] at htail
      apply nonpayableCalldataBody hwv hhi
      exact execFuncBody_prepend
        (ExecBlock.consNormal hlet (ExecBlock.consNormal hdyn (ExecBlock.consNormal hite
          (ExecBlock.consNormal hvalidate (ExecBlock.consNormal hid (ExecBlock.consNormal href ExecBlock.nil)))))) htail
    · rw [if_neg hv] at hvalidate ⊢
      apply ExecFuncBody.execBlockRevert
      apply nonpayableCalldataBlock hwv hhi
      exact ExecBlock.consNormal hlet (ExecBlock.consNormal hdyn (ExecBlock.consNormal hite (ExecBlock.consRevert hvalidate)))
  · rw [if_neg hauth]
    rw [decide_eq_true hauth] at hguard
    apply ExecFuncBody.execBlockRevert
    apply nonpayableCalldataBlock hwv hhi
    exact ExecBlock.consNormal hlet (ExecBlock.consNormal hdyn (ExecBlock.consRevert
      (ExecStmt.iteTrue hguard (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))))

end Benchmarks.UniswapV4PoolManager
